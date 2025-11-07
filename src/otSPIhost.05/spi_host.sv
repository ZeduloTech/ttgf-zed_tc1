//	USE SPI_HOST UNLESS YOU WANT TO HANDLE ALL SETUP AND HANDSHAKING CONTROL
//	NOTE THAT:
//		- SPI Mode 3 config in use
//		- ONLY NumCS SLAVE DEVICES CAN CONNECT DIRECTLY TO HOST VIA csb_o
//		- ALL BYTES ARE TRANSMITTED FROM MSB TO LSB

module spi_host (
	input			clk_i,		// System clock
	input			rst_ni,		// System reset (Active LOW)

	input	[7:0]		tx_byte_i,	// this byte will be sent to SLAVE via mosi
	input			write_i,	// tells HOST to WRITE tx_byte_i to SLAVE
	input			read_i,		// tells HOST to READ whatever SLAVE sends next into rx_byte_o
	input			miso_i,		// Master In Slave Out

	output	[7:0]		rx_byte_o,	// the most recent byte READ from SLAVE
	output			awake_o,	// indicates that HOST was properly reset at least once
	output			idle_o,		// indicates that HOST is ready to WRITE / READ
	output			mosi_o,		// Master Out Slave In

	output			sck_o,		// clock signal for SLAVE's use
	output	[NumCS-1:0]	csb_o		// Chip/Slave Select BUS
);
//	Parameters for scaling the Chip Select bus size
	parameter NumCS = 1;
	localparam CSW = prim_util_pkg::vbits(NumCS);

//	command config registers
	spi_host_cmd_pkg::command_t command_i;

//	Overall internal state info
	reg sw_rst_i = 0;
	reg awake = 0;
	reg transacting = 0;
	reg cmd_triggered = 0;
	reg read_done = 0;

//	Sampled inputs used for debouncing
	reg write_i_prev = 0;
	reg read_i_prev = 0;

//	Debounced inputs
	wire write_i_stable;
	wire read_i_stable;

//	Unprocessed input alert flags
	reg write_flag = 0;
	reg read_flag = 0;

//	Processed inputs for controlling the Cooore :)
	reg write_req = 0;
	reg read_req = 0;

//	Output buffers
	reg [7:0] rx_byte = 0;

//	Command Configuration for host_core
	reg [CSW-1:0] command_csid_i = 0; //Which CS line index of the CS bus is HOST to assert next

//	Remaining I/0 for Host Core
	reg  command_valid_i = 0;
	wire tx_ready_o;
	wire tx_byte_select_full_o;
	wire [3:0] sd_en_o;
	wire rx_stall_o;
	wire tx_stall_o;
	wire [31:0] rx_data_o;
	wire rx_valid_o;
	wire [3:0] sd_o;
	wire [3:0] sd_i;
	wire command_ready_o;
	wire active_o;

//	Serial I/O assignments
	assign sd_i   = {1'b0, 1'b0, miso_i, 1'b0};
	assign mosi_o = sd_o[0];

//	Other I/O assignments
	assign rx_byte_o = rx_byte;

//	State assignments
	assign awake_o = awake;
	assign idle_o  = (awake && !transacting);

//	Debounced inputs
	assign write_i_stable = write_i && write_i_prev;
	assign read_i_stable  = read_i && read_i_prev;

	wire _unused_pins =  &{tx_ready_o, tx_byte_select_full_o, rx_data_o[31:8],
				sd_en_o, sd_o[3:1], rx_stall_o, tx_stall_o};

	spi_host_core #(
		.NumCS			(NumCS)
	) master_core (
		.clk_i			(clk_i),
		.rst_ni			(rst_ni),

		.command_i		(command_i),
		.command_csid_i		(command_csid_i),
		.command_valid_i	(command_valid_i),
		.command_ready_o	(command_ready_o),
		.en_i			(1'b1),

		.tx_data_i		({24'b0, tx_byte_i}),
		.tx_be_i		(4'b1),
		.tx_valid_i		(write_req),
		.tx_ready_o		(tx_ready_o),
		.tx_byte_select_full_o	(tx_byte_select_full_o),

		.rx_data_o		(rx_data_o),
		.rx_valid_o		(rx_valid_o),
		.rx_ready_i		(read_req),

		.sw_rst_i		(sw_rst_i),

//		SPI Interface
		.sck_o			(sck_o),
		.csb_o			(csb_o),
		.sd_o			(sd_o),
		.sd_en_o		(sd_en_o),
		.sd_i			(sd_i),

//		Status bits
		.rx_stall_o		(rx_stall_o),
		.tx_stall_o		(tx_stall_o),
		.active_o		(active_o)
	);

	always @(posedge clk_i or negedge rst_ni) begin
		if (!rst_ni) begin
			sw_rst_i	<= 1;
			awake		<= 0;
			transacting	<= 0;
			rx_byte		<= 0;
//			(RE)SET COMMAND CONFIGOPTS
			command_i.configopts.clkdiv	<= 95;
			command_i.configopts.csnidle	<= 0;
			command_i.configopts.csnlead	<= 0; // can destabilize READs if not 0
			command_i.configopts.csntrail	<= 0;
			command_i.configopts.full_cyc	<= 1; // for stable READS use 1
			command_i.configopts.cpol	<= 1; // SPI Mode 3
			command_i.configopts.cpha	<= 1;

			command_i.segment.speed		<= spi_host_cmd_pkg::Standard;
			// segment.cmd_(wr_en/rd_en) set later (WRITE/READ input)
			command_i.segment.cmd_wr_en	<= 0;
			command_i.segment.cmd_rd_en	<= 0;
			command_i.segment.len		<= 0; // can destabilize WRITEs if not 0
			command_i.segment.csaat		<= 1; // necessary if u wish to use clkdiv > 0
		end else begin
			if (sw_rst_i) begin
				sw_rst_i	<= 0;
				awake		<= 1;
				read_done	<= 0;
				cmd_triggered	<= 0;
				transacting	<= 0;
				command_i.segment.cmd_wr_en <= 0;
				command_i.segment.cmd_rd_en <= 0;
			end else begin
				if (awake) begin
					if (!transacting) begin
						write_i_prev	<= write_i;
						read_i_prev	<= read_i;

						if (command_ready_o) begin
							if (!active_o) begin
								if (write_flag || read_flag) begin
									if (!cmd_triggered) begin
										command_valid_i <= 1;
										cmd_triggered   <= 1;
									end
								end else begin
									if (write_i_stable) begin
										write_flag <= 1;
										command_i.segment.cmd_wr_en	<= 1;
									end

									if (read_i_stable) begin
										read_flag <= 1;
										command_i.segment.cmd_rd_en	<= 1;
									end
								end
							end
						end else begin // if !command ready_o
							if (command_valid_i)
								command_valid_i	<= 0;

							if (active_o) begin
								if (write_flag && !write_req) begin
									write_flag <= 0;
									write_req  <= 1;
								end

								if (read_flag && !read_req) begin
									read_flag <= 0;
									read_req  <= 1;
								end
								transacting <= 1;
							end
						end
					end else begin //if (transacting)
						if (command_ready_o) begin
							if (write_req)
								write_req <= 0;

							if (rx_valid_o && !read_done) begin
								rx_byte <= rx_data_o[7:0];
								read_done <= 1;

								if (read_req)
									read_req <= 0;
							end

							if (!active_o) begin
//								Start ignoring stale (W/R)s
//										&
//								Wait till W&R reqs are cleared
//								then, Send core to its "reset" state before the next tx_byte update
								if (!write_i && !read_i)
									if (!write_req && !read_req)
										if (!sw_rst_i)
											sw_rst_i <= 1;
							end
						end
					end
				end
			end
		end
	end
endmodule
