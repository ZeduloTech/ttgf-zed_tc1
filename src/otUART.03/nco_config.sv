// Computes NCO value at elaboration time (64-bit safe).

module nco_config #(
	parameter int BAUD_RATE,
	parameter int CLK_FREQ_HZ,
	parameter int NCO_WIDTH = 16
) ( 
	output logic [15:0] nco
);	

	// Using 64-bit to avoid overflow
	localparam logic [63:0] POW2      = 64'd1 << NCO_WIDTH;	// 2^NCO_WIDTH

	// wide numerator
	localparam logic [63:0] NUMERATOR = BAUD_RATE * 16 * POW2;
	// rounded division
	localparam int NCO_VALUE = (NUMERATOR + (CLK_FREQ_HZ/2)) / CLK_FREQ_HZ;

	assign nco = NCO_VALUE[NCO_WIDTH-1:0];
endmodule
