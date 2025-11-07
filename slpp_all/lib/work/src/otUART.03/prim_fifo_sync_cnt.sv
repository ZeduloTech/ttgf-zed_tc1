// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Read and write pointer logic for synchronous FIFOs

// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0




///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.



// Converts an arbitrary block of code into a Verilog string


// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.









// This macro is suitable for conditionally triggering lint errors, e.g., if a Sec parameter takes
// on a non-default value. This may be required for pre-silicon/FPGA evaluation but we don't want
// to allow this for tapeout.







// Static assertions for checks inside SV packages. If the conditions is not true, this will
// trigger an error during elaboration.







// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_INIT_NET: Assertion in initial block. Can be used for initial value of a net.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT_AT_RESET: Assertion just before reset. Can be used to check sum-like properties that get
//                   cleared at reset.
//                   Note that unless your simulation ends with a reset, the property does not get
//                   checked at end of simulation; use ASSERT_AT_RESET_AND_FINAL if the property
//                   should also get checked at end of simulation.
//
//  ASSERT_AT_RESET_AND_FINAL: Assertion just before reset and in final block. Can be used to check
//                             sum-like properties before every reset and at the end of simulation.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property




 // Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macro bodies included by prim_assert.sv for tools that don't support assertions. See
// prim_assert.sv for documentation for each of the macros.






















//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// NOTE: Removed default arguments for Quartus compatibility.
// Assert that signal is an active-high pulse with pulse length of 1 clock cycle



// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.



// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.






//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.





// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.





// COVER_FPV
// Cover a concurrent property during formal verification





// FPV assertion that proves that the FSM control flow is linear (no loops)
// The sequence triggers whenever the state changes and stores the current state as "initial_state".
// Then thereafter we must never see that state again until reset.
// It is possible for the reset to release ahead of the clock.
// Create a small "gray" window beyond the usual rst time to avoid
// checking.


















// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for security countermeasures.






// When a named error signal rises, expect to see an associated error in at most MAX_CYCLES_ cycles.








// Error signal     alert in at most MAX_CYCLES_






// Error signal     ALERT_IN_




////////////////////////////////////////////////////////////////////////////////
// Assertions for CMs that trigger alerts
////////////////////////////////////////////////////////////////////////////////

// NOTE: Quartus does not support default macro params, so caller must pass all arguments!




















////////////////////////////////////////////////////////////////////////////////
// Assertions for CMs that trigger alerts (input flavour)
////////////////////////////////////////////////////////////////////////////////




















////////////////////////////////////////////////////////////////////////////////
// Assertions for CMs that trigger errors
////////////////////////////////////////////////////////////////////////////////



















// Register with asynchronous reset.









///////////////////////////
// Macro for Sparse FSMs //
///////////////////////////



































module prim_fifo_sync_cnt #(
  // Depth of the FIFO, i.e., maximum number of entries the FIFO can contain
  parameter int unsigned Depth = 4,
  // Whether to instantiate hardened counters
  parameter bit Secure = 1'b0,
  // If this is set, the clr_i port will always be false
  parameter bit NeverClears = 1'b0
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic clr_i,
  input  logic incr_wptr_i,
  input  logic incr_rptr_i,
  // Write and read pointers.  Value range: [0, Depth-1]
  output logic [prim_util_pkg_u::vbits(Depth)-1:0] wptr_o,
  output logic [prim_util_pkg_u::vbits(Depth)-1:0] rptr_o,
  output logic full_o,
  output logic empty_o,
  // Current depth of the FIFO, i.e., number of entries the FIFO currently contains.
  // Value range: [0, Depth]
  output logic [prim_util_pkg_u::vbits(Depth+1)-1:0] depth_o,
  output logic err_o
);

  // Derived widths (move localparam inside module body to satisfy Quartus)
  localparam int unsigned PtrW  = prim_util_pkg_u::vbits(Depth);
  localparam int unsigned DepthW = prim_util_pkg_u::vbits(Depth+1);

  // Internal 'wrap' pointers that have an extra leading bit to account for wraparounds.
  localparam int unsigned WrapPtrW = PtrW + 1;
  logic [WrapPtrW-1:0] wptr_wrap_cnt_q, wptr_wrap_set_cnt,
                       rptr_wrap_cnt_q, rptr_wrap_set_cnt;

  // Derive real read and write pointers by truncating the internal 'wrap' pointers.
  assign wptr_o = wptr_wrap_cnt_q[PtrW-1:0];
  assign rptr_o = rptr_wrap_cnt_q[PtrW-1:0];

  // Extract the MSB of the 'wrap' pointers.
  logic wptr_wrap_msb, rptr_wrap_msb;
  assign wptr_wrap_msb = wptr_wrap_cnt_q[WrapPtrW-1];
  assign rptr_wrap_msb = rptr_wrap_cnt_q[WrapPtrW-1];

  // Wrap pointers when they have reached the maximum value and are about to get incremented.
  logic wptr_wrap_set, rptr_wrap_set;
  assign wptr_wrap_set = incr_wptr_i & (wptr_o == PtrW'(Depth-1));
  assign rptr_wrap_set = incr_rptr_i & (rptr_o == PtrW'(Depth-1));

  // When wrapping, invert the MSB and reset all lower bits to zero.
  assign wptr_wrap_set_cnt = {~wptr_wrap_msb, {(WrapPtrW-1){1'b0}}};
  assign rptr_wrap_set_cnt = {~rptr_wrap_msb, {(WrapPtrW-1){1'b0}}};

  // Full when both 'wrap' counters have a different MSB but all lower bits are equal.
  assign full_o  = wptr_wrap_cnt_q == (rptr_wrap_cnt_q ^ {1'b1, {(WrapPtrW-1){1'b0}}});
  // Empty when both 'wrap' counters are equal in all bits including the MSB.
  assign empty_o = wptr_wrap_cnt_q == rptr_wrap_cnt_q;

  // The current depth expression uses DepthW inside the module.
  assign depth_o = full_o                         ? DepthW'(Depth) :
                   wptr_wrap_msb == rptr_wrap_msb ? DepthW'(wptr_o) - DepthW'(rptr_o) :
                   DepthW'(Depth) - DepthW'(rptr_o) + DepthW'(wptr_o);
generate
  if (Secure) begin : gen_secure_ptrs
    logic wptr_err;
    prim_count #(
      .Width(WrapPtrW),
      .PossibleActions((NeverClears ? 0 : prim_count_pkg::Clr) |
                       prim_count_pkg::Set | prim_count_pkg::Incr)
    ) u_wptr (
      .clk_i       (clk_i),
      .rst_ni      (rst_ni),
      .clr_i       (clr_i),
      .set_i       (wptr_wrap_set),
      .set_cnt_i   (wptr_wrap_set_cnt),
      .incr_en_i   (incr_wptr_i),
      .decr_en_i   (1'b0),
      .step_i      (WrapPtrW'(1'b1)),
      .commit_i    (1'b1),
      .cnt_o       (wptr_wrap_cnt_q),
      .cnt_after_commit_o(),
      .err_o       (wptr_err)
    );

    logic rptr_err;
    prim_count #(
      .Width(WrapPtrW),
      .PossibleActions((NeverClears ? 0 : prim_count_pkg::Clr) |
                       prim_count_pkg::Set | prim_count_pkg::Incr)
    ) u_rptr (
      .clk_i       (clk_i),
      .rst_ni      (rst_ni),
      .clr_i       (clr_i),
      .set_i       (rptr_wrap_set),
      .set_cnt_i   (rptr_wrap_set_cnt),
      .incr_en_i   (incr_rptr_i),
      .decr_en_i   (1'b0),
      .step_i      (WrapPtrW'(1'b1)),
      .commit_i    (1'b1),
      .cnt_o       (rptr_wrap_cnt_q),
      .cnt_after_commit_o(),
      .err_o       (rptr_err)
    );

    assign err_o = wptr_err | rptr_err;

  end else begin : gen_normal_ptrs
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        wptr_wrap_cnt_q <= {WrapPtrW{1'b0}};
      end else if (clr_i) begin
        wptr_wrap_cnt_q <= {WrapPtrW{1'b0}};
      end else if (wptr_wrap_set) begin
        wptr_wrap_cnt_q <= wptr_wrap_set_cnt;
      end else if (incr_wptr_i) begin
        wptr_wrap_cnt_q <= wptr_wrap_cnt_q + {{(WrapPtrW-1){1'b0}}, 1'b1};
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rptr_wrap_cnt_q <= {WrapPtrW{1'b0}};
      end else if (clr_i) begin
        rptr_wrap_cnt_q <= {WrapPtrW{1'b0}};
      end else if (rptr_wrap_set) begin
        rptr_wrap_cnt_q <= rptr_wrap_set_cnt;
      end else if (incr_rptr_i) begin
        rptr_wrap_cnt_q <= rptr_wrap_cnt_q + {{(WrapPtrW-1){1'b0}}, 1'b1};
      end
    end

    assign err_o = '0;
  end
  endgenerate

  generate
  if (NeverClears) begin : gen_never_clears
 
    
	
  end
endgenerate

endmodule // prim_fifo_sync_cnt
