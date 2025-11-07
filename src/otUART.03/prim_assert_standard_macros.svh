// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macro bodies included by prim_assert.sv for tools that support full SystemVerilog and SVA syntax.
// See prim_assert.sv for documentation for each of the macros.

`define ASSERT_I(__name, __prop) \
  __name: assert (__prop)        \
    else begin                   \
      `ASSERT_ERROR(__name)      \
    end

`define ASSERT_INIT(__name, __prop)                                                  \
`ifdef FPV_ON                                                                        \
  if (!(__prop)) $fatal(2, "Fatal static assertion [%s]: (%s) is not true.",         \
                        (__name), (__prop));                                         \
`else                                                                                \
  initial begin                                                                      \
    __name: assert (__prop)                                                          \
      else begin                                                                     \
        `ASSERT_ERROR(__name)                                                        \
      end                                                                            \
  end                                                                                \
`endif

`define ASSERT_INIT_NET(__name, __prop)                                              \
  initial begin                                                                      \
    #1ps;                                                                            \
    __name: assert (__prop)                                                          \
      else begin                                                                     \
        `ASSERT_ERROR(__name)                                                        \
      end                                                                            \
  end                                                                                \

`define ASSERT_FINAL(__name, __prop)                                         \
`ifndef FPV_ON                                                               \
  final begin                                                                \
    __name: assert (__prop || $test$plusargs("disable_assert_final_checks")) \
      else begin                                                             \
        `ASSERT_ERROR(__name)                                                \
      end                                                                    \
  end                                                                        \
`endif

// NOTE: Removed default args for Quartus compatibility
`define ASSERT_AT_RESET(__name, __prop, __rst)                               \
`ifndef FPV_ON                                                               \
  __name: assert property (@(posedge __rst) $isunknown(__rst) || (__prop))   \
`else                                                                        \
  __name: assert property (@(posedge __rst) (__prop))                        \
`endif                                                                       \
    else begin                                                               \
      `ASSERT_ERROR(__name)                                                  \
    end

`define ASSERT_AT_RESET_AND_FINAL(__name, __prop, __rst) \
    `ASSERT_AT_RESET(AtReset_``__name``, __prop, __rst)  \
    `ASSERT_FINAL(Final_``__name``, __prop)

// NOTE: Removed default args for Quartus compatibility
`define ASSERT(__name, __prop, __clk, __rst)                                        \
  __name: assert property (@(posedge __clk) disable iff ((__rst) !== '0) (__prop))  \
    else begin                                                                     \
      `ASSERT_ERROR(__name)                                                        \
    end

// NOTE: Removed default args for Quartus compatibility
`define ASSERT_NEVER(__name, __prop, __clk, __rst)                                  \
  __name: assert property (@(posedge __clk) disable iff ((__rst) !== '0) not (__prop)) \
    else begin                                                                     \
      `ASSERT_ERROR(__name)                                                        \
    end

// NOTE: Removed default args for Quartus compatibility
`define ASSERT_KNOWN(__name, __sig, __clk, __rst) \
`ifndef FPV_ON                                    \
  `ASSERT(__name, !$isunknown(__sig), __clk, __rst) \
`endif

// NOTE: Removed default args for Quartus compatibility
`define COVER(__name, __prop, __clk, __rst) \
  __name: cover property (@(posedge __clk) disable iff ((__rst) !== '0) (__prop));

 // NOTE: Removed default args for Quartus compatibility
`define ASSUME(__name, __prop, __clk, __rst)                                         \
  __name: assume property (@(posedge __clk) disable iff ((__rst) !== '0) (__prop))   \
    else begin                                                                      \
      `ASSERT_ERROR(__name)                                                         \
    end

`define ASSUME_I(__name, __prop) \
  __name: assume (__prop)        \
    else begin                   \
      `ASSERT_ERROR(__name)      \
    end
