// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macro bodies included by prim_assert.sv for formal verification with Yosys. See prim_assert.sv
// for documentation for each of the macros.
















// This doesn't make much sense for a formal tool (we never get to the final block!)


// This needs sampling just before reset assertion and thus requires an event scheduler, which Yosys
// may or may not implement, so we leave it blank for the time being.
















// Yosys uses 2-state logic, so this doesn't make sense here
















