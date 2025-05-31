// SystemVerilog Assertions (SVA) for use with our FIFO module
// This file is included by the testbench to separate our main module checking code
// SVA are relatively new to 470, feel free to use them in the final project if you like

`include "verilog/sys_defs.svh"

module execute_sva #(
) (
    input   logic                               clock,
    input   logic                               reset,

    // --------------- TO/FROM ISSUE --------------- //
    input MULT_PACKET         [`NUM_FU_MULT-1:0] mult_packets_issuing_in, 
    input ALU_PACKET           [`NUM_FU_ALU-1:0] alu_packets_issuing_in,
    input BRANCH_PACKET     [`NUM_FU_BRANCH-1:0] branch_packets_issuing_in,
    input logic               [`NUM_FU_MULT-1:0] mult_cdb_en,
    input logic               [`NUM_FU_LDST-1:0] ldst_cdb_en,
    input logic [`N-1:0]     [`NUM_FU_TOTAL-1:0] complete_gnt_bus,

    input logic              [`NUM_FU_MULT-1:0] mult_free,
    input logic              [`NUM_FU_LDST-1:0] ldst_free,

    input logic              [`NUM_FU_MULT-1:0] mult_cdb_valid,
    input logic              [`NUM_FU_LDST-1:0] ldst_cdb_valid,

    // ------------ TO ALL DATA STRUCTURES ------------- //
    input CDB_ETB_PACKET               [`N-1:0] cdb_completing,
    input CDB_REG_PACKET               [`N-1:0] cdb_reg,

    // --------------- TO/FROM BRANCH STACK --------------- //
    input B_MASK_MASK                          b_mm_resolve,        // b_mm_out
    input logic                                b_mm_mispred,        // restore_valid
    input BRANCH_REG_PACKET                   branch_reg          // bitvector of the phys reg that are complete
);



/*Conditions that must be met
    1. All single cycle instructions selected by CDB should go on CDB
    2. Multiplier should 

*/



property valid_alu_insts (int i);
    for(int i = 0; i < `NUM_FU_ALU; ++i) begin
        

    end
endproperty













endmodule