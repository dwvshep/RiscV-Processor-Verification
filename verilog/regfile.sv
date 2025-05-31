/////////////////////////////////////////////////////////////////////////
//                                                                     //
//   Modulename :  regfile.sv                                          //
//                                                                     //
//  Description :  This module creates the Regfile used by the ID and  //
//                 WB Stages of the Pipeline.                          //
//                                                                     //
/////////////////////////////////////////////////////////////////////////

`include "verilog/sys_defs.svh"

// P4 TODO: update this with the new parameters from sys_defs
// namely: PHYS_REG_SZ_P6 or PHYS_REG_SZ_R10K

module regfile (
    input         clock, // system clock
    input         reset,
    
    /*---------------- FROM/TO RETIRE ---------------------------*/
    input PHYS_REG_IDX [`N-1:0] retire_phys_regs_reading,
    // input              [`N-1:0] retire_read_en,
    output DATA        [`N-1:0] retire_read_data,

    /*---------------- FROM/TO ISSUE ---------------------------*/
    input PHYS_REG_IDX [`NUM_FU_ALU-1:0] issue_alu_regs_reading_1,
    input PHYS_REG_IDX [`NUM_FU_ALU-1:0] issue_alu_regs_reading_2,
    output DATA        [`NUM_FU_ALU-1:0] issue_alu_read_data_1,
    output DATA        [`NUM_FU_ALU-1:0] issue_alu_read_data_2,

    input PHYS_REG_IDX [`NUM_FU_BRANCH-1:0] issue_branch_regs_reading_1,
    input PHYS_REG_IDX [`NUM_FU_BRANCH-1:0] issue_branch_regs_reading_2,
    output DATA        [`NUM_FU_BRANCH-1:0] issue_branch_read_data_1,
    output DATA        [`NUM_FU_BRANCH-1:0] issue_branch_read_data_2,

    input PHYS_REG_IDX [`NUM_FU_MULT-1:0] issue_mult_regs_reading_1,
    input PHYS_REG_IDX [`NUM_FU_MULT-1:0] issue_mult_regs_reading_2,
    output DATA        [`NUM_FU_MULT-1:0] issue_mult_read_data_1,
    output DATA        [`NUM_FU_MULT-1:0] issue_mult_read_data_2,

    input PHYS_REG_IDX [`NUM_FU_LOAD-1:0] issue_load_regs_reading_1,
    output DATA        [`NUM_FU_LOAD-1:0] issue_load_read_data_1,

    input PHYS_REG_IDX [`NUM_FU_STORE-1:0] issue_store_regs_reading_1,
    input PHYS_REG_IDX [`NUM_FU_STORE-1:0] issue_store_regs_reading_2,
    output DATA        [`NUM_FU_STORE-1:0] issue_store_read_data_1,
    output DATA        [`NUM_FU_STORE-1:0] issue_store_read_data_2,

    // note: no system reset, register values must be written before they can be read
    input CDB_REG_PACKET [`N-1:0] cdb_reg
);
    genvar i;

    // Intermediate data before accounting for register 0
    DATA  rdata2, rdata1;
    // Don't read or write when dealing with register 0
    logic re2, re1;
    logic we;

    //actual data structure
    DATA [`PHYS_REG_SZ_R10K-1:0] reg_file;

    // Read for Retire
    generate
        for (i = 0; i < `N; ++i) begin
            assign retire_read_data[i] = reg_file[retire_phys_regs_reading[i]];
        end
    endgenerate

    // Read for Issue
    generate
        for(i = 0; i < `NUM_FU_ALU; ++i) begin
            assign issue_alu_read_data_1[i] = reg_file[issue_alu_regs_reading_1[i]];
            assign issue_alu_read_data_2[i] = reg_file[issue_alu_regs_reading_2[i]];
        end
    endgenerate
    
    generate
        for(i = 0; i < `NUM_FU_BRANCH; ++i) begin
            assign issue_branch_read_data_1[i] = reg_file[issue_branch_regs_reading_1[i]];
            assign issue_branch_read_data_2[i] = reg_file[issue_branch_regs_reading_2[i]];
        end
    endgenerate
    
    generate
        for (i = 0; i < `NUM_FU_MULT; ++i) begin
            assign issue_mult_read_data_1[i] = reg_file[issue_mult_regs_reading_1[i]];
            assign issue_mult_read_data_2[i] = reg_file[issue_mult_regs_reading_2[i]];
        end
    endgenerate

    generate
        for (i = 0; i < `NUM_FU_LOAD; ++i) begin
            assign issue_load_read_data_1[i] = reg_file[issue_load_regs_reading_1[i]];
        end
    endgenerate

    generate
        for (i = 0; i < `NUM_FU_STORE; ++i) begin
            assign issue_store_read_data_1[i] = reg_file[issue_store_regs_reading_1[i]];
            assign issue_store_read_data_2[i] = reg_file[issue_store_regs_reading_2[i]];
        end
    endgenerate

    always_ff @(posedge clock) begin
        if (reset) begin
            reg_file <= '0;
        end else begin
            for(int i = 0; i < `N; ++i) begin
                // $display("cdb_reg[%d].result: %h", i, cdb_reg[i].result);
                if (cdb_reg[i].valid && (cdb_reg[i].completing_reg != 0)) begin
                    reg_file[cdb_reg[i].completing_reg] <= cdb_reg[i].result;
                end
            end
        end
    end
endmodule // regfile
