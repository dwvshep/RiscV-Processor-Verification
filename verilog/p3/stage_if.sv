/////////////////////////////////////////////////////////////////////////
//                                                                     //
//   Modulename :  stage_if.sv                                         //
//                                                                     //
//  Description :  instruction fetch (IF) stage of the pipeline;       //
//                 fetch instruction, compute next PC location, and    //
//                 send them down the pipeline.                        //
//                                                                     //
/////////////////////////////////////////////////////////////////////////

`include "sys_defs.svh"

module stage_if (
    input           clock,          // system clock
    input           reset,          // system reset
    input           if_valid,       // only go to next PC when true
    input           take_branch,    // taken-branch signal
    input ADDR      branch_target,  // target pc: use if take_branch is TRUE
    input MEM_BLOCK Imem_data,      // data coming back from Instruction memory

    // tags from memory
    input MEM_TAG   Imem2proc_transaction_tag, // Should be zero unless there is a response
    input MEM_TAG   Imem2proc_data_tag,

    output MEM_COMMAND  Imem_command, // Command sent to memory
    output IF_ID_PACKET if_packet,
    output ADDR         Imem_addr // address sent to Instruction memory
);

    ADDR PC_reg; // PC we are currently fetching
    MEM_BLOCK icache_out;
    logic   icache_valid;

    logic   valid_out;

    icache icache_0 (
        // inputs
        .clock                      (clock),
        .reset                      (reset),
        .Imem2proc_transaction_tag  (Imem2proc_transaction_tag),
        .Imem2proc_data             (Imem_data),
        .Imem2proc_data_tag         (Imem2proc_data_tag),
        .proc2Icache_addr           (PC_reg),
        // outputs
        .proc2Imem_command          (Imem_command),
        .proc2Imem_addr             (Imem_addr),
        .Icache_data_out            (icache_out), // Data is mem[proc2Icache_addr]
        .Icache_valid_out           (icache_valid) // When valid is high
    );

    always_ff @(posedge clock) begin
        if (reset) begin
            PC_reg <= 0;             // initial PC value is 0 (the memory address where our program starts)
        end else if (take_branch) begin
            PC_reg <= branch_target; // update to a taken branch (does not depend on valid bit)
        end else if (valid_out) begin
            PC_reg <= PC_reg + 4;    // or transition to next PC if valid
        end
    end

    logic if_valid_q;

    // Keep if valid until it gets valid data out
    always_ff @(posedge clock) begin
        if (reset) begin
            if_valid_q <= 1'b0;
        end else begin
            if_valid_q <= if_valid || (if_valid_q && !valid_out);
        end
    end

    assign valid_out = icache_valid && if_valid_q;

    // index into the word (32-bits) of memory that matches this instruction
    assign if_packet.inst = valid_out ? icache_out.word_level[PC_reg[2]] : `NOP;

    assign if_packet.PC  = PC_reg;
    assign if_packet.NPC = PC_reg + 4; // pass PC+4 down pipeline w/instruction

    assign if_packet.valid = valid_out;

endmodule // stage_if
