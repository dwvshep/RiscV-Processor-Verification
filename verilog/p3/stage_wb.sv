/////////////////////////////////////////////////////////////////////////
//                                                                     //
//   Modulename :  stage_wb.sv                                         //
//                                                                     //
//  Description :   writeback (WB) stage of the pipeline;              //
//                  determine the destination register of the          //
//                  instruction and write the result to the register   //
//                  file (if not to the zero register), also reset the //
//                  NPC in the fetch stage to the correct next PC      //
//                  address.                                           //
//                                                                     //
/////////////////////////////////////////////////////////////////////////

`include "sys_defs.svh"

module stage_wb (
    input MEM_WB_PACKET mem_wb_reg,

    output COMMIT_PACKET wb_packet
);

    // Select register writeback data:
    // ALU/MEM result, unless taken branch, in which case we write
    // back the old NPC as the return address. Note that ALL branches
    // and jumps write back the 'link' value, but those that don't
    // use it specify ZERO_REG as the destination.
    assign wb_packet.data = (mem_wb_reg.take_branch) ? mem_wb_reg.NPC : mem_wb_reg.result;

    // Pass-throughs
    assign wb_packet.NPC     = mem_wb_reg.NPC;
    assign wb_packet.reg_idx = mem_wb_reg.dest_reg_idx;
    assign wb_packet.illegal = mem_wb_reg.illegal && mem_wb_reg.valid;
    assign wb_packet.halt    = mem_wb_reg.halt && mem_wb_reg.valid;
    assign wb_packet.valid   = mem_wb_reg.valid;

endmodule // stage_wb
