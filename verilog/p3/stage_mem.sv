/////////////////////////////////////////////////////////////////////////
//                                                                     //
//   Modulename :  stage_mem.sv                                        //
//                                                                     //
//  Description :  memory access (MEM) stage of the pipeline;          //
//                 this stage accesses memory for stores and loads,    //
//                 and selects the proper next PC value for branches   //
//                 based on the branch condition computed in the       //
//                 previous stage.                                     //
//                                                                     //
/////////////////////////////////////////////////////////////////////////

`include "sys_defs.svh"

module stage_mem (
    input EX_MEM_PACKET  ex_mem_reg,
    // the MEM_LOAD response will magically be present in the *same* cycle it's requested (0ns latency)
    // this will not be true in project 4 (100ns latency)
    input MEM_BLOCK      Dmem_load_data, // Data loaded from memory

    output MEM_WB_PACKET mem_packet,
    output MEM_COMMAND   Dmem_command,   // The memory command
    output MEM_SIZE      Dmem_size,      // Size of data to read or write
    output ADDR          Dmem_addr,      // Address sent to Data memory
    output MEM_BLOCK     Dmem_store_data // Data sent to Data memory
);

    DATA load_data;

    assign mem_packet.result = (ex_mem_reg.rd_mem) ? load_data : ex_mem_reg.alu_result;

    // Pass-throughs
    assign mem_packet.NPC          = ex_mem_reg.NPC;
    assign mem_packet.valid        = ex_mem_reg.valid;
    assign mem_packet.halt         = ex_mem_reg.halt;
    assign mem_packet.illegal      = ex_mem_reg.illegal;
    assign mem_packet.dest_reg_idx = ex_mem_reg.dest_reg_idx;
    assign mem_packet.take_branch  = ex_mem_reg.take_branch;

    // Outputs from the processor to memory
    assign Dmem_command = (ex_mem_reg.valid && ex_mem_reg.wr_mem) ? MEM_STORE :
                          (ex_mem_reg.valid && ex_mem_reg.rd_mem) ? MEM_LOAD : MEM_NONE;
    assign Dmem_size = ex_mem_reg.mem_size;
    assign Dmem_addr = ex_mem_reg.alu_result; // Memory address is calculated by the ALU
    assign Dmem_store_data = {32'b0, ex_mem_reg.rs2_value}; // for p3, just use low 32 bits

    // Read data from memory and sign extend the proper bits
    always_comb begin
        load_data = Dmem_load_data[31:0]; // for p3, just use low 32 bits
        if (ex_mem_reg.rd_unsigned) begin
            // unsigned: zero-extend the data
            if (ex_mem_reg.mem_size == BYTE) begin
                load_data[31:8] = 0;
            end else if (ex_mem_reg.mem_size == HALF) begin
                load_data[31:16] = 0;
            end
        end else begin
            // signed: sign-extend the data
            if (ex_mem_reg.mem_size == BYTE) begin
                load_data[31:8] = {(24){load_data[7]}};
            end else if (ex_mem_reg.mem_size == HALF) begin
                load_data[31:16] = {(16){load_data[15]}};
            end
        end
    end

endmodule // stage_mem
