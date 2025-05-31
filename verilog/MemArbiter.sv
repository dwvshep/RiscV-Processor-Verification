`include "verilog/sys_defs.svh"

module memarbiter (
    input logic clock,
    input logic reset,

    // ------------------- TO/FROM DCACHE --------------- //
    input  MEM_REQ_PACKET                    dcache_mem_req_packet,
    output logic                             dcache_mem_req_accepted,

    // ------------------- TO/FROM ICACHE --------------- //
    input  MEM_REQ_PACKET                    icache_mem_req_packet,
    output logic                             icache_mem_req_accepted,

    // ------------------- TO CACHES --------------- //
    output MEM_TAG                           mem_trxn_tag,
    output MEM_DATA_PACKET                   mem_data_packet,

    // ------------------- TO/FROM MAIN MEM --------------//
    input  MEM_TAG                           mem2proc_transaction_tag,
    input  MEM_BLOCK                         mem2proc_data,
    input  MEM_TAG                           mem2proc_data_tag,
    output ADDR                              proc2mem_addr,
    output MEM_BLOCK                         proc2mem_data,
    output MEM_COMMAND                       proc2mem_command           

);

    assign mem_trxn_tag = mem2proc_transaction_tag;
    assign mem_data_packet.data = mem2proc_data;
    assign mem_data_packet.mem_tag = mem2proc_data_tag;

    always_comb begin
        //defaults
        dcache_mem_req_accepted = 0;
        icache_mem_req_accepted = 0;
        proc2mem_command = 0;
        proc2mem_addr = '0;
        proc2mem_data = '0;

        if (dcache_mem_req_packet.valid && dcache_mem_req_packet.prior == 1) begin
            dcache_mem_req_accepted = 1;
            proc2mem_addr = dcache_mem_req_packet.addr;
            proc2mem_data = dcache_mem_req_packet.data;
            proc2mem_command = 1;
        end else if (icache_mem_req_packet.valid && icache_mem_req_packet.prior == 1) begin
            icache_mem_req_accepted = 1;
            proc2mem_addr = icache_mem_req_packet.addr;
            proc2mem_data = icache_mem_req_packet.data;
            proc2mem_command = 1;
        end else if (dcache_mem_req_packet.valid && dcache_mem_req_packet.prior == 0) begin
            dcache_mem_req_accepted = 1;
            proc2mem_addr = dcache_mem_req_packet.addr;
            proc2mem_data = dcache_mem_req_packet.data;
            proc2mem_command = 2;
        end else if (icache_mem_req_packet.valid && icache_mem_req_packet.prior == 0) begin
            icache_mem_req_accepted = 1;
            proc2mem_addr = icache_mem_req_packet.addr;
            proc2mem_data = icache_mem_req_packet.data;
            proc2mem_command = 1;
        end
    end

    always_ff @(posedge clock) begin
        // $display("---------MEM ARB -----------");

        // $display("mem_trxn_tag: %d", mem_trxn_tag);
        // $display("mem_data_packet.data: %h", mem_data_packet.data);
        // $display("mem_data_packet.mem_tag: %d", mem_data_packet.mem_tag);
        // $display("dcache_mem_req_accepted: %b", dcache_mem_req_accepted);
        // $display("icache_mem_req_accepted: %b", icache_mem_req_accepted);
        // $display("proc2mem_command: %d", proc2mem_command);
        // $display("proc2mem_addr: %d", proc2mem_command);
        // $display("proc2mem_data: %d", proc2mem_command);
    end

endmodule