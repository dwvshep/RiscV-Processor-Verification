
`include "verilog/sys_defs.svh"

module load_data_stage (
    input clock,
    input reset,
    // ------------ FROM LOAD ADDR STAGE ------------- //
    input LOAD_DATA_PACKET          load_data_packet_in,
    output logic                    load_data_free,
    
    // ------------ TO/FROM CACHE ------------- //
    input LOAD_DATA_CACHE_PACKET    load_data_cache_packet,
    output logic                    load_req_valid,

    // ------------ TO/FROM STORE QUEUE ------------- //
    input DATA                      sq_load_data,
    input BYTE_MASK                 sq_data_mask,
    output SQ_POINTER               load_sq_tail,
    output ADDR                     load_req_addr, //also goes to cache
    
    // ------------ TO LOAD BUFFER ------------- //
    output LOAD_BUFFER_PACKET       load_buffer_packet,

    // ------------ FROM BS ------------- //
    input B_MASK                                b_mm_resolve,
    input logic                                 b_mm_mispred
);

    LOAD_DATA_PACKET load_data_packet;

    //ldback press

    // TODO: make sure this logic is correct
    assign load_data_free = ((b_mm_resolve & load_data_packet.bm) && b_mm_mispred) || !load_data_packet.valid || load_data_cache_packet.valid || !load_buffer_packet.byte_mask;
    assign load_req_addr = load_data_packet.load_addr;
    assign load_req_valid = load_data_packet.valid;
    assign load_sq_tail = load_data_packet.sq_tail;

    always_comb begin
        load_buffer_packet.mshr_idx = load_data_cache_packet.mshr_idx;
        load_buffer_packet.bm = load_data_packet.bm;
        load_buffer_packet.dest_reg_idx = load_data_packet.dest_reg_idx;
        load_buffer_packet.load_addr = load_data_packet.load_addr;
        load_buffer_packet.load_func = load_data_packet.load_func;
        load_buffer_packet.result = '0;
        load_buffer_packet.byte_mask = load_data_packet.byte_mask;
        for (int i = 0; i < 4; ++i) begin
            if (load_data_packet.byte_mask[i]) begin
                if (sq_data_mask[i]) begin
                    load_buffer_packet.result.bytes[i] = sq_load_data.bytes[i];
                    load_buffer_packet.byte_mask[i] = 1'b0;
                end else if (load_data_cache_packet.byte_mask[load_data_packet.load_addr.dw.w_idx][i]) begin
                    load_buffer_packet.result.bytes[i] = load_data_cache_packet.data[load_data_packet.load_addr.dw.w_idx].bytes[i];
                    load_buffer_packet.byte_mask[i] = 1'b0;
                end
            end 
        end

        // TODO: make sure this logic is correct
        load_buffer_packet.valid = load_data_packet.valid && (load_data_cache_packet.valid || !load_buffer_packet.byte_mask);

        if (b_mm_resolve & load_data_packet.bm) begin
            load_buffer_packet.bm = load_data_packet.bm & ~(b_mm_resolve);
            if (b_mm_mispred) begin
                load_buffer_packet = NOP_LOAD_BUFFER_PACKET;
            end
        end
    end

    always_ff @(posedge clock) begin
        if(reset) begin
            load_data_packet <= NOP_LOAD_DATA_PACKET;
        end else if (load_data_free) begin
            load_data_packet <= load_data_packet_in;
        end
        // $display("-------load data stage------");
        // $display("load_data_packet.valid: %h", load_data_packet.valid);
        // $display("load_data_packet.load_addr: %h", load_data_packet.load_addr);
        // $display("load_buffer_packet.result: %h", load_buffer_packet.result);
        // $display("load_buffer_packet.valid: %h", load_buffer_packet.valid);
        // $display("sq_load_data: %h", sq_load_data);
        // $display("load_data_packet.dest_reg_idx: %h", load_data_packet.dest_reg_idx);
        // $display("load_data_cache_packet.valid: %h", load_data_cache_packet.valid);
        // $display("load_data_cache_packet.byte_mask: %b", load_data_cache_packet.byte_mask);
        // $display("load_data_cache_packet.data: %h", load_data_cache_packet.data);
        // $display("load_data_cache_packet.mshr_idx: %d", load_data_cache_packet.mshr_idx);

    end

endmodule // alu