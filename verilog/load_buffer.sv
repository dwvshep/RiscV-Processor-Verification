`include "verilog/sys_defs.svh"

module load_buffer(
    input   logic                                 clock, 
    input   logic                                 reset,

    // ------------ TO/FROM LOAD_FU ------------- //
    input   LOAD_BUFFER_PACKET                    load_buffer_packet_in, // New instructions from Dispatch, MUST BE IN ORDER FROM OLDEST TO NEWEST INSTRUCTIONS
    output  logic                                 load_buffer_free,

    // ------------- TO/FROM CACHE -------------- //
    input   LOAD_BUFFER_CACHE_PACKET              load_buffer_cache_packet,

    // ------------- TO/FROM ISSUE -------------- //
    input  logic            [`LOAD_BUFFER_SZ-1:0] load_cdb_gnt,
    output logic            [`LOAD_BUFFER_SZ-1:0] load_cdb_req,

    // ------------ TO CDB ------------- //
    output CDB_REG_PACKET   [`LOAD_BUFFER_SZ-1:0] load_result,

    // ------------ FROM BS ------------- //
    input B_MASK                                b_mm_resolve,
    input logic                                 b_mm_mispred
);

    logic [`LOAD_BUFFER_SZ-1:0] load_buffer_valid, next_load_buffer_valid, chosen_spot, new_load;
    LOAD_BUFFER_PACKET [`LOAD_BUFFER_SZ-1:0] load_buffer, next_load_buffer;

    psel_gen #(
         .WIDTH(`LOAD_BUFFER_SZ),
         .REQS(1)
    ) psel_inst (
         .req(~(load_buffer_valid)),
         .gnt(chosen_spot)
    );
    
    assign new_load = load_buffer_packet_in.valid ? chosen_spot : '0;

    always_comb begin
        next_load_buffer_valid = load_buffer_valid;
        next_load_buffer = load_buffer;

        for (int i = 0; i < `LOAD_BUFFER_SZ; ++i) begin
            if (b_mm_resolve & load_buffer[i].bm) begin
                next_load_buffer[i].bm = load_buffer[i].bm & ~(b_mm_resolve);
                if (b_mm_mispred) begin
                    next_load_buffer[i] = NOP_LOAD_BUFFER_PACKET;
                    next_load_buffer_valid[i] = 1'b0;
                end
            end
        end

        for (int i = 0; i < `LOAD_BUFFER_SZ; ++i) begin    
            load_cdb_req[i] = next_load_buffer_valid[i] && !load_buffer[i].byte_mask;
        end
        
        next_load_buffer_valid = next_load_buffer_valid ^ load_cdb_gnt ^ new_load;
        load_buffer_free = ~(&next_load_buffer_valid);

        for (int i = 0; i < `LOAD_BUFFER_SZ; ++i) begin
            if (new_load[i]) begin
                next_load_buffer[i] = load_buffer_packet_in;
            end
        end

        for (int i = 0; i < `LOAD_BUFFER_SZ; ++i) begin
            if (load_buffer_cache_packet.valid && load_buffer[i].mshr_idx == load_buffer_cache_packet.mshr_idx) begin
                for (int j = 0; j < 4; j++) begin
                    if (load_buffer[i].byte_mask[j]) begin
                        next_load_buffer[i].result.bytes[j] = load_buffer_cache_packet.data[load_buffer[i].load_addr.dw.w_idx].bytes[j];
                        next_load_buffer[i].byte_mask[j] = 1'b0;
                    end
                end
            end
        end

        for (int i = 0; i < `LOAD_BUFFER_SZ; ++i) begin
            load_result[i].result = sign_extend(load_buffer[i].result, load_buffer[i].load_addr.w.offset, load_buffer[i].load_func);
            load_result[i].completing_reg = load_buffer[i].dest_reg_idx; 
            load_result[i].valid = load_buffer[i].valid;
        end
    end

    function logic signed [31:0] sign_extend(input DATA result, input logic [1:0] offset, input LOAD_FUNC func);
        sign_extend = result >> (offset*8);
        if (func[2]) begin
            // unsigned: zero-extend the data
            if (MEM_SIZE'(func[1:0]) == BYTE) begin
                sign_extend[31:8] = 0;
            end else if (MEM_SIZE'(func[1:0]) == HALF) begin
                sign_extend[31:16] = 0;
            end
        end else begin
            // signed: sign-extend the data
            if (MEM_SIZE'(func[1:0]) == BYTE) begin
                sign_extend[31:8] = {(24){sign_extend[7]}};
            end else if (MEM_SIZE'(func[1:0]) == HALF) begin
                sign_extend[31:16] = {(16){sign_extend[15]}};
            end
        end
    endfunction

    always_ff @(posedge clock) begin
        if (reset) begin
            load_buffer_valid <= '0;
            load_buffer <= '0;
        end else begin
            load_buffer_valid <= next_load_buffer_valid;
            load_buffer <= next_load_buffer;       
        end
        // $display("load_cdb_grant: %b", load_cdb_gnt); //in case its some dont care
        // $display("load_buffer_valid: %b", load_buffer_valid); //in case its some dont care
        // $display("new_load: %b", new_load); //in case its some dont care
        // for(int ii = 0; ii < `LOAD_BUFFER_SZ; ++ii) begin
        //     $display("load_buffer[%d].load_addr: %h", ii, load_buffer[ii].load_addr); //in case its some dont care
        //     $display("load_buffer[%d].valid: %b", ii, load_buffer[ii].valid); //in case its some dont care
        //     $display("next_load_buffer[%d].valid: %h", ii, next_load_buffer[ii].valid); //in case its some dont care
        //     $display("load_buffer[%d].result: %h", ii, load_buffer[ii].result); //in case its some dont care
        //     $display("load_buffer[%d].mshr_idx: %h", ii, load_buffer[ii].mshr_idx); //in case its some dont care
        //     $display("load_buffer[%d].byte_mask: %b", ii, load_buffer[ii].byte_mask); //in case its some dont care
        //     $display("load_result[%d].result: %h", ii, load_result[ii].result);
        // end
    end

endmodule