
`include "verilog/sys_defs.svh"

module store_addr_stage (
    input                   clock,
    input                   reset,

    // ------------ FROM ISSUE --------------- //
    input STORE_ADDR_PACKET            store_addr_packet_in,

    // ------------- TO STORE QUEUE ----------//
    output SQ_MASK                     resolving_sq_mask,
    output STORE_QUEUE_PACKET          sq_packet
);

    STORE_ADDR_PACKET store_addr_packet; 
    
    BYTE_MASK temp_byte_mask;

    assign sq_packet.valid = store_addr_packet.valid;
    assign sq_packet.addr = store_addr_packet.source_reg_1 + store_addr_packet.store_imm; 
    assign sq_packet.result = store_addr_packet.source_reg_2 << (sq_packet.addr.w.offset*8);
    assign sq_packet.byte_mask = temp_byte_mask << sq_packet.addr.w.offset;
    assign sq_packet.dest_reg_idx = store_addr_packet.dest_reg_idx;
    assign resolving_sq_mask = store_addr_packet.sq_mask;

    always_comb begin
        case (MEM_SIZE'(store_addr_packet.store_func[1:0]))
            BYTE:       temp_byte_mask = 4'b0001;
            HALF:       temp_byte_mask = 4'b0011;
            WORD:       temp_byte_mask = 4'b1111;
            default:    temp_byte_mask = 4'b0000;
        endcase
    end

    always_ff @(posedge clock) begin
        if(reset) begin
            store_addr_packet <= NOP_STORE_ADDR_PACKET;
        end else begin
            store_addr_packet <= store_addr_packet_in;
        end
        // $display("------ Store addr --------");
        // $display("sq_packet.valid: %b", sq_packet.valid);
        // $display("sq_packet.addr: %h", sq_packet.addr);
        // $display("sq_packet.result: %b", sq_packet.result);
        // $display("sq_packet.byte_mask: %b", sq_packet.byte_mask);
        // $display("sq_packet.dest_reg_idx: %b", sq_packet.dest_reg_idx);
        // $display("store_addr_packet.sq_mask: %b", store_addr_packet.sq_mask);
        // $display("store_addr_packet.source_reg_1: %d", store_addr_packet.source_reg_1);
        // $display("store_addr_packet.store_imm: %d", store_addr_packet.store_imm);
        // $display("store_addr_packet.source_reg_2: %d", store_addr_packet.source_reg_2);
    end

endmodule // alu