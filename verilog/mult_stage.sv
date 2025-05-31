module mult_stage (
    input logic clock,
    input logic reset, 
    input logic is_last_stage,
    input logic next_stage_free,
    input INTERNAL_MULT_PACKET internal_mult_packet_in,
    input logic b_mm_mispred,
    input B_MASK b_mm_resolve,

    output logic current_stage_free,
    output INTERNAL_MULT_PACKET internal_mult_packet_out
);

    parameter SHIFT = 64/`MULT_STAGES;
    INTERNAL_MULT_PACKET internal_mult_packet;

    always_comb begin
        internal_mult_packet_out.valid        = internal_mult_packet.valid;
        internal_mult_packet_out.prev_sum     = internal_mult_packet.prev_sum + (internal_mult_packet.mplier[SHIFT-1:0] * internal_mult_packet.mcand);
        internal_mult_packet_out.mplier       = {SHIFT'('b0), internal_mult_packet.mplier[63:SHIFT]};
        internal_mult_packet_out.mcand        = {internal_mult_packet.mcand[63-SHIFT:0], SHIFT'('b0)};
        internal_mult_packet_out.dest_reg_idx = internal_mult_packet.dest_reg_idx;
        internal_mult_packet_out.bm           = internal_mult_packet.bm;
        internal_mult_packet_out.func         = internal_mult_packet.func;
        if (b_mm_resolve & internal_mult_packet.bm) begin
            internal_mult_packet_out.bm = internal_mult_packet_out.bm & ~(b_mm_resolve);
            if (b_mm_mispred) begin
                internal_mult_packet_out = NOP_MULT_PACKET;
            end
        end
    end

    assign current_stage_free = next_stage_free || (~internal_mult_packet_out.valid && ~is_last_stage); // Either the next stage is free, or the current stage doesn't have anything

    always_ff @(posedge clock) begin
        // use next_stage_free because we are deciding whether we should update the next mult stage, if in last stage, just forward the packet unconditionally
        //$display("internal_mult_packet_out.dest_reg_idx: %d\ninternal_mult_packet_out.valid: %b\ninternal_mult_packet_out.mplier: %d\ninternal_mult_packet_out.mcand: %d\ninternal_mult_packet_out.prev_sum: %d\n",
        //internal_mult_packet_out.dest_reg_idx, internal_mult_packet_out.valid, internal_mult_packet_out.mplier, internal_mult_packet_out.mcand, internal_mult_packet_out.prev_sum);
        if (reset) begin
            internal_mult_packet <= NOP_MULT_PACKET;        // NOP_MULT_PACKET must have valid to 0;
        end else if (current_stage_free) begin
            internal_mult_packet <= internal_mult_packet_in;
        end
    end

endmodule // mult_stage
