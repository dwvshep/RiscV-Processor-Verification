`include "verilog/sys_defs.svh"

module branchstack #(
) (
    input   logic                                      clock, 
    input   logic                                      reset,
    // ------------- TO ALL -------------- //
    output  logic                                      restore_valid,

    // ------------- TO FETCH -------------- //
    output  ADDR                                       PC_restore,

    // ------------- FROM COMPLETE -------------- //
    input   BRANCH_REG_PACKET                          branch_completing,

    // ------------- TO ROB ------------------- //
    output  logic                   [`ROB_SZ_BITS-1:0] rob_tail_restore,

    // ------------- TO FREDDY LIST ----------- //
    input   logic              [`PHYS_REG_SZ_R10K-1:0] free_list_in,
    output  logic              [`PHYS_REG_SZ_R10K-1:0] free_list_restore,

    // ------------- TO/FROM DISPATCH -------------- //
    input   BS_ENTRY_PACKET        [`B_MASK_WIDTH-1:0] branch_stack_entries,
    input   B_MASK                                     next_b_mask,
    output  PHYS_REG_IDX       [`ARCH_REG_SZ_R10K-1:0] map_table_restore,     
    output  B_MASK                                     b_mask_combinational,

    // ------------- TO RS/EXECUTE -------------- //
    output  B_MASK                                     b_mm_out,

    // ------------- TO BRANCH PREDICTOR -------------- //
    output BRANCH_PREDICTOR_PACKET                     bs_bp_packet,
    output logic                                       resolving_valid_branch,

    // ------------- TO BTB -------------- //
    output  logic                                      resolving_valid,
    output  ADDR                                       resolving_target_PC,
    output  ADDR                                       resolving_branch_PC,

    // ------------- FROM STORE UNIT ------------------ //
    input  SQ_MASK                                     sq_mask_resolving,

    // ------------- TO SQ ------------------ //
    output SQ_POINTER                                  sq_tail_restore,
    output SQ_MASK                                     sq_mask_restore
    
`ifdef DEBUG
    , output BS_DEBUG                            bs_debug
`endif
); 

    B_MASK_MASK   b_mm_resolve;
    logic         b_mm_mispred;
    ADDR          target_PC;
    logic         predict_taken;


    assign b_mm_resolve = branch_completing.bmm;
    //assign b_mm_mispred = is_jump..
    assign b_mm_mispred = branch_completing.bm_mispred;
    assign target_PC = branch_completing.target_PC;
    assign predict_taken = branch_completing.predict_taken;
    assign resolving_target_PC = target_PC;


    BS_ENTRY_PACKET [`B_MASK_WIDTH-1:0] branch_stack, next_branch_stack;
    logic [`NUM_B_MASK_BITS-1:0] next_branch_stack_spots;
    
    B_MASK b_mask_reg;
    
    always_comb begin 
        next_branch_stack = branch_stack;
        b_mask_combinational = b_mask_reg;
        for (int i = 0; i < `B_MASK_WIDTH; i++) begin
            next_branch_stack[i].sq_mask &= ~sq_mask_resolving;
            if ((b_mm_mispred && (branch_stack[i].b_m & b_mm_resolve)) || b_mm_resolve[i]) begin
                b_mask_combinational[i] = 1'b0;
                next_branch_stack[i] = '0;
            end else begin
                next_branch_stack[i].b_m = branch_stack[i].b_m & ~b_mm_resolve;
                if (next_branch_stack[i]) begin
                    next_branch_stack[i].free_list = next_branch_stack[i].free_list | free_list_in;
                end
            end
        end
    end

    always_comb begin
        restore_valid = 0;
        PC_restore = '0;
        rob_tail_restore = 0;
        free_list_restore = 0;
        map_table_restore = 0;
        b_mm_out = '0;   
        resolving_valid = '0;
        resolving_valid_branch = '0;
        bs_bp_packet = '0;
        resolving_branch_PC = '0;
        sq_tail_restore = '0;
        sq_mask_restore = '0;
        
        for (int i = 0; i < `B_MASK_WIDTH; i++) begin
            if (b_mm_resolve[i] && b_mask_reg[i]) begin
                b_mm_out[i] = 1'b1;
                bs_bp_packet = branch_stack[i].bp_packet;
                resolving_valid = 1'b1;
                resolving_branch_PC = branch_stack[i].original_PC;
                resolving_valid_branch = !branch_stack[i].is_jump;
                if (b_mm_mispred) begin
                    // || (branch_stack[i].is_jump && (target_PC != branch_stack[i].recovery_PC))
                    restore_valid = 1;
                    PC_restore = (predict_taken && !branch_stack[i].is_jump) ? branch_stack[i].recovery_PC : target_PC;
                    rob_tail_restore = branch_stack[i].rob_tail;
                    free_list_restore = branch_stack[i].free_list;
                    map_table_restore = branch_stack[i].map_table;
                    sq_tail_restore = branch_stack[i].sq_tail;
                    sq_mask_restore = branch_stack[i].sq_mask;
                end
            end
        end  
    end
    
    always_ff @(posedge clock) begin
        if (reset) begin
            //branch_stack_spots <= `B_MASK_WIDTH;
            b_mask_reg <= 0;
            branch_stack <= 0;
        end else begin
            //branch_stack_spots <= next_branch_stack_spots;
            b_mask_reg <= next_b_mask;
            branch_stack <= next_branch_stack | branch_stack_entries;
            // $display("PC_restore: %h", PC_restore);
            // $display("restore_valid: %b", restore_valid);
        end
    end

`ifdef DEBUG
    assign bs_debug.branch_stack = branch_stack;
    assign bs_debug.b_mask_reg = b_mask_reg;
    assign bs_debug.next_branch_stack = next_branch_stack;
`endif

endmodule