// branchstack module testbench
// This module generates the test vectors

`include "verilog/sys_defs.svh"
`include "test/branchstack_sva.svh"

`define DEBUG

module BranchStack_test ();

    logic                                clock; 
    logic                                reset;

    logic                                restore_valid;
    // ------------- TO FETCH -------------- //
    ADDR                                 PC_restore;
    // ------------- FROM COMPLETE -------------- //
    B_MASK_MASK                          b_mm_resolve;
    logic                                b_mm_mispred;
    // ------------- TO ROB ------------------- //
    logic             [`ROB_SZ_BITS-1:0] rob_tail_restore;
    // ------------- TO FREDDY LIST ----------- //
    logic        [`PHYS_REG_SZ_R10K-1:0] free_list_restore;
    // ------------- TO/FROM DISPATCH -------------- //
    BS_ENTRY_PACKET  [`B_MASK_WIDTH-1:0] branch_stack_entries;
    logic            [`B_MASK_WIDTH-1:0] next_b_mask;
    PHYS_REG_IDX [`ARCH_REG_SZ_R10K-1:0] map_table_restore;
    B_MASK                               b_mask_combinational;
    BS_DEBUG                             bs_debug;

    branchstack dut (
        .clock(clock),
        .reset(reset),
        .PC_restore(PC_restore),
        .b_mm_resolve(b_mm_resolve),
        .b_mm_mispred(b_mm_mispred),
        .rob_tail_restore(rob_tail_restore),
        .restore_valid(restore_valid),
        .free_list_restore(free_list_restore),
        .branch_stack_entries(branch_stack_entries),
        .next_b_mask(next_b_mask),
        .map_table_restore(map_table_restore),
        .b_mask_combinational(b_mask_combinational),
        .bs_debug(bs_debug)
    );

    BranchStack_sva dut_sva(
        .clock(clock),
        .reset(reset),
        .PC_restore(PC_restore),
        .restore_valid(restore_valid),
        .b_mm_resolve(b_mm_resolve),
        .b_mm_mispred(b_mm_mispred),
        .rob_tail_restore(rob_tail_restore),
        .free_list_restore(free_list_restore),
        .branch_stack_entries(branch_stack_entries),
        .next_b_mask(next_b_mask),
        .map_table_restore(map_table_restore),
        .b_mask_combinational(b_mask_combinational),
        .bs_debug(bs_debug)
    );

    always begin
        #(`CLOCK_PERIOD/2) clock = ~clock;
    end


    // Only recovery PC and b_m is randomize for this purpose
    task randomize_all_bs(output BS_ENTRY_PACKET [`B_MASK_WIDTH-1:0] bs_entries);
        for(int i = 0; i < `B_MASK_WIDTH; ++i) begin
            bs_entries[i] = $urandom;
        end
    endtask

    task randomize_one_hot_bmm(output logic [`B_MASK_WIDTH-1:0] bmm);
        int rand_idx;
        rand_idx = $urandom_range(0, `B_MASK_WIDTH-1);
        bmm = 1'b1 << rand_idx;
    endtask

    task dispatch_based_on_b_mask_combinational(input logic [`B_MASK_WIDTH-1:0] bm_comb, output BS_ENTRY_PACKET [`B_MASK_WIDTH-1:0] bs_entries, output logic [`B_MASK_WIDTH-1:0] next_bm);
        for(int i = 0; i < `B_MASK_WIDTH; ++i) begin
            if(!bm_comb[i]) begin
                bs_entries[i] = $urandom;
                next_bm[i] = 1'b1;
            end else begin
                bs_entries[i] = 0;
                next_bm[i] = bm_comb[i];
            end
        end
    endtask

    initial begin
        $display("\nStart Testbench");

        clock = 1;
        reset = 1;

        $monitor("  %3d | reset: %b   b_mm_resolve: %b   b_mm_mispred: %0d,   next_b_mask: %b,   b_mask_combinational: %b,   branch_stack[0]: %0b,       next_branch_stack[0]: %0b",
                  $time,  reset, b_mm_resolve,      b_mm_mispred,        next_b_mask,       b_mask_combinational,       bs_debug.branch_stack[0],     bs_debug.next_branch_stack[0]);

        @(negedge clock);
        @(negedge clock);
        reset = 0;
        b_mm_resolve = 0;
        b_mm_mispred = 0;
        branch_stack_entries = 0;
        next_b_mask = 0;

        // fill the branch stack 
        next_b_mask = ~0;
        randomize_all_bs(branch_stack_entries);
        @(negedge clock);

        // ---------- Test 1 ---------- //
        $display("\nTest 1: No Dispatch, No Mispredict");
        $display("Randomize b_mm_resolve");
        
        branch_stack_entries = 0;
        b_mm_mispred = 0;

        // @(negedge clock);
        
        for (int i = 0; i < 50; ++i) begin
            branch_stack_entries = 0;
            randomize_one_hot_bmm(b_mm_resolve);
            #1;
            next_b_mask = b_mask_combinational;
            @(negedge clock);
            b_mm_resolve = 0;
            dispatch_based_on_b_mask_combinational(b_mask_combinational, branch_stack_entries, next_b_mask); // Fill branch stack back up
            @(negedge clock);
        end

        // ---------- Test 2 ---------- //
        $display("\nTest 2: No Dispatch, Yes Mispredict ");
        $display("Randomize b_mm_resolve");

        b_mm_mispred = 1;
        
        for (int i = 0; i < 50; ++i) begin
            branch_stack_entries = 0;
            randomize_one_hot_bmm(b_mm_resolve);
            #1;
            next_b_mask = b_mask_combinational;
            @(negedge clock);
            b_mm_resolve = 0;
            dispatch_based_on_b_mask_combinational(b_mask_combinational, branch_stack_entries, next_b_mask);
            @(negedge clock);
        end

        // ---------- Test 3 ---------- //
        $display("\nTest 3: Yes Dispatch, No Mispredict");
        $display("Randomize b_mm_resolve");

        b_mm_mispred = 0;
        branch_stack_entries = 0;
        
        for (int i = 0; i < 50; ++i) begin
            b_mm_mispred = 0;
            randomize_one_hot_bmm(b_mm_resolve);
            #1; 
            dispatch_based_on_b_mask_combinational(b_mask_combinational, branch_stack_entries, next_b_mask);
            @(negedge clock);
            branch_stack_entries = 0;
            randomize_one_hot_bmm(b_mm_resolve);
            b_mm_mispred = 1;
            #1;
            next_b_mask = b_mask_combinational;
            @(negedge clock);
        end


        @(negedge clock);

        $display("\n\033[32m@@@ Passed\033[0m\n");
        $finish;

    end


endmodule