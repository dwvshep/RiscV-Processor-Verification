// ROB module testbench
// This module generates the test vectors
// Correctness checking is in FIFO_sva.svh

`include "verilog/sys_defs.svh"
`include "test/rs_sva.svh"

`define DEBUG

module Dispatch_test ();
    logic                               clock;
    logic                               reset;

    // ------------ FROM INSTRUCTION BUFFER ------------- //
    FETCH_PACKET                        instruction_packets;
    logic        [`NUM_SCALAR_BITS-1:0] instructions_valid;

    // ------------ TO/FROM BRANCH STACK ------------- //
    PHYS_REG_IDX    [`ARCH_REG_SZ_R10K] map_table_restore;
    logic                               restore_valid;
    B_MASK                              b_mask_combinational;
    BS_ENTRY_PACKET [`B_MASK_WIDTH-1:0] branch_stack_entries;
    B_MASK                              next_b_mask;

    // ------------ TO/FROM ROB ------------- //
    logic            [`ROB_SZ_BITS-1:0] rob_tail;
    logic        [`NUM_SCALAR_BITS-1:0] rob_spots;
    ROB_ENTRY_PACKET           [`N-1:0] rob_entries;

    // ------------ TO/FROM RS ------------- //
    RS_PACKET                  [`N-1:0] rs_entries;
    logic        [`NUM_SCALAR_BITS-1:0] rs_spots;

    // ------------ TO/FROM FREDDY LIST ------------- //
    logic        [`NUM_SCALAR_BITS-1:0] num_regs_available;
    logic       [`PHYS_REG_SZ_R10K-1:0] next_complete_list;
    PHYS_REG_IDX               [`N-1:0] regs_to_use;
    logic       [`PHYS_REG_SZ_R10K-1:0] free_list_copy;
    logic       [`PHYS_REG_SZ_R10K-1:0] updated_free_list;
    
    // ------------ FROM ISSUE? ------------- //
    logic       [`NUM_SCALAR_BITS-1:0] num_issuing;

    // ------------ TO ALL DATA STRUCTURES ------------- //
    logic       [`NUM_SCALAR_BITS-1:0] num_dispatched;

    DISPATCH_DEBUG                 dispatch_debug;

    Dispatch dut (
        .clock                (clock),
        .reset                (reset),
        .instruction_packets  (instruction_packets),
        .instructions_valid   (instructions_valid), 
        .map_table_restore    (map_table_restore),
        .restore_valid        (restore_valid),
        .b_mask_combinational (b_mask_combinational),
        .branch_stack_entries (branch_stack_entries),
        .next_b_mask          (next_b_mask),
        .rob_tail             (rob_tail),
        .rob_spots            (rob_spots),
        .rob_entries          (rob_entries),
        .rs_entries           (rs_entries),
        .rs_spots             (rs_spots),
        .num_regs_available   (num_regs_available),
        .next_complete_list   (next_complete_list),
        .regs_to_use          (regs_to_use),
        .free_list_copy       (free_list_copy),
        .updated_free_list    (updated_free_list),
        .num_issuing          (num_issuing),
        .num_dispatched       (num_dispatched),
        .dispatch_debug       (dispatch_debug)
    );
    
    RS_sva DUT_sva (
        .clock                (clock),
        .reset                (reset),
        .instruction_packets  (instruction_packets),
        .instructions_valid   (instructions_valid), 
        .map_table_restore    (map_table_restore),
        .restore_valid        (restore_valid),
        .b_mask_combinational (b_mask_combinational),
        .branch_stack_entries (branch_stack_entries),
        .next_b_mask          (next_b_mask),
        .rob_tail             (rob_tail),
        .rob_spots            (rob_spots),
        .rob_entries          (rob_entries),
        .rs_entries           (rs_entries),
        .rs_spots             (rs_spots),
        .num_regs_available   (num_regs_available),
        .next_complete_list   (next_complete_list),
        .regs_to_use          (regs_to_use),
        .free_list_copy       (free_list_copy),
        .updated_free_list    (updated_free_list),
        .num_issuing          (num_issuing),
        .num_dispatched       (num_dispatched),
        .dispatch_debug       (dispatch_debug)
    );
    
    always begin
        #(`CLOCK_PERIOD/2) clock = ~clock;
    end


    initial begin
        $display("\nStart Testbench");

        clock = 1;
        reset = 1;


        $monitor("  %3d | num_dispatched: %d   b_mm_resolve: %d   b_mm_mispred: %d,   spots: %d     rs_reqs: %b         rs_valid: %b        rs_valid_next: %b   rs_data_issuing: %b   CDB_tags: %d %d %d        RS27.src2: %d   RS27.src2rdy: %b",
                  $time,  num_dispatched,      b_mm_resolve,      b_mm_mispred,       rs_spots,     rs_debug.rs_reqs,   rs_debug.rs_valid,  rs_valid_next,      rs_data_issuing,   CDB_tags[0], CDB_tags[1], CDB_tags[2], rs_data[27].Source2, rs_data[27].Source2_ready);
        @(negedge clock);
        @(negedge clock);
        reset = 0;
        
        // ---------- Test 0 ---------- //
        $display("\nTest 0: Add one entry and squash on next cycle");
        for(int i = 0; i < `N; ++i) begin 
            logic [$bits(RS_PACKET)-1:0] temp_rand;
            std::randomize(temp_rand); 
            rs_entries[i] = temp_rand;
            rs_entries[i].b_mask = 'd1;
        end 

        CDB_tags = '0;
        b_mm_mispred = '0;
        rs_data_issuing = '0;
        CDB_valid = '0;
        num_dispatched = 1;
        b_mm_resolve = '0;

        @(negedge clock);
        
        for(int i = 0; i < `N; ++i) begin  
            logic [$bits(RS_PACKET)-1:0] temp_rand;
            std::randomize(temp_rand); 
            rs_entries[i] = temp_rand;
            rs_entries[i].b_mask = 'd2;
        end 

        CDB_tags = '0;
        b_mm_mispred = '1;
        rs_data_issuing = '0;
        CDB_valid = '0;
        num_dispatched = 1;
        b_mm_resolve = 'd1;

        @(negedge clock);
        /*
        List of corner cases to test
        1. When RS is almost full
        2. When RS is full
        3. When RS is empty
        4. 
        

        1. Branch mispredict ( squash)
        2. Branch resolution (no mispredict)
        3. 



        */
        // ---------- Test 1 ---------- //
        $display("\nTest 1: Randomize many times");
        for (int k = 0; k <= 1000; ++k) begin
            std::randomize(rs_data_issuing);
            b_mm_resolve_idx = $urandom_range(0, `B_MASK_WIDTH);
            //std::randomize(b_mm_mispred);
            b_mm_mispred = (k % 10) == 0;
            std::randomize(CDB_valid);
            for(int i = 0; i < `N; ++i) begin
                logic [$bits(RS_PACKET)-1:0] temp_rand;
                logic [$bits(PHYS_REG_IDX)-1:0] temp_CDB_rand;
                std::randomize(temp_CDB_rand);
                std::randomize(temp_rand);
                CDB_tags[i] = temp_CDB_rand;
                rs_entries[i] = temp_rand;
            end
            rs_spots_random = $urandom_range(rs_spots);
            num_dispatched = b_mm_mispred ? 0 : rs_spots_random;
            b_mm_resolve = 1 << b_mm_resolve_idx;
            // $display("\n\033[32m@@@ Reached check #1\033[0m\n");
            // //randomizing rs_entry packets
            for(int i = 0; i < `N; ++i) begin  
                for(int j = 0; j < `N; ++j) begin
                    if(CDB_tags[j] == rs_entries[i].Source1) rs_entries[i].Source1_ready = '1;
                    if(CDB_tags[j] == rs_entries[i].Source2) rs_entries[i].Source2_ready = '1;
                end
                rs_entries[i].b_mask &= ~b_mm_resolve;
            end 
            $display("\n\033[32m@@@ Reached check #2\033[0m\n");
            @(negedge clock);
            $display("\n\033[32m@@@ Reached check #3\033[0m\n");
        end
        $display("\n\033[32m@@@ Passed\033[0m\n");

        $finish;
    end
endmodule
