// ROB module testbench
// This module generates the test vectors
// Correctness checking is in FIFO_sva.svh

`include "verilog/sys_defs.svh"
`include "test/rob_sva.svh"

`define DEBUG

module ROB_test ();
    logic                        clock; 
    logic                        reset;
    ROB_PACKET          [`N-1:0] rob_inputs; // New instructions from Dispatch, MUST BE IN ORDER FROM OLDEST TO NEWEST INSTRUCTIONS
    logic [`NUM_SCALAR_BITS-1:0] rob_inputs_valid; // To distinguish invalid instructions being passed in from Dispatch
    logic [`NUM_SCALAR_BITS-1:0] rob_spots;
    logic     [`ROB_SZ_BITS-1:0] rob_tail;
    logic [`NUM_SCALAR_BITS-1:0] num_retiring; // Retire module tells the ROB how many entries can be cleared
    ROB_PACKET          [`N-1:0] rob_outputs; // For retire to check eligibility
    logic [`NUM_SCALAR_BITS-1:0] rob_outputs_valid; // If not all N rob entries are valid entries they should not be considered
    logic                        tail_restore_valid;
    logic     [`ROB_SZ_BITS-1:0] tail_restore;
    
    ROB_DEBUG                    rob_debug;

    logic [$bits(ROB_PACKET)-1:0] index;

    // INSTANCE is from the sys_defs.svh file
    // it renames the module if SYNTH is defined in
    // order to rename the module to FIFO_svsim
    rob dut (
        .clock             (clock),
        .reset             (reset),
        .rob_inputs        (rob_inputs),
        .rob_inputs_valid  (rob_inputs_valid), 
        .rob_spots         (rob_spots),
        .rob_tail          (rob_tail),
        .num_retiring      (num_retiring),
        .rob_outputs       (rob_outputs),
        .rob_outputs_valid (rob_outputs_valid),
        .tail_restore_valid(tail_restore_valid),
        .tail_restore      (tail_restore),
        .rob_debug         (rob_debug)
    );
    
    ROB_sva DUT_sva (
        .clock             (clock),
        .reset             (reset),
        .rob_inputs        (rob_inputs),
        .rob_inputs_valid  (rob_inputs_valid), 
        .rob_spots         (rob_spots),
        .rob_tail          (rob_tail),
        .num_retiring      (num_retiring),
        .rob_outputs       (rob_outputs),
        .rob_outputs_valid (rob_outputs_valid),
        .tail_restore_valid(tail_restore_valid),
        .tail_restore      (tail_restore),
        .rob_debug         (rob_debug)
    );
    
    always begin
        #(`CLOCK_PERIOD/2) clock = ~clock;
    end

    // logic [`N-1:0] [$bits(ROB_ENTRY_PACKET)-`PHYS_REG_ID_BITS-1:0] temp;
    logic [`N-1:0] [`PHYS_REG_ID_BITS - 1:0] T_new;
    //Generate random numbers for our write data on each cycle
    // always_ff @(negedge clock) begin
    //     //std::randomize(wr_data);
    //     for(int i = 0; i < `N; ++i) begin  
    //         temp[i] = '0;
    //     end
    // end

    always_ff @(posedge clock) begin
        if (reset) begin
            index <= 0;
        end else begin
            index <= index + rob_inputs_valid;
        end
    end

    always_comb begin : generateRobInputs 
        for(int i = 0; i < `N; ++i) begin
            // T_new[i] = (rob_debug.Tail + i)%DEPTH;
            // rob_inputs[i].T_new = {T_new[i], temp[i]}; 
            rob_inputs[i] = index + i; 
            // $display(" rob_inputs[%0d]: %0d, index %d",
            //       i,    (i + index),   rob_inputs[i], index);
        end
    end

    initial begin
        $display("\nStart Testbench");

        clock = 1;
        reset = 1;
        rob_inputs_valid = 0;
        num_retiring = 0;
        tail_restore = 0;
        tail_restore_valid = 0;

        $monitor("  %3d | inputs_valid: %d   outputs_valid: %d   num_retiring: %d,   spots: %d,   rob_head: %d,   tail: %d,   entries: %d",
                  $time,  rob_inputs_valid,      rob_outputs_valid,      num_retiring,       rob_spots,       rob_debug.head, rob_debug.rob_tail, rob_debug.rob_num_entries);

        // for (int Index = 0; Index < `N; ++Index) begin
        //     $monitor("Index: %b | rob_inputs: %b   rob_outputs: %b",
        //               Index,      rob_inputs[Index].T_new, rob_outputs[Index].T_new);
        // end

        @(negedge clock);
        @(negedge clock);
        reset = 0;

        // ---------- Test 1 ---------- //
        $display("\nTest 1: Add/Retire 1 entry to/from the ROB");
        $display("Add 1 entry to the ROB");
        rob_inputs_valid = 1;
        @(negedge clock);
        rob_inputs_valid = 0;

        @(negedge clock);

        $display("Retire 1 entry from the ROB");
        num_retiring = 1;
        @(negedge clock);
        num_retiring = 0;

        @(negedge clock);
        
        // ---------- Test 2 ---------- //
        $display("\nTest 2: Add/Retire N entries to/from ROB");

        rob_inputs_valid = `N;
        @(negedge clock);
        rob_inputs_valid = 0;
        
        @(negedge clock);

        num_retiring = `N;
        @(negedge clock);
        num_retiring = 0;

        // ---------- Test 3 ---------- //
        $display("\nTest 3: Simultaneuos Write and Retire");
        $display("Start with N Entries");
        rob_inputs_valid = `N;
        @(negedge clock);
        rob_inputs_valid = 0;

        $display("Write and Retire 1 values");
        rob_inputs_valid = 1;
        num_retiring = 1;
        @(negedge clock);
        rob_inputs_valid = 0;
        num_retiring = 0;
        @(negedge clock);

        $display("Write and Retire N values");
        rob_inputs_valid = `N;
        num_retiring = `N;
        @(negedge clock);
        rob_inputs_valid = 0;
        num_retiring = 0;
        @(negedge clock);

        // ---------- Test 4 ---------- //
        $display("\nTest 4: Write until full");

        while (rob_spots) begin // checking spots > 0
           rob_inputs_valid = rob_spots;
           @(negedge clock);
        end

        // ---------- Test 5 ---------- //
        $display("\nTest 5: Simultaneous Write and Retire when full");
        $display("Write and Retire 1");
        rob_inputs_valid = 1;
        num_retiring = 1;
        @(negedge clock);
        rob_inputs_valid = 0;
        num_retiring = 0;

        $display("Write and Retire N");
        rob_inputs_valid = `N;
        num_retiring = `N;
        @(negedge clock); 
        rob_inputs_valid = 0;
        num_retiring = 0;

        // ---------- Test 6 ---------- //
        $display("\nTest 6: Simultaneous Write and Retire when one less than Full");
        $display("Retire 1");
        num_retiring = 1;
        @(negedge clock);
        num_retiring = 0;

        $display("Write and Retire 1");
        rob_inputs_valid = 1;
        num_retiring = 1;
        @(negedge clock);
        rob_inputs_valid = 0;
        num_retiring = 0;

        $display("Write and Retire N");
        rob_inputs_valid = `N;
        num_retiring = `N;
        @(negedge clock);
        rob_inputs_valid = 0;
        num_retiring = 0;

        // ---------- Test 7 ---------- //
        $display("\nTest 7: Retire until Empty");
        while (rob_outputs_valid) begin // checking spots > 0
           num_retiring = rob_outputs_valid;
           @(negedge clock);
           num_retiring = 0;
        end

        // ---------- Test 8 ---------- //
        $display("\nTest 8: Write and Retire randon number of values");
        @(negedge clock);
        for (int i=0; i <= 100; ++i) begin
            for (int j=0; j <= 100; ++j) begin
                rob_inputs_valid = $urandom_range(rob_spots); 
                num_retiring = $urandom_range(rob_outputs_valid);
                @(negedge clock);
                rob_inputs_valid = 0;
                num_retiring = 0;
            end
        end

        // ---------- Test 9 ---------- //
        $display("\nTest 9a: Tail Restore With Full ROB to same tail (Branch is at current tail)");
        @(negedge clock);
        //fill the rob
        while (rob_spots) begin // checking spots > 0
            rob_inputs_valid = rob_spots;
            num_retiring = 0;
            @(negedge clock);
        end
        rob_inputs_valid = 0;
        num_retiring = 0;
        tail_restore_valid = 1;
        tail_restore = rob_tail;
        
        
        $display("\nTest 9b: Tail Restore With Full ROB to older tail");
        @(negedge clock);
        rob_inputs_valid = 0;
        num_retiring = 1;
        tail_restore_valid = 1;
        tail_restore = (rob_tail == 0) ? '1 : (rob_tail - 1);

        $display("\n\033[32m@@@ Passed\033[0m\n");

        $finish;
    end
endmodule
