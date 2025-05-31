`include "verilog/sys_defs.svh"

module rob #(
) (
    input   logic                        clock, 
    input   logic                        reset,

    // ------------ TO/FROM DISPATCH ------------- //
    input   ROB_PACKET           [`N-1:0] rob_inputs,        // New instructions from Dispatch, MUST BE IN ORDER FROM OLDEST TO NEWEST INSTRUCTIONS
    input   logic  [`NUM_SCALAR_BITS-1:0] rob_inputs_valid,  // To distinguish invalid instructions being passed in from Dispatch (A number, NOT one hot)
    output  logic  [`NUM_SCALAR_BITS-1:0] rob_spots,         //number of spots available, saturated at N
    output  logic      [`ROB_SZ_BITS-1:0] rob_tail,

    // ------------- TO/FROM RETIRE -------------- //
    input   logic  [`NUM_SCALAR_BITS-1:0] num_retiring,      // Retire module tells the ROB how many entries can be cleared
    output  ROB_PACKET           [`N-1:0] rob_outputs,       // For retire to check eligibility
    output  logic  [`NUM_SCALAR_BITS-1:0] rob_outputs_valid, // If not all N rob entries are valid entries they should not be considered

    // ------------- FROM BRANCH STACK -------------- //
    input   logic                         tail_restore_valid,
    input   logic      [`ROB_SZ_BITS-1:0] tail_restore
`ifdef DEBUG
    , output  ROB_DEBUG                   rob_debug
`endif
); 

    // Main ROB Data Here
    ROB_PACKET    [`ROB_SZ-1:0] rob_entries;

    logic          [`ROB_SZ_BITS-1:0] head, next_head;
    logic          [`ROB_SZ_BITS-1:0] next_tail;
    logic [`ROB_NUM_ENTRIES_BITS-1:0] entries, next_entries;

    always_comb begin
        next_head = (head + num_retiring) % `ROB_SZ;
        next_tail = tail_restore_valid ? tail_restore : (rob_tail + rob_inputs_valid) % `ROB_SZ;
        next_entries = entries + rob_inputs_valid - num_retiring;
        rob_spots = (`ROB_SZ - entries < `N) ? `ROB_SZ - entries : `N;
        rob_outputs_valid = (entries < `N) ? entries : `N;
        rob_outputs = '0;
        for (int i = 0; i < `N; ++i) begin
            if (i < rob_outputs_valid) begin
                rob_outputs[i] = rob_entries[(head + i) % `ROB_SZ];
            end
        end
    end

    always_ff @(posedge clock) begin
        if (reset) begin
            rob_entries <= '0;
            head <= 0;
            rob_tail <= 0;
            entries <= 0;
        end else if(tail_restore_valid) begin
            head <= next_head;
            rob_tail <= tail_restore;
            entries <= (tail_restore == next_head) ? `ROB_SZ : (tail_restore - next_head + `ROB_SZ) % `ROB_SZ;
        end else begin
            for (int i = 0; i < `N; ++i) begin
                if (i < rob_inputs_valid) begin
                    rob_entries[(rob_tail + i) % `ROB_SZ] <= rob_inputs[i]; 
                end
            end
            head <= next_head;
            rob_tail <= next_tail;
            entries <= next_entries;
        end
        // $display("rob_entries: %d\nrob_head: %d\nrob_tail: %d", entries, head, rob_tail);
    end

// Debug signals
`ifdef DEBUG
    assign rob_debug = {
        rob_inputs:         rob_entries,
        head:               head,
        rob_tail:           rob_tail,
        rob_spots:          rob_spots,
        rob_outputs_valid:  rob_outputs_valid,
        rob_outputs:        rob_outputs,
        rob_num_entries:    entries
    };
`endif

endmodule