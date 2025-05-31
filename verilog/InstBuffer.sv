 `include "verilog/sys_defs.svh"

module instbuffer #() (
    input   logic                        clock, 
    input   logic                        reset,

    // ------------ TO/FROM FETCH ------------- //
    input   FETCH_PACKET         [`N-1:0] inst_buffer_inputs,
    input   logic  [`NUM_SCALAR_BITS-1:0] inst_valid, //number of valid instructions fetch sends to instruction buffer     // New instructions from Dispatch, MUST BE IN ORDER FROM OLDEST TO NEWEST INSTRUCTIONS
    output  logic  [`NUM_SCALAR_BITS-1:0] inst_buffer_spots,

    // ------------ FROM BRANCH STACK ------------- //
    input   logic                         restore_valid,

    // ------------ TO/FROM DISPATCH or DECODER -------- //
    input   logic  [`NUM_SCALAR_BITS-1:0] num_dispatched,     //number of spots available in dispatch
    output  FETCH_PACKET         [`N-1:0] inst_buffer_outputs,   // For retire to check eligibility
    output  logic  [`NUM_SCALAR_BITS-1:0] inst_buffer_outputs_valid // If not all N FB entries are valid entries they should not be considered 
);

    FETCH_PACKET [`FB_SZ-1:0] inst_buffer;
    
    logic   [`FB_SZ_BITS-1:0] head, next_head;
    logic   [`FB_SZ_BITS-1:0] tail, next_tail;
    logic [$clog2(`FB_SZ + 1)-1:0] entries, next_entries;
    
    always_comb begin
        next_head = restore_valid ? tail : (head + num_dispatched) % `FB_SZ;
        next_tail = (tail + inst_valid) % `FB_SZ;
        next_entries = restore_valid ? inst_valid : entries + inst_valid - num_dispatched;
        inst_buffer_spots = restore_valid ? `N : ((`FB_SZ - entries < `N) ? `FB_SZ - entries : `N);
        inst_buffer_outputs_valid = (entries < `N) ? entries : `N;
        inst_buffer_outputs = '0;
        for (int i = 0; i < `N; ++i) begin
            if (i < inst_buffer_outputs_valid) begin
                inst_buffer_outputs[i] = inst_buffer[(head + i) % `FB_SZ];
            end
        end
    end

    always_ff @(posedge clock) begin
        if (reset) begin
            inst_buffer <= '0; 
            head <= 0;             // initial PC value is 0 (the memory address where our program starts)
            tail <= 0;
            entries <= '0;
        end else begin
            for (int i = 0; i < `N; ++i) begin
                if (i < inst_valid) begin
                    inst_buffer[(tail + i) % `FB_SZ] <= inst_buffer_inputs[i]; 
                end
            end  
            // $display("inst_buffer_outputs_valid: %d", inst_buffer_outputs_valid);
            // $display("entries: %d", entries);
            // $display("inst_buffer_head: %d", head);
            // $display("inst_buffer_tail: %d", tail);
            // for (int i = 0; i < `FB_SZ; ++i) begin
            //     $display("inst_buffer[%d].PC: %h", i, inst_buffer[i].PC);
            // end
            head <= next_head;
            tail <= next_tail;
            entries <= next_entries;
        end
    end
endmodule
