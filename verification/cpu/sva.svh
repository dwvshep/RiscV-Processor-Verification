// SystemVerilog Assertions (SVA) for use with our FIFO module
// This file is included by the testbench to separate our main module checking code
// SVA are relatively new to 470, feel free to use them in the final project if you like

module ROB_sva #(
) (
    input logic                        clock, 
    input logic                        reset,
    input ROB_PACKET          [`N-1:0] rob_inputs, // New instructions from Dispatch, MUST BE IN ORDER FROM OLDEST TO NEWEST INSTRUCTIONS
    input logic [`NUM_SCALAR_BITS-1:0] rob_inputs_valid, // To distinguish invalid instructions being passed in from Dispatch
    input logic [`NUM_SCALAR_BITS-1:0] rob_spots,
    input logic     [`ROB_SZ_BITS-1:0] rob_tail,
    input logic [`NUM_SCALAR_BITS-1:0] num_retiring, // Retire module tells the ROB how many entries can be cleared
    input ROB_PACKET          [`N-1:0] rob_outputs, // For retire to check eligibility
    input logic [`NUM_SCALAR_BITS-1:0] rob_outputs_valid, // If not all N rob entries are valid entries they should not be considered
    input logic                        tail_restore_valid,
    input logic     [`ROB_SZ_BITS-1:0] tail_restore,
    
    input ROB_DEBUG                    rob_debug
);

    int spots_manual;
    //update to include tail recovery logic
    assign spots_manual = rob_debug.head == rob_debug.rob_tail && rob_debug.rob_spots == 0 && rob_debug.rob_num_entries != 0
                            ? 0
                            : `ROB_SZ - ((rob_debug.rob_tail - rob_debug.head + `ROB_SZ) % `ROB_SZ) > `N 
                                ? `N
                                : `ROB_SZ - ((rob_debug.rob_tail - rob_debug.head + `ROB_SZ) % `ROB_SZ);

    logic [$bits(ROB_PACKET)-1:0] index;

    logic [`ROB_SZ_BITS-1:0] previous_tail_restore;

    always_ff @(posedge clock) begin
        if (reset) begin
            index <= 0;
            previous_tail_restore <= 0;
        end else begin
            index <= index + num_retiring;
            previous_tail_restore <= tail_restore;
        end
    end
    
    clocking cb @(posedge clock);
        property tail_recovery;
            (tail_restore_valid) |=> (rob_tail == previous_tail_restore);
        endproperty
    endclocking

    always @(posedge clock) begin

    // Check each valid output
        // for (int i = 0; i < rob_outputs_valid; i++) begin
        //     assert (reset || rob_outputs[i] == (i + index))
        //         else begin
        //             $error("Mismatch on rob_outputs[%0d]: expected %0d, got %0d", 
        //                 i,    (i + index),      rob_outputs[i]);
        //             $finish;
        //         end
        // end

        // Check overall conditions
        assert (reset || rob_debug.rob_spots == spots_manual)
            else begin
                $error("rob_debug.Spots (%0d) does not equal spots_manual (%0d)", 
                        rob_debug.rob_spots, spots_manual);
                $finish;
            end
        
        assert (reset || {1'b0, rob_inputs_valid} <= {1'b0, rob_spots})
            else begin
                $error("inputs_valid (%0d) exceeds spots (%0d)", 
                        rob_inputs_valid, rob_spots);
                $finish;
            end

        assert (reset || num_retiring <= rob_debug.rob_num_entries)
            else begin
                $error("num_retiring (%0d) exceeds num_entries (%0d)", 
                        num_retiring, rob_debug.rob_num_entries);
                $finish;
            end

        assert property (cb.tail_recovery)
            else begin 
                $error("Tail recovery failed: tail did not restore to checkpointed tail (%0d)", previous_tail_restore);
                $finish;
            end 
            
    end

endmodule

