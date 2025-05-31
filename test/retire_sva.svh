`include "verilog/sys_defs.svh"

module retire_sva #(
) (
    input  logic clock,
    input  logic reset,
    // ------------- TO/FROM ROB -------------- //
    input  ROB_PACKET      [`N-1:0] rob_outputs,                   // Coming from rob, to retrieve T_old from the packet, so that it can be retired
    input  logic  [`NUM_SCALAR_BITS-1:0] rob_outputs_valid,             // Coming from rob, to check which output is valid, only valid rob outputs can be retired
    input  logic  [`NUM_SCALAR_BITS-1:0] num_retiring,                  // Send to rob, how many rob_outputs can be retired
    // ------------- TO/FROM FREDDYLIST -------------- //
    input        [`PHYS_REG_SZ_R10K-1:0] complete_list_exposed,         // Coming from freddylist, to find out which rob_output is actually completed and ready to retire
    input  PHYS_REG_IDX         [`N-1:0] phys_regs_retiring
);

    logic  [`NUM_SCALAR_BITS-1:0] prev_num_retiring;
    PHYS_REG_IDX         [`N-1:0] prev_phys_regs_retiring;
    logic [`PHYS_REG_SZ_R10K-1:0] prev_complete_list_exposed;
    ROB_PACKET      [`N-1:0] prev_rob_outputs;
    task exit_on_error;
        begin
            $display("\n\033[31m@@@ Failed at time %4d\033[0m\n", $time);
            $finish;
        end
    endtask

    always_ff @(posedge clock) begin
        prev_num_retiring <= num_retiring;
        prev_phys_regs_retiring <= phys_regs_retiring;
        prev_rob_outputs <= rob_outputs;
    end

    clocking retire_prop @(posedge clock);
        property all_retiring_complete (int i);
            ((complete_list_exposed[0] === 0 || complete_list_exposed[0] === 1) && ~reset) |=> ((complete_list_exposed[rob_outputs[i].T_new]) || (i >= num_retiring));
        endproperty

        property check_break_works (int i);
            ((complete_list_exposed[0] === 0 || complete_list_exposed[0] === 1) && ~reset) |=> ((~complete_list_exposed[rob_outputs[i].T_new]) || (i != num_retiring) || (num_retiring == rob_outputs_valid)) ;
        endproperty

        property never_retiring_0 (int i);
            ((complete_list_exposed[0] === 0 || complete_list_exposed[0] === 1) && ~reset) |=> ((phys_regs_retiring[i] != 0) || (i >= num_retiring));
        endproperty

        property num_retiring_must_lt_rob_outputs_valid;
            ((complete_list_exposed[0] === 0 || complete_list_exposed[0] === 1) && ~reset) |=> (num_retiring <= rob_outputs_valid);
        endproperty
    endclocking
    

    genvar i;
    generate
    for(i = 0; i < `N; ++i) begin
        // always @(posedge clock) begin

        // Check for every retired rob_outputs, the T_new must be complete
            assert property (retire_prop.all_retiring_complete(i))
                else begin
                    $error("Rob_output at index %d retired but it hasn't been completed, reset: %b", 
                        i, reset);
                    $finish;
                end

        // Check if num_retiring is less than rob_outputs_valid, it must be due to next one being not complete
            assert property (retire_prop.check_break_works(i))
                else begin
                    $error("At index %d, rob_outputs should have retired (complete is high), but didn't, num_retiring: %d",
                        i, num_retiring);
                    $finish;
                end

            assert property (retire_prop.never_retiring_0(i))
                else begin
                    $error("Somehow, phys_reg_0 is retired at index %d",
                        i);
                    $finish;
                end
        //end
    end
    endgenerate

    always @(posedge clock) begin
        assert property (retire_prop.num_retiring_must_lt_rob_outputs_valid)
            else begin
                $error("num_retiring is greater than rob_outputs_valid");
                    $finish;
            end
    end

endmodule

