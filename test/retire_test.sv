`include "verilog/sys_defs.svh"
`include "test/retire_sva.svh"

`define DEBUG

module retire_test ();


    logic clock;
    logic reset;

    // ------------- TO/FROM ROB -------------- //
    ROB_PACKET      [`N-1:0] rob_outputs;                   // Coming from rob, to retrieve T_old from the packet, so that it can be retired
    logic  [`NUM_SCALAR_BITS-1:0] rob_outputs_valid;             // Coming from rob, to check which output is valid, only valid rob outputs can be retired
    logic  [`NUM_SCALAR_BITS-1:0] num_retiring;                  // Send to rob, how many rob_outputs can be retired

    // ------------- TO/FROM FREDDYLIST -------------- //
    logic        [`PHYS_REG_SZ_R10K-1:0] complete_list_exposed;         // Coming from freddylist, to find out which rob_output is actually completed and ready to retire
    PHYS_REG_IDX                [`N-1:0] phys_regs_retiring;             // Send to freddylist, which physical registers are being retired

    always begin
        #(`CLOCK_PERIOD/2) clock = ~clock;
    end

    retire dut (
        .rob_outputs(rob_outputs),                    
        .rob_outputs_valid(rob_outputs_valid),        
        .num_retiring(num_retiring),                  
        .complete_list_exposed(complete_list_exposed),
        .phys_regs_retiring(phys_regs_retiring)       
    );

    retire_sva dut_sva (
        .clock(clock),
        .reset(reset),
        .rob_outputs(rob_outputs),                    
        .rob_outputs_valid(rob_outputs_valid),        
        .num_retiring(num_retiring),                  
        .complete_list_exposed(complete_list_exposed),
        .phys_regs_retiring(phys_regs_retiring)       
    );

    task randomize_rob_output_has_dest (output ROB_PACKET [`N-1:0] rob_out);
        for(int i = 0; i < `N; ++i) begin
            rob_out[i].T_old = $urandom_range(`PHYS_REG_SZ_R10K-1, 1);
            rob_out[i].T_new = $urandom_range(`PHYS_REG_SZ_R10K-1, 1);
        end
    endtask

    task randomize_rob_output_hasorno_dest (output ROB_PACKET [`N-1:0] rob_out);
        for(int i = 0; i < `N; ++i) begin
            rob_out[i].T_old = $urandom_range(`PHYS_REG_SZ_R10K-1, 1);
            rob_out[i].T_new = $urandom_range(`PHYS_REG_SZ_R10K-1, 1);
        end
    endtask

    task randomize_complete_list (output [`PHYS_REG_SZ_R10K-1:0] cl_exposed);
        for(int i = 0; i < `PHYS_REG_SZ_R10K; ++i) begin
            cl_exposed[i] = $urandom_range(1,0);
        end
    endtask

    initial begin
        $display("\nStart Testbench");
        reset = 1;
        clock = 1;
        rob_outputs = 0;
        rob_outputs_valid = 0;
        complete_list_exposed = 0;

        $monitor("  %3d   |  rob_outputs_valid: %d  | rob_outputs[1].T_old: %d  | num_retiring: %d   |  phys_regs_retiring[1]: %d", 
                   $time, rob_outputs_valid, rob_outputs[1].T_old, num_retiring, phys_regs_retiring[1]);

        @(negedge clock);
        reset = 0;

        // ---------- Test 1 ---------- //
        $display("\nTest 1: rob_outputs_valid > 0, all complete");

        for(int i = 0; i < 10; ++i) begin
            complete_list_exposed = ~0;
            rob_outputs_valid = $urandom_range(`N, 1);
            randomize_rob_output_has_dest(rob_outputs);
            @(negedge clock);
        end

        // ---------- Test 2 ---------- //
        $display("\nTest 2: rob_outputs_valid > 0, not all complete");

        for(int i = 0; i < 100; ++i) begin
            randomize_complete_list(complete_list_exposed);
            rob_outputs_valid = $urandom_range(`N, 1);
            randomize_rob_output_has_dest(rob_outputs);
            @(negedge clock);
        end


        // ---------- Test 3 ---------- //
        $display("\nTest 3: rob_outputs_valid = 0, all complete");

        for(int i = 0; i < 10; ++i) begin
            complete_list_exposed = ~0;
            rob_outputs_valid = 0;
            randomize_rob_output_has_dest(rob_outputs);
            @(negedge clock);
        end

        // ---------- Test 4 ---------- //
        $display("\nTest 4: rob_outputs_valid > 0, has_dest = 0/1, should retire T_new");

        for(int i = 0; i < 100; ++i) begin
            complete_list_exposed = ~0;
            rob_outputs_valid = $urandom_range(`N, 1);
            randomize_rob_output_hasorno_dest(rob_outputs);
            @(negedge clock);
        end


        @(negedge clock);

        $display("\n\033[32m@@@ Passed\033[0m\n");
        $finish;
        
    end



endmodule