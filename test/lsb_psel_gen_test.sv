module msb_psel_gen_tb;
    // Testbench parameters
    localparam WIDTH = 20;   // Width of request vector
    localparam REQS = 2;    // Number of requests to grant

    // Signals for the DUT
    logic [WIDTH-1:0] req;
    logic [WIDTH-1:0] r_req;
    logic [WIDTH-1:0] gnt;
    logic [WIDTH-1:0] exp_gnt;
    logic [REQS-1:0][WIDTH-1:0] gnt_bus, exp_gnt_bus;
    logic empty;

    // Instantiate the Device Under Test (DUT)
    lsb_psel_gen #(
        .WIDTH(WIDTH),
        .REQS(REQS)
    ) dut (
        .req(req),
        .gnt(gnt),
        .gnt_bus(gnt_bus),
        .empty(empty)
    );

    // Testbench variables
    int errors = 0;

    
    // generate expected gnt

    logic [3:0] cnt;

    always_comb begin
        cnt = 0;
        exp_gnt_bus = 0;
        for(int i = 0; i < WIDTH; i++) begin
            if(req[i] && cnt < REQS) begin
                exp_gnt_bus[cnt] = 0;
                exp_gnt_bus[cnt][i] = 1'b1;
                exp_gnt[i] = 1'b1;
                cnt++;
            end else begin
                exp_gnt[i] = 0;
            end
        end
    end


    // Test cases to check priority and grant mechanics
    task automatic check_priority_selector(
        input logic [WIDTH-1:0] test_req,
        input logic [WIDTH-1:0] expected_gnt,
        input string test_name
    );
        // Apply input
        req = test_req;
        #10; // Wait for combinational logic to settle

        // Check grant lines
        if (gnt !== expected_gnt) begin
            $display("ERROR in %s:", test_name);
            $display("  Input req:  %b", test_req);
            $display("  Expected gnt: %b", expected_gnt);
            $display("  Actual gnt:   %b", gnt);
            // $display("  Actual gnt_bus[0]:   %b", gnt_bus[0]);
            // $display("  Actual gnt_bus[1]:   %b", gnt_bus[1]);
            // $display("  Actual gnt_bus[2]:   %b", gnt_bus[2]);
            errors++;
        end

        for(int k = 0; k < REQS; k++) begin
            if(exp_gnt_bus[k] !== gnt_bus[k]) begin
                $display("ERROR in %s:", test_name);
                $display("  Input req:  %b", test_req);
                $display("  Expected gnt_bus[%d]: %b", k, exp_gnt_bus[k]);
                $display("  Actual gnt_bus[%d]: %b", k, gnt_bus[k]);
                errors++;
            end
        end
    endtask

    // Main test sequence
    initial begin

        for(int j = 0; j < 100; j++) begin
            req = $urandom;
            #10;
            check_priority_selector(
                req, 
                exp_gnt, 
                "Random testing"
            );
        end


        // Summary
        if (errors == 0)
            $display("\n\033[32m@@@ Passed\033[0m\n");
        else
            $display("@@@TEST FAILED: %0d errors found", errors);

        $finish;
    end
endmodule