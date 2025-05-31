// FIFO module testbench
// This module generates the test vectors
// Correctness checking is in FIFO_sva.svh

`include "sys_defs.svh"
`include "FIFO_sva.svh"

module FIFO_test();

    localparam CNT_BITS = $clog2(`MAX_CNT+1);

    logic                clock, reset;
    logic                wr_en;
    logic   [`WIDTH-1:0] wr_data;
    logic                rd_en;
    logic   [`WIDTH-1:0] rd_data;
    logic                rd_valid;
    logic                wr_valid;
    logic [CNT_BITS-1:0] spots;
    logic                full;

    // variable to count values written to FIFO
    int cnt;

    // INSTANCE is from the sys_defs.svh file
    // it renames the module if SYNTH is defined in
    // order to rename the module to FIFO_svsim
    `INSTANCE(FIFO) #(
        .DEPTH(`DEPTH),
        .WIDTH(`WIDTH),
        .MAX_CNT(`MAX_CNT))
    dut (
        .clock    (clock),
        .reset    (reset),
        .wr_en    (wr_en),
        .wr_data  (wr_data),
        .rd_en    (rd_en),
        .rd_data  (rd_data),
        .rd_valid (rd_valid),
        .wr_valid (wr_valid),
        .spots    (spots),
        .full     (full)
    );

    bind dut FIFO_sva #(
        .DEPTH(`DEPTH),
        .WIDTH(`WIDTH),
        .MAX_CNT(`MAX_CNT)
    ) DUT_sva (.*);

    always begin
        #(`CLOCK_PERIOD/2) clock = ~clock;
    end

    // Generate random numbers for our write data on each cycle
    always @(negedge clock) begin
        std::randomize(wr_data);
    end

    initial begin
        $display("\nStart Testbench");

        clock = 1;
        reset = 1;
        wr_en = 0;
        rd_en = 0;

        $monitor("  %3d | d_in: %h   wr: %b  rd: %b  |  wr_vld: %b  rd_vld: %b   d_out: %h   full: %b  spots: %2d",
                  $time,  wr_data,   wr_en, rd_en,      wr_valid,  rd_valid,     rd_data,    full,     spots);

        @(negedge clock);
        @(negedge clock);
        reset = 0;

        // ---------- Test 1 ---------- //
        $display("\nTest 1: invalid read");
        rd_en = 1;
        @(negedge clock);
        rd_en = 0;

        // ---------- Test 2 ---------- //
        $display("\nTest 2: Write and read with one cycle wait");
        $display("Write 1 value");
        wr_en = 1;
        @(negedge clock);
        wr_en = 0;

        $display("Wait one cycle");
        @(negedge clock);

        rd_en = 1;
        $display("Read 1 value");
        @(negedge clock);
        rd_en = 0;

        // ---------- Test 3 ---------- //
        $display("\nTest 3: Write and read with no wait");
        $display("Write 1 value");
        wr_en = 1;
        @(negedge clock);
        wr_en = 0;

        rd_en = 1;
        $display("Read 1 value");
        @(negedge clock);
        rd_en = 0;

        // ---------- Test 4 ---------- //
        $display("\nTest 4: Read and write when empty");
        wr_en = 1;
        rd_en = 1;
        @(negedge clock);
        rd_en = 0;

        // ---------- Test 5 ---------- //
        $display("\nTest 5: Write 4 values");
        repeat (4) @(negedge clock);
        wr_en = 0;

        // ---------- Test 6 ---------- //
        $display("\nTest 6: Read 3 values");
        rd_en = 1;
        repeat (3) @(negedge clock);
        rd_en = 0;

        // ---------- Test 7 ---------- //
        $display("\nTest 7: Write until full");
        cnt = 1;
        wr_en = 1;
        while (!full) begin
            cnt++;
            @(negedge clock);
        end

        // ---------- Test 8 ---------- //
        $display("\nTest 8: Invalid write");
        @(negedge clock);

        // ---------- Test 9 ---------- //
        $display("\nTest 9: Simultaneous read and write when full");
        rd_en = 1;
        @(negedge clock);
        wr_en = 0;
        rd_en = 0;
        @(negedge clock);

        // ---------- Test 10 ---------- //
        $display("\nTest 10: Read and write when one less than full");
        rd_en = 1;
        $display("Read when full");
        @(negedge clock);
        $display("Read and write");
        wr_en = 1;
        @(negedge clock);
        wr_en = 0;
        rd_en = 0;
        @(negedge clock);

        // ---------- Test 11 ---------- //
        $display("\nTest 11: Read all values");
        rd_en = 1;
        while (cnt > 0) begin
            cnt--;
            @(negedge clock);
        end

        // ---------- Test 12 ---------- //
        $display("\nTest 12: Invalid read");
        @(negedge clock);
        rd_en = 0;

        // ---------- Test 13 ---------- //
        $display("\nTest 13: Four simultaneous reads and writes");
        rd_en = 1;
        wr_en = 1;
        repeat (4) @(negedge clock);
        wr_en = 0;

        // ---------- Test 14 ---------- //
        $display("\nTest 14: Read last item");
        @(negedge clock);
        rd_en = 0;

        @(negedge clock);
        @(negedge clock);

        $display("\n\033[32m@@@ Passed\033[0m\n");

        $finish;
    end

endmodule
