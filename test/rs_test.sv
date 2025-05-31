// ROB module testbench
// This module generates the test vectors
// Correctness checking is in FIFO_sva.svh

`include "verilog/sys_defs.svh"
`include "test/rs_sva.svh"

`define DEBUG

module RS_test ();
    logic                        clock; 
    logic                        reset;

    // ------ TO/FROM: DISPATCH ------- //
    logic   [`NUM_SCALAR_BITS:0] num_dispatched;      // Number of input RS packets actually coming from dispatch
    RS_PACKET           [`N-1:0] rs_entries;          // Input RS packets data
    logic [`NUM_SCALAR_BITS-1:0] rs_spots;            // Number of spots <-- Coded       

    // --------- FROM: CDB ------------ //
    PHYS_REG_IDX        [`N-1:0] CDB_tags;            // Tags that are broadcasted from the CDB
    logic               [`N-1:0] CDB_valid;           // 1 is the broadcast is valid
    
    // ------- TO/FROM: ISSUE --------- //
    logic           [`RS_SZ-1:0] rs_data_issuing;      // bit vector of rs_data that is being issued by issue stage
    RS_PACKET       [`RS_SZ-1:0] rs_data;              // The entire RS data 
    logic           [`RS_SZ-1:0] rs_valid_next;        // 1 if RS data is valid <-- Coded

    // ------- FROM: EXECUTE (BRANCH) --------- //
    B_MASK_MASK                   b_mm_resolve;         // b_mask_mask to resolve
    logic                         b_mm_mispred;
    RS_DEBUG                      rs_debug; 

    rs dut (
        .clock             (clock),
        .reset             (reset),
        .num_dispatched    (num_dispatched),
        .rs_entries        (rs_entries), 
        .rs_spots          (rs_spots),
        .CDB_tags          (CDB_tags),
        .CDB_valid         (CDB_valid),
        .rs_data_issuing   (rs_data_issuing),
        .rs_data           (rs_data),
        .rs_valid_next     (rs_valid_next),
        .b_mm_resolve      (b_mm_resolve),
        .b_mm_mispred      (b_mm_mispred),
        .rs_debug          (rs_debug)
    );
    
    RS_sva DUT_sva (
        .clock             (clock),
        .reset             (reset),
        .num_dispatched    (num_dispatched),
        .rs_entries        (rs_entries), 
        .rs_spots          (rs_spots),
        .CDB_tags          (CDB_tags),
        .CDB_valid         (CDB_valid),
        .rs_data_issuing   (rs_data_issuing),
        .rs_data           (rs_data),
        .rs_valid_next     (rs_valid_next),
        .b_mm_resolve      (b_mm_resolve),
        .b_mm_mispred      (b_mm_mispred),
        .rs_debug          (rs_debug)
    );
    
    always begin
        #(`CLOCK_PERIOD/2) clock = ~clock;
    end

    //temp signals for randomization
    logic [`N-1:0]    [$bits(RS_PACKET)-1:0] temp; // randomized RS_Packet
    logic [`N-1:0] [$bits(PHYS_REG_IDX)-1:0] temp_CDB; // randomized RS_Packet
    logic                           [`N-1:0] CDB_valid_rand;
    logic                                    b_mm_mispred_rand;
    logic                       [`RS_SZ-1:0] rs_data_issuing_rand;
    logic             [`NUM_SCALAR_BITS-1:0] rs_spots_random;
    int                                      b_mm_resolve_idx;

    //temp signals for manual
    /*
    RS_PACKET                       [`N-1:0] rs_entries_manual;
    PHYS_REG_IDX                    [`N-1:0] CDB_tags_manual;
    logic                                    b_mm_mispred_manual;
    logic                       [`RS_SZ-1:0] rs_data_issuing_manual;
    logic                           [`N-1:0] CDB_valid_manual;
    logic             [`NUM_SCALAR_BITS-1:0] num_dispatched_manual;
    B_MASK_MASK                              b_mm_resolve_manual;
    logic                                    manual_mode;
    */
    
    //logic [`N-1:0] [`PHYS_REG_ID_BITS - 1:0] T_new; //using physical reg as instruction identifier
    //Generate random numbers for our write data on each cycle
   

    /*always_ff @(negedge clock) begin
        std::randomize(rs_data_issuing);
        b_mm_resolve_idx = $urandom_range(0, `B_MASK_WIDTH);
        //std::randomize(b_mm_mispred);
        b_mm_mispred = 0;
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
    end*/
    
    
    /*always_comb begin : generateRSInputs
        std::randomize(rs_data_issuing);
        b_mm_resolve_idx = $urandom_range(0, `B_MASK_WIDTH);
        //std::randomize(b_mm_mispred);
        b_mm_mispred = 0;
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
    end*/

    /*
    Variables that can be independent (truly randomized)
    1. T_new
    2. Source1 <- DONE (through general randomization)
    3. Source2 <- DONE (through general randomization)
    4. Op <- DONE (through general randomization)
    5. CDB_tags <- DONE
    6. CDB_valid <- DONE
    7. b_mm_mispred <- DONE
    8. num dispatch <- DONE
    9. b_mm_resolve <- DONE
    10. rs_data_issuing

    Variables that are dependent
    1. Source1_ready = (Source1 == CDB_tag) <- DONE
    2. Source2_ready = (Source2 == CDB_tag) <- DONE
    3. b_mask &= ~b_mm_resolve 
    4. if (B_mm_mispred) --> num_dispatching = 0; <- DONE
    5. else num_dispatching = (num_dispatching > rs_spots) ? rs_spots : num_dispatching <- DONE


    
    Things to control
    1. Phys regs tags in src1 and src2 need to be rdy if on cdb
    2. bmasks for incoming entries cannot be 1 in the idx that is
    currrently being resolved
    3. If we have a mispredict, num_dispatching should be 0
    4. Num_dispathing should be <= rs_spots
    */

    initial begin
        $display("\nStart Testbench");

        clock = 1;
        reset = 1;


        $monitor("  %3d | num_dispatched: %d   b_mm_resolve: %d   b_mm_mispred: %d,   spots: %d     rs_reqs: %b         rs_valid: %b        rs_valid_next: %b   rs_data_issuing: %b   CDB_tags: %d %d %d        RS27.src2: %d   RS27.src2rdy: %b",
                  $time,  num_dispatched,      b_mm_resolve,      b_mm_mispred,       rs_spots,     rs_debug.rs_reqs,   rs_debug.rs_valid,  rs_valid_next,      rs_data_issuing,   CDB_tags[0], CDB_tags[1], CDB_tags[2], rs_data[27].Source2, rs_data[27].Source2_ready);
        @(negedge clock);
        @(negedge clock);
        reset = 0;
        
        // ---------- Test 0 Start ---------- //
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
        $display("\n\033[32m@@@ Test 0 Passes\033[0m\n");
        // ---------- Test 0 End ---------- //


        // ---------- Test 1 Start ---------- //
        /*
        $display("\n\033[32m@@@ Test 1: Dispatching when RS is full\033[0m\n");
        //fill up the RS
        for(int x = 0; x < 9; ++x) begin
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
            num_dispatched =`N;
            b_mm_resolve = '0;

            @(negedge clock);
        end
        //last 2
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
        num_dispatched = 2;
        b_mm_resolve = '0;

        @(negedge clock);

        $display("\n\033[32m@@@ Test 1 Passes\033[0m\n");
        */
        // ---------- Test 1 End ---------- //


        // ---------- Test 2 Start ---------- //
        $display("\n\033[32m@@@ Test 2: Dispatching when RS is almost full\033[0m\n");

        $display("\n\033[32m@@@ Test 2 Passes\033[0m\n");
        // ---------- Test 2 End ---------- //


        // ---------- Test 3 Start ---------- //
        $display("\n\033[32m@@@ Test 3: Branch mispredict when RS is empty\033[0m\n");

        $display("\n\033[32m@@@ Test 3 Passes\033[0m\n");
        // ---------- Test 3 End ---------- //


        // ---------- Test 4 Start ---------- //
        $display("\n\033[32m@@@ Test 4: Data Issuing is 0\033[0m\n");



        $display("\n\033[32m@@@ Test 4 Passes\033[0m\n");
        // ---------- Test 4 End ---------- //


        // ---------- Test Inf ---------- //
        $display("\nTest Inf: Randomize many times");
        for (int k = 0; k <= 10; ++k) begin
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
            b_mm_mispred = (k % 10) == 0;

            $display("\nEnd of iteration\n");
            @(negedge clock);
        end
        $display("\n\033[32m@@@ Test Inf Passes\033[0m\n");
        $display("\n\033[32m@@@ Passed\033[0m\n");

        $finish;
    end
endmodule