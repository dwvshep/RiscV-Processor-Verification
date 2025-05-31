// SystemVerilog Assertions (SVA) for use with our FIFO module
// This file is included by the testbench to separate our main module checking code
// SVA are relatively new to 470, feel free to use them in the final project if you like

`include "verilog/sys_defs.svh"

module RS_sva #(
) (
    input  logic                        clock, 
    input  logic                        reset,

    // ------ TO/FROM: DISPATCH ------- //
    input  logic [`NUM_SCALAR_BITS-1:0] num_dispatched,      // Number of input RS packets actually coming from dispatch
    input  RS_PACKET           [`N-1:0] rs_entries,          // Input RS packets data
    input  logic [`NUM_SCALAR_BITS-1:0] rs_spots,            // Number of spots <-- Coded       

    // --------- FROM: CDB ------------ //
    input  CDB_ETB_PACKET      [`N-1:0] ETB_tags,
    
    // ------- TO/FROM: ISSUE --------- //
    input  logic           [`RS_SZ-1:0] rs_data_issuing,      // bit vector of rs_data that is being issued by issue stage
    input  RS_PACKET       [`RS_SZ-1:0] rs_data,              // The entire RS data 
    input  logic           [`RS_SZ-1:0] rs_valid_next,        // 1 if RS data is valid <-- Coded

    // ------- FROM: EXECUTE (BRANCH) --------- //
    input B_MASK_MASK                   b_mm_resolve,         // b_mask_mask to resolve
    input logic                         b_mm_mispred,
    input RS_DEBUG                      rs_debug  
);
    genvar i;

    PHYS_REG_IDX        [`N-1:0] CDB_tags;
    logic               [`N-1:0] CDB_valid;
    generate
        for (i = 0; i < `N; ++i) begin
            assign CDB_tags[i] = ETB_tags[i].completing_reg;
            assign CDB_valid[i] = ETB_tags[i].valid;
        end
    endgenerate
    
    B_MASK_MASK  b_mm_resolve_prev;       
    logic        b_mm_mispred_prev;
    logic [`B_MASK_WIDTH-1:0] b_mask_temp;
    logic [`RS_NUM_ENTRIES_BITS-1:0] rs_spots_c;
    assign rs_spots_c = ($countones(rs_debug.rs_reqs) > `N) ? `N : $countones(rs_debug.rs_reqs);

    always_ff @(posedge clock) begin
        if (reset) begin
            b_mm_resolve_prev <= '0;         
            b_mm_mispred_prev <= 0;
        end else begin
            b_mm_resolve_prev <= b_mm_resolve;
            b_mm_mispred_prev <= b_mm_mispred;
        end
    end
    
    clocking cb @(posedge clock);
        property squashing(i);
            (b_mm_mispred && rs_debug.rs_valid[i] && (rs_data[i].b_mask & b_mm_resolve)) |-> (rs_valid_next[i] == 0);
        endproperty

        property cammingSrc1(i, j);
            (rs_debug.rs_valid[i] && CDB_valid[j] && (CDB_tags[j] == rs_data[i].Source1)) |=> (rs_data[i].Source1_ready);
        endproperty

        property cammingSrc2(i, j);
            (rs_debug.rs_valid[i] && CDB_valid[j] && (CDB_tags[j] == rs_data[i].Source2)) |=> (rs_data[i].Source2_ready);
        endproperty
    endclocking

    always @(posedge clock) begin
        //Check that rs_spots is properly calculated
        assert(reset || rs_spots == rs_spots_c)
            else begin
                $error("RS_spots (%0d) not equal to number of invalid entries (%0d).", 
                rs_spots, rs_spots_c);
                $finish;
            end

        //testing b_mask values after resolving (no mispred)
        //should be checking rs_data[i].b_mask
        for (int i = 0; i < `RS_SZ; ++ i) begin // for each RS entry
            if(rs_debug.rs_valid[i]) begin
                assert(reset || !(rs_data[i].b_mask & b_mm_resolve_prev))
                    else begin
                        $error("RS entry #%0d did not properly set b_mask idx to zero - Current B_mask(%0d) - Prev B_mask_mask(%0d).", 
                        i, rs_data[i].b_mask, b_mm_resolve_prev);
                        $finish;
                    end
            end
        end
        assert(reset || num_dispatched <= rs_spots)
            else begin
                $error("invalid number dispatching(%0d), greater than rs_spots(%0d)",
                num_dispatched, rs_spots);
                $finish;
            end
        assert(reset || num_dispatched <= `N)
            else begin
                $error("invalid number dispatching(%0d), greater than N(%0d)",
                num_dispatched, `N);
                $finish;
            end
    end

    generate
        for(i = 0; i < `RS_SZ; ++i) begin
            assert property (cb.squashing(i))
                else begin
                    $error("RS entry #%0d did not properly squash when it should have - Current B_mask(%0d) - b_mm_resolve(%0d).", 
                        i, rs_data[i].b_mask, b_mm_resolve_prev);
                    $finish;
                end
        end
    endgenerate
    generate
        genvar k, j;
            for(k = 0; k < `RS_SZ; ++k) begin
                for(j = 0; j < `N; ++j) begin
                    assert property (cb.cammingSrc1(k, j))
                        else begin
                            $error("RS entry #%0d did not properly match the cdb to src 1 when it should have - Current cdb idx(%0d) - RS entry src 1(%0d).", 
                            k, CDB_tags[j], rs_data[k].Source1);
                            $finish;
                        end
                    assert property (cb.cammingSrc2(k, j))
                        else begin
                            $error("RS entry #%0d did not properly match the cdb to src 2 when it should have - Current cdb idx(%0d) - RS entry src 2(%0d).", 
                            k, CDB_tags[j], rs_data[k].Source2);
                            $finish;
                        end
                end
            end
    endgenerate

endmodule

