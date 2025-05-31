`include "verilog/sys_defs.svh"

module rs #(
) (
    input  logic                        clock, 
    input  logic                        reset,

    // ------ TO/FROM: DISPATCH ------- //
    input  logic [`NUM_SCALAR_BITS-1:0] num_dispatched,      // Number of input RS packets actually coming from dispatch
    input  RS_PACKET           [`N-1:0] rs_entries,          // Input RS packets data
    output logic [`NUM_SCALAR_BITS-1:0] rs_spots,            // Number of spots
    
    // --------- FROM: CDB ------------ //
    input  CDB_ETB_PACKET      [`N-1:0] ETB_tags,            // Tags that are broadcasted from the CDB
    
    // --------- FROM: STORE UNIT ------------ //
    input  SQ_MASK                      resolving_sq_mask,

    // ------- TO/FROM: ISSUE --------- //
    input  logic           [`RS_SZ-1:0] rs_data_issuing,      // bit vector of rs_data that is being issued by issue stage
    output RS_PACKET       [`RS_SZ-1:0] rs_data_next,        // The entire RS data 
    output logic           [`RS_SZ-1:0] rs_valid_issue,       // 1 if RS data is valid, seperate from next_rs_valid since it shouldn't include dispatched instructions

    // ------- FROM: BRANCH STACK --------- //
    input B_MASK_MASK                   b_mm_resolve,         // b_mask_mask to resolve
    input logic                         b_mm_mispred          // 1 if mispredict happens
    `ifdef DEBUG
        , output RS_DEBUG               rs_debug
    `endif
);

    RS_PACKET           [`RS_SZ-1:0] rs_data;        // 1 if RS data is valid <-- Coded
    RS_PACKET           [`RS_SZ-1:0] rs_data_next_next;
    logic [`RS_SZ-1:0] rs_valid, next_rs_valid;
    //TODO Need to handle corner case where RS_SZ is odd - maybe with genvar

    logic [`RS_NUM_ENTRIES_BITS-1:0] rs_num_available;
    logic [`N-1:0][`RS_SZ-1:0] rs_gnt_bus;
    logic [`RS_SZ-1:0] rs_reqs;
    assign rs_reqs = ~rs_valid;

    psel_gen #(
         .WIDTH(`RS_SZ),
         .REQS(`N)
    ) rs_psel (
         .req(rs_reqs),
         .gnt_bus(rs_gnt_bus)
    );

    //given the rs_valid bit array, this module counts 
    //how many valid entries are in the RS and 
    //how many spots are available
    CountOnes #(
        .WIDTH(`RS_SZ)
    ) RS_Counter (
        .bit_array(rs_reqs),
        .count_ones(rs_num_available)
    );

    always_comb begin

        rs_spots = rs_num_available > `N ? `N : rs_num_available;
        //B_mask camming
        rs_valid_issue = rs_valid;
        rs_data_next = rs_data;

        for(int i = 0; i < `RS_SZ; ++i) begin
            //resolving masks 
            rs_data_next[i].b_mask = rs_data[i].b_mask & ~(b_mm_resolve);
            rs_data_next[i].sq_mask = rs_data[i].sq_mask & ~(resolving_sq_mask);
        end
        for(int i = 0; i < `RS_SZ; ++i) begin
            //squashing step
            if (b_mm_mispred && (b_mm_resolve & rs_data[i].b_mask)) begin
                rs_valid_issue[i] =  '0;
                rs_data_next[i] = '0;
            end
        end

        //Cam logic
        for(int i = 0; i < `N; ++i) begin
            if(ETB_tags[i].valid) begin
                for(int j = 0; j < `RS_SZ; ++j)begin
                    if (rs_data_next[j].Source1 == ETB_tags[i].completing_reg) rs_data_next[j].Source1_ready = 1;
                    if (rs_data_next[j].Source2 == ETB_tags[i].completing_reg) rs_data_next[j].Source2_ready = 1;
                end
            end
        end
    end


    always_comb begin
        rs_data_next_next = rs_data_next;
        next_rs_valid = rs_valid_issue;
        //Maybe can make this more efficient by using wor/wand or smth
        for (int i = 0; i < `N; ++i) begin
            for(int j = 0; j < `RS_SZ; ++j) begin
                if (i < num_dispatched && rs_gnt_bus[i][j]) begin
                    rs_data_next_next[j] = rs_entries[i];
                    next_rs_valid[j] = 1;
                end else begin
                    if (rs_data_issuing[j]) begin
                        next_rs_valid[j] = 0;
                        rs_data_next_next[j] = 0;
                    end
                end
            end
        end
    end


    always_ff @(posedge clock) begin
        if (reset) begin
            rs_data <= '0;
            rs_valid <= '0;
        end else begin
            rs_data <= rs_data_next_next;
            rs_valid <= next_rs_valid;
        end
        // $display("------ RS --------");
        // $display("b_mm_mispred: %b", b_mm_mispred);
        // $display("b_mm_resolve: %b", b_mm_resolve);
        // for (int i = 0; i < `RS_SZ; ++i) begin
        //     $display("rs_data[%d].b_mask: %b", i, rs_data[i].b_mask);
        //     $display("rs_data_next[%d].sq_mask: %b", i, rs_data_next[i].sq_mask);
        // end
        // for (int i = 0; i < `N; ++i) begin
        //     $display("ETB_tags[%d].valid: %b", i, ETB_tags[i].valid);
        // end
    end

    always_comb begin
        // for (int i = 0; i < `RS_SZ; ++i) begin
        //     $display("rs_data[%d].Source1_ready: %b, rs_data[%d].Source2_ready: %b\n",
        //     i, rs_data[i].Source1_ready, i, rs_data[i].Source2_ready);
        // end
        // for (int i = 0; i < `RS_SZ; ++i) begin
        //     $display("rs_data[%d]: %b, rs_data[%d].Source2_ready: %b\n",
        //     i, rs_data[i].Source1_ready, i, rs_data[i].Source2_ready);
        // end
        // $display("rs_valid  : %b", rs_valid);

        // $display("------ RS --------");
        // $display("store_mask: %b", store_mask);
        // for (int i = 0; i < `RS_SZ; ++i) begin
        //     $display("rs_data_next[%d].sq_mask: %b", sq_packet.valid);
        // end

    end

`ifdef DEBUG
    assign rs_debug = {
        rs_valid:   rs_valid,
        rs_reqs:    rs_reqs
    };
`endif
endmodule