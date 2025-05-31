`include "verilog/sys_defs.svh"

module branchpredictor #(
) (
    input   logic                                clock, 
    input   logic                                reset,

    // ------------- TO/FROM FETCH or BTB -------------- //
    input  ADDR                         [`N-1:0] PCs_out,
    input logic [`N-1:0]                [`N-1:0] branch_gnt_bus,
    input logic                         [`N-1:0] final_branch_gnt_line,
    input logic                                  no_branches_fetched,
    input logic                         [`N-1:0] btb_hits,
    output BRANCH_PREDICTOR_PACKET      [`N-1:0] bp_packets,
    output logic                        [`N-1:0] branches_taken,

    // ------------- TO/FROM BRANCH STACK -------------- //
    input BRANCH_PREDICTOR_PACKET                     bs_bp_packet,
    input logic                                       resolving_valid_branch,
    
    // ------------- TO/FROM EXECUTE (unpacked by CPU) -------------- //
    input logic                                       actual_taken,
    input logic                                       mispred

`ifdef DEBUG
    , output BP_DEBUG                                 bp_debug //define BP_DEBUG later sys defs
`endif
); 

    TWO_BIT_PREDICTOR   [`PHT_SZ-1:0] gshare_pht, next_gshare_pht;
    TWO_BIT_PREDICTOR   [`PHT_SZ-1:0] simple_pht, next_simple_pht;
    CHOOSER             [`PHT_SZ-1:0] meta_pht, next_meta_pht;
    BHR                               bhr, next_bhr;
    BHR                      [`N-1:0] intermediate_bhrs;
    BHR                      [`N-1:0] assigned_bhrs; // BHRS assigned to each branch inst

    // Assign each branch inst a bhr based on their relative positions to each other
    always_comb begin
        for (int i = 0; i < `N; ++i) begin
            intermediate_bhrs[i] = bhr << i;
        end

        assigned_bhrs = '0;
        for (int i = 0; i < `N; ++i) begin
            for(int j = 0; j < `N; ++j) begin
                if (branch_gnt_bus[j][i]) begin
                    assigned_bhrs[i] = intermediate_bhrs[j];
                end
            end
        end
    end

    // Figure out next_bhr based on which branch inst was fetched last
    // Do this by camming the branch gnt bus sent at the beginning of the cycle
    always_comb begin
        next_bhr = bhr;
        if (!no_branches_fetched) begin
            // $display("no_branches_fetched: %b", no_branches_fetched);
            // $display("final_branch_gnt_line: %b", final_branch_gnt_line);
            for(int j = 0; j < `N; ++j) begin
                if (branch_gnt_bus[j] == final_branch_gnt_line) begin
                    next_bhr = (assigned_bhrs[j] << 1) | branches_taken[j];
                end 
            end 
        end
    end

    // Update the PHTs, then assign branches a bp packet
    always_comb begin
        next_gshare_pht = gshare_pht;
        next_simple_pht = simple_pht;
        next_meta_pht = meta_pht;

        if (resolving_valid_branch) begin
            if ((^gshare_pht[bs_bp_packet.gshare_PHT_idx]) || (actual_taken != gshare_pht[bs_bp_packet.gshare_PHT_idx][0])) begin
                next_gshare_pht[bs_bp_packet.gshare_PHT_idx] += actual_taken ? 1 : -1;
            end

            if ((^simple_pht[bs_bp_packet.meta_PHT_idx]) || (actual_taken != simple_pht[bs_bp_packet.meta_PHT_idx][0])) begin
                next_simple_pht[bs_bp_packet.meta_PHT_idx] += actual_taken ? 1 : -1;
            end

            if ((^meta_pht[bs_bp_packet.meta_PHT_idx]) || 
                (((actual_taken == bs_bp_packet.gshare_predict_taken) - (actual_taken == bs_bp_packet.simple_predict_taken)) == 3) && meta_pht[bs_bp_packet.meta_PHT_idx] != 0 ||
                (((actual_taken == bs_bp_packet.gshare_predict_taken) - (actual_taken == bs_bp_packet.simple_predict_taken)) == 1) && meta_pht[bs_bp_packet.meta_PHT_idx] != 3) begin
                next_meta_pht[bs_bp_packet.meta_PHT_idx] += (actual_taken == bs_bp_packet.gshare_predict_taken) - (actual_taken == bs_bp_packet.simple_predict_taken);
            end 
        end 

        bp_packets = '0;
        for (int i = 0; i < `N; ++i) begin  
            bp_packets[i].gshare_predict_taken = next_gshare_pht[assigned_bhrs[i] ^ PCs_out[i][`HISTORY_BITS-1:0]][1];
            bp_packets[i].simple_predict_taken = next_simple_pht[PCs_out[i][`HISTORY_BITS-1:0]][1];
            bp_packets[i].meta_PHT_idx = PCs_out[i][`HISTORY_BITS-1:0];
            bp_packets[i].gshare_PHT_idx = PCs_out[i][`HISTORY_BITS-1:0] ^ assigned_bhrs[i];
            bp_packets[i].BHR_state = assigned_bhrs[i];
            branches_taken[i] = btb_hits[i] && (next_meta_pht[PCs_out[i][`HISTORY_BITS-1:0]][1] ? bp_packets[i].gshare_predict_taken : bp_packets[i].simple_predict_taken);
            // $display("Branches taken[%d]: %b", i, branches_taken[i]);
        end
    end

    always_ff @(posedge clock) begin
        if (reset) begin
            bhr <= '0;
            // meta_pht <= '0;
            // gshare_pht <= '0;
            // simple_pht <= '0;
            for (int i = 0; i < `PHT_SZ; ++i) begin
                simple_pht[i] <= 1'b1;
                gshare_pht[i] <= 2'b10;
                meta_pht[i] <= 1'b1;
            end
        end else begin
            bhr <= (resolving_valid_branch && mispred) ? ((bs_bp_packet.BHR_state << 1) | actual_taken) : next_bhr; 
            meta_pht <= next_meta_pht;
            gshare_pht <= next_gshare_pht;
            simple_pht <= next_simple_pht;
        end

        // if (resolving_valid_branch) begin
        //     $display("I'M RESOLVING!!!");
        // end

        // if (resolving_valid_branch && mispred) begin
        //     $display("I'M MISPREDICTED!!!");
        // end

        // for (int i = 0; i < `PHT_SZ; ++i) begin
        //     $display("next_meta_pht[%d]: %b", i, next_meta_pht[i]);
        // end

        // $display("bhr: %b", bhr);
        // for (int i = 0; i < `N; ++i) begin
        //     $display("next bhrs: %b", next_bhr);
        //     $display("intermediate bhrs[%d]: %b", i, intermediate_bhrs[i]);
        //     $display("assigned bhrs[%d]: %b", i, assigned_bhrs[i]);
        // end
        // $display("branches taken: %b", branches_taken);
        // $display("taken in branchPred: %b", actual_taken);
        // $display("mispred in branchPred: %b", mispred);
        // $display("bs_bp_packet.BHR_state: %b", bs_bp_packet.BHR_state);
        // if (resolving_valid_branch) begin
        //     $display("new next_gshare_pht[%d]: %b", bs_bp_packet.gshare_PHT_idx, next_gshare_pht[bs_bp_packet.gshare_PHT_idx]);
        //     $display("new next_simple_pht[%d]: %b", bs_bp_packet.meta_PHT_idx, next_simple_pht[bs_bp_packet.meta_PHT_idx]);
        //     $display("new next_meta_pht[%d]: %b", bs_bp_packet.meta_PHT_idx, next_meta_pht[bs_bp_packet.meta_PHT_idx]);
        // end

    end

`ifdef DEBUG
    assign bp_debug.place_holder = 0;
`endif


endmodule