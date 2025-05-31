`include "verilog/sys_defs.svh"

// // TODO!!!!!!!!!!!!: make sure that the block offset is accounted for when indexing into a btb set. Right now, we are only indexing the btb set with index 0

module btb #(
) (
    input   logic                                clock, 
    input   logic                                reset,

    // ------------- TO/FROM FETCH -------------- //
    input   ADDR                        [`N-1:0] PCs,
    output  ADDR                        [`N-1:0] target_PCs,
    output  logic                       [`N-1:0] btb_hits,


    // ------------- TO/FROM BRANCH STACK -------------- //
    input  logic                                 resolving_valid,
    input  ADDR                                  resolving_target_PC,
    input  ADDR                                  resolving_branch_PC
    //NOTE: This is not necessarily PC restore, this is whatever the target address is for a valid resolving branch
    
`ifdef DEBUG
    , output BTB_DEBUG                            btb_debug //define BP_DEBUG later sys defs
`endif
); 

    BTB_ENTRY [`BTB_NUM_SETS-1:0] [`BTB_NUM_WAYS-1:0] btb_entries, next_btb_entries;
    BTB_SET_IDX wr_btb_set_idx;
    BTB_TAG wr_btb_tag;
    
    assign wr_btb_set_idx = resolving_branch_PC.btb.set_idx;
    assign wr_btb_tag = resolving_branch_PC.btb.tag;

    logic found;

    generate
    genvar i;
    genvar j;

    for (i = 0; i < `BTB_NUM_SETS; ++i) begin
        logic [`BTB_NUM_WAYS-1:0] lru_gnt_line;
        logic [$clog2(`BTB_NUM_WAYS)-1:0] lru_idx;
        logic [$clog2(`BTB_NUM_WAYS)-1:0] victim_idx;
        logic [`BTB_NUM_WAYS-1:0] requests;

        for(j = 0; j < `BTB_NUM_WAYS; ++j) begin
            assign requests[j] = btb_entries[i][j].btb_lru == 0;
        end
        
        psel_gen #(
            .WIDTH(`BTB_NUM_WAYS),
            .REQS(1)
        ) lru_psel (
            .req(requests),
            .gnt(lru_gnt_line)
        );

        encoder #(`BTB_NUM_WAYS, $clog2(`BTB_NUM_WAYS)) lru_idx_encoder (lru_gnt_line, lru_idx);
        
        always_comb begin
            next_btb_entries[i] = btb_entries[i];
            if (resolving_valid && (i == wr_btb_set_idx)) begin
                victim_idx = lru_idx;
                for(int k = 0; k < `BTB_NUM_WAYS; k++) begin
                    if (btb_entries[i][k].btb_tag == wr_btb_tag) begin
                        victim_idx = k;
                    end
                end
                next_btb_entries[i][victim_idx].btb_tag = wr_btb_tag;
                next_btb_entries[i][victim_idx].target_PC = resolving_target_PC;
                next_btb_entries[i][victim_idx].btb_lru = `BTB_NUM_WAYS - 1'b1;
                next_btb_entries[i][victim_idx].valid = 1'b1;
                for (int l = 0; l < `BTB_NUM_WAYS; l++) begin
                    if (btb_entries[i][l].valid && (btb_entries[i][l].btb_lru > btb_entries[i][victim_idx].btb_lru)) begin
                        next_btb_entries[i][l].btb_lru--;
                    end
                end
            end

        end   
    end

    endgenerate

    BTB_SET_IDX [`N-1:0] rd_btb_set_idx;
    BTB_TAG [`N-1:0] rd_btb_tag;

    always_comb begin
        btb_hits = '0;
        target_PCs = '0;
        for(int i = 0; i < `N; i++) begin
            rd_btb_set_idx[i] = PCs[i].btb.set_idx;
            rd_btb_tag[i] = PCs[i].btb.tag;
            for(int j = 0; j < `BTB_NUM_WAYS; j++) begin
                if(next_btb_entries[rd_btb_set_idx[i]][j].valid && (next_btb_entries[rd_btb_set_idx[i]][j].btb_tag === rd_btb_tag[i])) begin
                    target_PCs[i] = next_btb_entries[rd_btb_set_idx[i]][j].target_PC;
                    btb_hits[i] = 1'b1;
                end
            end
        end
    end

    always_ff@(posedge clock) begin
        if(reset) begin
            btb_entries <= '0;
        end else begin
            btb_entries <= next_btb_entries;
            // $display("resolving_valid: %b", resolving_valid);
            // $display("resolving_branch_pc: %h", resolving_branch_PC);
            // for (int i = 0; i < `N; ++i) begin
            //     $display("target_pc[%d]: %h", i, target_PCs[i]);
            //     $display("btb_hits[%d]: %h", i, btb_hits[i]); 
            // end
            
        end
    end

`ifdef DEBUG
    assign btb_debug.place_holder_btb = 0;
`endif

endmodule

// `include "verilog/sys_defs.svh"

// // TODO!!!!!!!!!!!!: make sure that the block offset is accounted for when indexing into a btb set. Right now, we are only indexing the btb set with index 0

// module btb #(
// ) (
//     input   logic                                clock, 
//     input   logic                                reset,

//     // ------------- TO/FROM FETCH -------------- //
//     input   ADDR                        [`N-1:0] PCs,
//     output  ADDR                        [`N-1:0] target_PCs,
//     output  logic                       [`N-1:0] btb_hits,


//     // ------------- TO/FROM BRANCH STACK -------------- //
//     input  logic                                 resolving_valid,
//     input  ADDR                                  resolving_target_PC,
//     input  ADDR                                  resolving_branch_PC
//     //NOTE: This is not necessarily PC restore, this is whatever the target address is for a valid resolving branch

// `ifdef DEBUG
//     , output BTB_DEBUG                            btb_debug //define BP_DEBUG later sys defs
// `endif
// ); 

//     BTB_SET_PACKET [`BTB_NUM_SETS-1:0] btb_set_entries, next_btb_set_entries;
//     BTB_SET_IDX wr_btb_set_idx;
//     BTB_TAG wr_btb_tag;
    
//     assign wr_btb_set_idx = resolving_branch_PC.btb.set_idx;
//     assign wr_btb_tag = resolving_branch_PC.btb.tag;

//     logic found;

//     generate
//     genvar i;
//     genvar j;

//     for (i = 0; i < `BTB_NUM_SETS; ++i) begin
//         logic [`BTB_NUM_WAYS-1:0] lru_gnt_line;
//         logic [$clog2(`BTB_NUM_WAYS)-1:0] lru_idx;
//         logic [$clog2(`BTB_NUM_WAYS)-1:0] victim_idx;
//         logic [`BTB_NUM_WAYS-1:0] requests;

//         for(j = 0; j < `BTB_NUM_WAYS; ++j) begin
//             assign requests[j] = btb_set_entries[i].btb_entries[j].btb_lru == 0;
//         end
        
//         psel_gen #(
//             .WIDTH(`BTB_NUM_WAYS),
//             .REQS(1)
//         ) lru_psel (
//             .req(requests),
//             .gnt(lru_gnt_line)
//         );

//         encoder #(`BTB_NUM_WAYS, $clog2(`BTB_NUM_WAYS)) lru_idx_encoder (lru_gnt_line, lru_idx);
        
//         always_comb begin
//             next_btb_set_entries[i] = btb_set_entries[i];
//             if (resolving_valid && (i == wr_btb_set_idx)) begin
//                 victim_idx = lru_idx;
//                 for(int k = 0; k < `BTB_NUM_WAYS; k++) begin
//                     if (btb_set_entries[i].btb_entries[k].btb_tag == wr_btb_tag) begin
//                         victim_idx = k;
//                     end
//                 end
//                 next_btb_set_entries[i].btb_entries[victim_idx].btb_tag = wr_btb_tag;
//                 next_btb_set_entries[i].btb_entries[victim_idx].target_PC = resolving_target_PC;
//                 next_btb_set_entries[i].btb_entries[victim_idx].btb_lru = `BTB_NUM_WAYS - 1'b1;
//                 next_btb_set_entries[i].btb_entries[victim_idx].valid = 1'b1;
//                 for (int l = 0; l < `BTB_NUM_WAYS; l++) begin
//                     if (btb_set_entries[i].btb_entries[l].valid && (btb_set_entries[i].btb_entries[l].btb_lru > btb_set_entries[i].btb_entries[victim_idx].btb_lru)) begin
//                         next_btb_set_entries[i].btb_entries[l].btb_lru--;
//                     end
//                 end
//             end

//         end   
//     end

//     endgenerate

//     // always_comb begin
//     //     next_btb_set_entries = btb_set_entries;
//     //     found = '0;
//     //     if(resolving_valid) begin
//     //         for(int i = 0; i < `NUM_BTB_WAYS; i++) begin
//     //             if(btb_set_entries[wr_btb_set_idx].btb_entries[i].btb_tag == wr_btb_tag) begin
//     //                 found = 1'b1;
//     //                 next_btb_set_entries[wr_btb_set_idx].btb_entries[i].target_PC = resolving_target_PC;
//     //                 next_btb_set_entries[wr_btb_set_idx].btb_entries[i].valid = 1'b1;
//     //                 //update LRU
//     //                 next_btb_set_entries[wr_btb_set_idx].btb_entries[i].LRU = next_btb_set_entries[wr_btb_set_idx].num_entry - 1'b1;
//     //                 for(int j = 0; j < `NUM_BTB_WAYS; j++) begin
//     //                     if((btb_set_entries[wr_btb_set_idx].btb_entries[j].LRU > btb_set_entries[wr_btb_set_idx].btb_entries[i].LRU) 
//     //                                                                         && btb_set_entries[wr_btb_set_idx].btb_entries[j].valid) begin
//     //                         next_btb_set_entries[wr_btb_set_idx].btb_entries[j].LRU--;
//     //                     end
//     //                 end
//     //             end
//     //         end
//     //         // btb miss write 
//     //         if(~found) begin
            
//     //         next_btb_set_entries[wr_btb_set_idx].btb_entries[lru_idx[wr_btb_set_idx]]
            
            
            
            
//     //         //search for LRU
//     //             if (next_btb_set_entries[wr_btb_set_idx].num_entry == `NUM_BTB_WAYS) begin // if set is full
//     //                 for(int i = 0; i < `NUM_BTB_WAYS; i++) begin
//     //                     if((!btb_set_entries[wr_btb_set_idx].btb_entries[i].LRU)) begin
//     //                         next_btb_set_entries[wr_btb_set_idx].btb_entries[i].btb_tag = wr_btb_tag;
//     //                         next_btb_set_entries[wr_btb_set_idx].btb_entries[i].target_PC = resolving_target_PC;
//     //                         next_btb_set_entries[wr_btb_set_idx].btb_entries[i].valid = 1'b1;
//     //                         //update LRU
//     //                         next_btb_set_entries[wr_btb_set_idx].btb_entries[i].LRU = next_btb_set_entries[wr_btb_set_idx].num_entry - 1'b1;
//     //                         for(int j = 0; j < `NUM_BTB_WAYS; j++) begin
//     //                             if((j != i) && next_btb_set_entries[wr_btb_set_idx].btb_entries[j].valid) begin
//     //                                 next_btb_set_entries[wr_btb_set_idx].btb_entries[j].LRU--;
//     //                             end
//     //                         end
//     //                     end
//     //                 end
//     //             end else begin      // num_entry is not full
//     //                 for(int i = 0; i < `NUM_BTB_WAYS; i++) begin
//     //                     if(!btb_set_entries[wr_btb_set_idx].btb_entries[i].valid) begin
//     //                         next_btb_set_entries[wr_btb_set_idx].num_entry++;
//     //                         next_btb_set_entries[wr_btb_set_idx].btb_entries[i].btb_tag = wr_btb_tag;
//     //                         next_btb_set_entries[wr_btb_set_idx].btb_entries[i].target_PC = resolving_target_PC;
//     //                         next_btb_set_entries[wr_btb_set_idx].btb_entries[i].valid = 1'b1;
//     //                         //update LRU
//     //                         next_btb_set_entries[wr_btb_set_idx].btb_entries[i].LRU = next_btb_set_entries[wr_btb_set_idx].num_entry;
//     //                     end
//     //                 end
//     //             end    
//     //         end
//     //     end
//     // end

//     // Read BTB logic

//     BTB_SET_IDX [`N-1:0] rd_btb_set_idx;
//     BTB_TAG [`N-1:0] rd_btb_tag;

//     always_comb begin
//         btb_hits = '0;
//         target_PCs = '0;
//         for(int i = 0; i < `N; i++) begin
//             rd_btb_set_idx[i] = PCs[i].btb.set_idx;
//             rd_btb_tag[i] = PCs[i].btb.tag;
//             for(int j = 0; j < `BTB_NUM_WAYS; j++) begin
//                 if(next_btb_set_entries[rd_btb_set_idx[i]].btb_entries[j].btb_tag === rd_btb_tag[i]) begin
//                     target_PCs[i] = next_btb_set_entries[rd_btb_set_idx[i]].btb_entries[j].target_PC;
//                     btb_hits[i] = 1'b1;
//                 end
//             end
//         end
//     end

//     always_ff@(posedge clock) begin
//         if(reset) begin
//             btb_set_entries <= '0;
//         end else begin
//             btb_set_entries <= next_btb_set_entries;
//             $display("resolving_valid: %b", resolving_valid);
//             $display("resolving_branch_pc: %h", resolving_branch_PC);
//             for (int i = 0; i < `N; ++i) begin
//                 $display("target_pc[%d]: %h", i, target_PCs[i]);
//                 $display("btb_hits[%d]: %h", i, btb_hits[i]);
//             end
//         end
//     end

// `ifdef DEBUG
//     assign btb_debug.place_holder_btb = 0;
// `endif

// endmodule
