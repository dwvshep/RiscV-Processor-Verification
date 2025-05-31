`include "verilog/sys_defs.svh"

module Dispatch (
    input   logic                               clock,
    input   logic                               reset,

    // ------------ FROM INST BUFFER ------------- //
    input   logic        [`NUM_SCALAR_BITS-1:0] inst_buffer_instructions_valid,

    // ------------ FROM DECODER ------------- //
    input   DECODE_PACKET              [`N-1:0] decoder_out,
    input   logic                      [`N-1:0] is_rs1_used,
    input   logic                      [`N-1:0] is_rs2_used,
    input   ARCH_REG_IDX               [`N-1:0] source1_arch_reg,
    input   ARCH_REG_IDX               [`N-1:0] source2_arch_reg,
    input   ARCH_REG_IDX               [`N-1:0] dest_arch_reg,

    // ------------ TO/FROM BRANCH STACK ------------- //
    input  PHYS_REG_IDX [`ARCH_REG_SZ_R10K-1:0] map_table_restore,
    input   logic                               restore_valid,
    input   B_MASK                              b_mask_combinational,
    output  BS_ENTRY_PACKET [`B_MASK_WIDTH-1:0] branch_stack_entries,
    output  B_MASK                              next_b_mask,

    // ------------ TO/FROM ROB ------------- //
    input   logic            [`ROB_SZ_BITS-1:0] rob_tail,
    input   logic        [`NUM_SCALAR_BITS-1:0] rob_spots,
    output  ROB_PACKET                 [`N-1:0] rob_entries,

    // ------------ TO/FROM RS ------------- // 
    input   logic        [`NUM_SCALAR_BITS-1:0] rs_spots,
    output  RS_PACKET                  [`N-1:0] rs_entries,

    // ------------ TO/FROM SQ ------------- // 
    input   logic            [`NUM_SQ_BITS-1:0] sq_spots,
    input   SQ_POINTER                          sq_tail,
    input   SQ_MASK                             sq_mask_combinational,
    output  SQ_MASK                             dispatch_sq_mask,
    output  logic        [`NUM_SCALAR_BITS-1:0] stores_dispatching,

    // ------------ TO/FROM FREDDY LIST ------------- //
    //input   logic        [`NUM_SCALAR_BITS-1:0] num_regs_available,
    input   logic       [`PHYS_REG_SZ_R10K-1:0] next_complete_list,
    input   PHYS_REG_IDX               [`N-1:0] regs_to_use,
    input   logic       [`PHYS_REG_SZ_R10K-1:0] free_list_copy,
    output  logic       [`PHYS_REG_SZ_R10K-1:0] updated_free_list,
    
    // ------------ FROM ISSUE? ------------- //
    //input   logic        [`NUM_SCALAR_BITS-1:0] num_issuing,

    // ------------ FROM EXECUTE ------------- //
    input   CDB_ETB_PACKET             [`N-1:0] cdb_completing,

    // ------------ TO ALL DATA STRUCTURES ------------- //
    output   logic       [`NUM_SCALAR_BITS-1:0] num_dispatched
    `ifdef DEBUG
        , output DISPATCH_DEBUG                 dispatch_debug
    `endif
);

    PHYS_REG_IDX [`ARCH_REG_SZ_R10K-1:0] map_table, next_map_table;

    // PHYS_REG_IDX [`N:0] [`ARCH_REG_SZ_R10K-1:0] next_map_table;
    // assign next_map_table[0] = map_table;

    logic [`NUM_SCALAR_BITS-1:0] i_num_dispatched;

    logic [`NUM_SCALAR_BITS-1:0] min;           // min (rs_spots +num_issuing, rob_spots, instruction valid)

    //TODO: need to update this to account for store queue structural hazards
    assign min = ((rs_spots <= rob_spots) && (rs_spots <= inst_buffer_instructions_valid)) ? (rs_spots) :
                                ((rob_spots <= rs_spots) && (rob_spots <= inst_buffer_instructions_valid)) ? rob_spots : inst_buffer_instructions_valid;

    logic [`B_MASK_ID_BITS-1:0] empty_bs_index;

    parameter MIN_BRANCH_WIDTH_N = (`B_MASK_WIDTH < `N) ? `B_MASK_WIDTH : `N;

    logic [MIN_BRANCH_WIDTH_N-1:0] [`B_MASK_WIDTH-1:0] b_mask_chosen_spots;
    logic [`NUM_B_MASK_BITS-1:0] branches_dispatching;
    SQ_POINTER sq_tail_combinational;

    psel_gen #(
         .WIDTH(`B_MASK_WIDTH),  // The width of the request bus
         .REQS(MIN_BRANCH_WIDTH_N) // The number of requests that can be simultaenously granted
    ) psel_inst (
         .req(~b_mask_combinational), // Input request bus
         .gnt_bus(b_mask_chosen_spots)  // Output bus for each request
    );

    assign i_num_dispatched = restore_valid ? 0 : min; //if not restoring, num_dispatching = min (rs_entries, rob_entries, free_list)


    always_comb begin
        branch_stack_entries = '0;
        dispatch_sq_mask = sq_mask_combinational;
        sq_tail_combinational = sq_tail;
        next_b_mask = b_mask_combinational;
        num_dispatched = '0;
        next_map_table = map_table;
        updated_free_list = free_list_copy;
        rs_entries = '0;
        rob_entries = '0;
        branches_dispatching = 0;
        stores_dispatching = 0;
        for (int i = 0; i < `N; ++i) begin
            // next_map_table[i+1] = next_map_table[i];             // Create rob/rs/branch-stack entries
            if (i < i_num_dispatched) begin
                rs_entries[i].decoded_signals = decoder_out[i];
                rs_entries[i].T_new = regs_to_use[i];
                rs_entries[i].Source1 = next_map_table[source1_arch_reg[i]];
                rs_entries[i].sq_tail = sq_tail_combinational;

                if (!is_rs1_used[i] || next_complete_list[rs_entries[i].Source1]) begin
                    rs_entries[i].Source1_ready = 1'b1; 
                end else begin
                    for (int j = 0; j < `N; j++) begin
                        if (rs_entries[i].Source1 == cdb_completing[j].completing_reg && cdb_completing[j].valid)begin
                            rs_entries[i].Source1_ready = 1'b1;
                        end
                    end
                end

                rs_entries[i].Source2 = next_map_table[source2_arch_reg[i]];
                if (!is_rs2_used[i] || next_complete_list[rs_entries[i].Source2]) begin
                    rs_entries[i].Source2_ready = 1'b1; 
                end else begin
                    for(int j = 0; j < `N; j++) begin
                        if(rs_entries[i].Source2 == cdb_completing[j].completing_reg && cdb_completing[j].valid)begin
                            rs_entries[i].Source2_ready = 1'b1;
                        end
                    end
                end

                rs_entries[i].b_mask = next_b_mask;

                //Create ROB Packet
                /*
                    PHYS_REG_IDX    T_new; // Use as unique rob id
                    PHYS_REG_IDX    T_old;
                    ARCH_REG_IDX    Arch_reg;
                */
                rob_entries[i].T_new = regs_to_use[i];                          //this should be the output from freddy
                rob_entries[i].halt = decoder_out[i].halt;
                rob_entries[i].arch_reg = decoder_out[i].has_dest ? dest_arch_reg[i] : 0;         //this should come from instruction dest_reg
                rob_entries[i].T_old = decoder_out[i].has_dest ? next_map_table[dest_arch_reg[i]] : rob_entries[i].T_new;      //this should be coming from map table
                rob_entries[i].illegal = decoder_out[i].illegal;
                rob_entries[i].NPC = decoder_out[i].NPC;
                rob_entries[i].is_store = decoder_out[i].wr_mem;

                // create the branch checkpoint
                if(decoder_out[i].cond_branch || decoder_out[i].uncond_branch) begin // TODO: need to check 'branch' to an actual flag
                    if(~next_b_mask) begin // checking that there is room in the BS
                        updated_free_list[regs_to_use[i]] = 0;
                        next_map_table[dest_arch_reg[i]] = decoder_out[i].has_dest ? regs_to_use[i] : next_map_table[dest_arch_reg[i]];
                        for (int j = 0; j < `B_MASK_WIDTH; ++j) begin
                            if (b_mask_chosen_spots[branches_dispatching][j]) begin
                                // branch_stack_entries[j].recovery_PC = decoder_out[i].is_jump ? decoder_out[i].predicted_PC : decoder_out[i].NPC; 
                                branch_stack_entries[j].recovery_PC = decoder_out[i].NPC;
                                branch_stack_entries[j].rob_tail = (rob_tail + i + 1) % `ROB_SZ;
                                branch_stack_entries[j].free_list = updated_free_list;
                                branch_stack_entries[j].map_table = next_map_table;
                                branch_stack_entries[j].b_m = next_b_mask;
                                branch_stack_entries[j].bp_packet = decoder_out[i].bp_packet;
                                branch_stack_entries[j].is_jump = decoder_out[i].is_jump;
                                branch_stack_entries[j].original_PC = decoder_out[i].PC;
                                branch_stack_entries[j].sq_tail = sq_tail_combinational;
                                branch_stack_entries[j].sq_mask = dispatch_sq_mask;
                                next_b_mask[j] = 1'b1;
                                rs_entries[i].b_mask_mask[j] = 1'b1;
                            end
                        end
                        branches_dispatching += 1;
                    end else begin
                        break;
                    end
                end 

                // Store Dispatched
                if (decoder_out[i].wr_mem) begin 
                    if (stores_dispatching < sq_spots) begin
                        dispatch_sq_mask[sq_tail_combinational.sq_idx] = 1'b1;
                        rs_entries[i].sq_mask[sq_tail_combinational.sq_idx] = 1'b1;
                        sq_tail_combinational = sq_tail_combinational + 1;
                        stores_dispatching += 1;
                    end else begin
                        break;
                    end
                end 

                // Load Dispatched
                if (decoder_out[i].rd_mem) begin
                    rs_entries[i].sq_mask = dispatch_sq_mask;
                end

                updated_free_list[regs_to_use[i]] = 0;
                next_map_table[dest_arch_reg[i]] = decoder_out[i].has_dest ? regs_to_use[i] : next_map_table[dest_arch_reg[i]];
                num_dispatched += 1;
            end
        end
    end
    
    always_ff @(posedge clock) begin
        if (reset) begin
            for(int i = 0; i < `ARCH_REG_SZ_R10K; ++i) begin
                map_table[i] <= i[`ARCH_REG_ID_BITS-1:0];
            end
        end else begin
            /*for (int i = 0; i < `ARCH_REG_SZ_R10K; ++i) begin
                $display("map_table[%d]: %d", i, map_table[i]);
            end*/
            // for (int i = 0; i < `N; ++i) begin
            //     $display("dest_arch_reg[%d]: %d\ndecoder_out[%d].has_dest: %b\nregs_to_use[%d]: %d", i, dest_arch_reg[i], i, decoder_out[i].has_dest, i, regs_to_use[i]);
            // end
            // $display("sq_spots: %d", sq_spots);
            // $display(
            //     "num_dispatched: %d\ni_num_dispatched: %d\nrob_spots: %d\nrs_spots: %d",
            //     num_dispatched,
            //     i_num_dispatched,
            //     rob_spots,
            //     rs_spots
            // );
            map_table <= restore_valid ? map_table_restore : next_map_table;
        end
    end

    // `ifdef DEBUG
    //     assign dispatch_debug = {
    //         map_table:      map_table,
    //         next_map_table: next_map_table,
    //         fu_type:        fu_type
    //     };
    // `endif

endmodule
