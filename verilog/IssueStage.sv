`include "verilog/sys_defs.svh"

module Issue # (
) (
    input logic                                clock,
    input logic                                reset,

    // ------------- FROM FREDDY -------------- //
    input logic        [`PHYS_REG_SZ_R10K-1:0] complete_list,       // The entire complete list of each register

    // ------------- TO/FROM RS -------------- //
    input RS_PACKET               [`RS_SZ-1:0] rs_data_next,             // full RS data exposed to issue for psel and FU packets generating
    input logic                   [`RS_SZ-1:0] rs_valid_issue,
    output logic                  [`RS_SZ-1:0] rs_data_issuing,     // set index to 1 when a rs_data is selected to be issued

    // ------------- TO/FROM REGFILE -------------- //
    
    input DATA             [`NUM_FU_ALU-1:0] issue_alu_read_data_1,
    input DATA             [`NUM_FU_ALU-1:0] issue_alu_read_data_2,
    input DATA            [`NUM_FU_MULT-1:0] issue_mult_read_data_1,
    input DATA            [`NUM_FU_MULT-1:0] issue_mult_read_data_2,
    input DATA          [`NUM_FU_BRANCH-1:0] issue_branch_read_data_1,
    input DATA          [`NUM_FU_BRANCH-1:0] issue_branch_read_data_2,
    input DATA            [`NUM_FU_LOAD-1:0] issue_load_read_data_1,
    input DATA           [`NUM_FU_STORE-1:0] issue_store_read_data_1,
    input DATA           [`NUM_FU_STORE-1:0] issue_store_read_data_2,

    output PHYS_REG_IDX    [`NUM_FU_ALU-1:0] issue_alu_regs_reading_1,
    output PHYS_REG_IDX    [`NUM_FU_ALU-1:0] issue_alu_regs_reading_2,
    output PHYS_REG_IDX   [`NUM_FU_MULT-1:0] issue_mult_regs_reading_1,
    output PHYS_REG_IDX   [`NUM_FU_MULT-1:0] issue_mult_regs_reading_2,
    output PHYS_REG_IDX [`NUM_FU_BRANCH-1:0] issue_branch_regs_reading_1,
    output PHYS_REG_IDX [`NUM_FU_BRANCH-1:0] issue_branch_regs_reading_2,
    output PHYS_REG_IDX   [`NUM_FU_LOAD-1:0] issue_load_regs_reading_1,
    output PHYS_REG_IDX  [`NUM_FU_STORE-1:0] issue_store_regs_reading_1,
    output PHYS_REG_IDX  [`NUM_FU_STORE-1:0] issue_store_regs_reading_2,
    
    // ------------- FROM CDB -------------- //
    input CDB_REG_PACKET              [`N-1:0] cdb_reg,
    input CDB_REG_PACKET              [`N-1:0] next_cdb_reg,

    // ------------- TO/FROM EXECUTE -------------- //
    // TODO: include the backpressure signals from each FU. 
    input                         [`NUM_FU_MULT-1:0] mult_free, // backpressure signal from the mult FU
    input                         [`NUM_FU_LOAD-1:0] load_free, // backpressure signal from the load FU

    input                         [`NUM_FU_MULT-1:0] mult_cdb_req, // High if there is a valid instruction in the second to last stage of mult
    input                      [`LOAD_BUFFER_SZ-1:0] load_cdb_req, // High if there is a valid instruction in the second to last stage of load

    output logic                  [`NUM_FU_MULT-1:0] mult_cdb_gnt,
    output logic               [`LOAD_BUFFER_SZ-1:0] load_cdb_gnt,
    output ALU_PACKET              [`NUM_FU_ALU-1:0] alu_packets,
    output MULT_PACKET            [`NUM_FU_MULT-1:0] mult_packets,
    output BRANCH_PACKET        [`NUM_FU_BRANCH-1:0] branch_packets,
    output LOAD_ADDR_PACKET       [`NUM_FU_LOAD-1:0] load_addr_packets,
    output logic [`N-1:0]        [`NUM_FU_TOTAL-1:0] complete_gnt_bus,

    // ------------- TO/FROM STORE ADDR STAGE  -------------- //
    output STORE_ADDR_PACKET     [`NUM_FU_STORE-1:0] store_addr_packets
);

genvar i;
// Functional Unit Request Lines
logic [`RS_SZ-1:0] branch_entries_valid; // Which entries in the rs are a branch instruction
logic [`RS_SZ-1:0] mult_entries_valid;
logic [`RS_SZ-1:0] alu_entries_valid;
logic [`RS_SZ-1:0] load_entries_valid;
logic [`RS_SZ-1:0] store_entries_valid;
logic [`RS_SZ-1:0] single_cycle_entries_valid;

assign single_cycle_entries_valid = branch_entries_valid | alu_entries_valid; // which entries in the rs are single cycle instructions

//Functional Unit Grant Buses
logic [`N-1:0]             [`NUM_FU_TOTAL-1:0] next_complete_gnt_bus;
logic                             [`RS_SZ-1:0] rs_cdb_gnt;
logic                        [`NUM_FU_ALU-1:0] alu_cdb_gnt;
logic                     [`NUM_FU_BRANCH-1:0] branch_cdb_gnt;

logic [`NUM_FU_BRANCH-1:0]        [`RS_SZ-1:0] branch_inst_gnt_bus;
logic [`NUM_FU_ALU-1:0]           [`RS_SZ-1:0] alu_inst_gnt_bus;
logic [`NUM_FU_MULT-1:0]          [`RS_SZ-1:0] mult_inst_gnt_bus;
logic [`NUM_FU_LOAD-1:0]          [`RS_SZ-1:0] load_inst_gnt_bus;
logic [`NUM_FU_STORE-1:0]         [`RS_SZ-1:0] store_inst_gnt_bus;

logic [`NUM_FU_MULT-1:0]    [`NUM_FU_MULT-1:0] mult_fu_gnt_bus;

generate
for (i = 0; i < `RS_SZ; ++i) begin
    assign branch_entries_valid[i] = rs_valid_issue[i] && rs_data_next[i].Source1_ready && rs_data_next[i].Source2_ready && (rs_data_next[i].decoded_signals.FU_type == BU);
    assign mult_entries_valid[i] = rs_valid_issue[i] && rs_data_next[i].Source1_ready && rs_data_next[i].Source2_ready && (rs_data_next[i].decoded_signals.FU_type == MULT); 
    assign alu_entries_valid[i] = rs_valid_issue[i] && rs_data_next[i].Source1_ready && rs_data_next[i].Source2_ready && (rs_data_next[i].decoded_signals.FU_type == ALU); 
    assign load_entries_valid[i] = rs_valid_issue[i] && rs_data_next[i].Source1_ready && rs_data_next[i].Source2_ready && !rs_data_next[i].sq_mask && (rs_data_next[i].decoded_signals.FU_type == LOAD); 
    assign store_entries_valid[i] = rs_valid_issue[i] && rs_data_next[i].Source1_ready && rs_data_next[i].Source2_ready && (rs_data_next[i].decoded_signals.FU_type == STORE); 
end
endgenerate

always_comb begin
    rs_data_issuing = '0;
    for (int i = 0; i < `NUM_FU_MULT; ++i) begin
        rs_data_issuing |= (mult_inst_gnt_bus[i] && mult_fu_gnt_bus[i]) ? mult_inst_gnt_bus[i] : '0;
    end
    for (int i = 0; i < `NUM_FU_ALU; ++i) begin
        rs_data_issuing |= alu_inst_gnt_bus[i] & rs_cdb_gnt;
    end
    for (int i = 0; i < `NUM_FU_BRANCH; ++i) begin
        rs_data_issuing |= branch_inst_gnt_bus[i] & rs_cdb_gnt;
    end
    for (int i = 0; i < `NUM_FU_LOAD; ++i) begin
        rs_data_issuing |= load_free ? load_inst_gnt_bus[i] : '0; 
    end
    for (int i = 0; i < `NUM_FU_STORE; ++i) begin
        rs_data_issuing |= store_inst_gnt_bus[i]; 
    end
end

psel_gen #(
    .WIDTH(`RS_SZ),
    .REQS(`NUM_FU_BRANCH)
) branch_inst_psel (
    .req(branch_entries_valid),
    .gnt_bus(branch_inst_gnt_bus),
    .empty(empty)
);

psel_gen #(
    .WIDTH(`RS_SZ),
    .REQS(`NUM_FU_MULT)
) mult_inst_psel (
    .req(mult_entries_valid),
    .gnt_bus(mult_inst_gnt_bus),
    .empty(empty)
);

psel_gen #(
    .WIDTH(`RS_SZ),
    .REQS(`NUM_FU_ALU)
) alu_inst_psel (
    .req(alu_entries_valid),
    .gnt_bus(alu_inst_gnt_bus),
    .empty(empty)
);

psel_gen #(
    .WIDTH(`RS_SZ),
    .REQS(`NUM_FU_LOAD)
) load_inst_psel (
    .req(load_entries_valid),
    .gnt_bus(load_inst_gnt_bus),
    .empty(empty)
);

psel_gen #(
    .WIDTH(`RS_SZ),
    .REQS(`NUM_FU_STORE)
) store_inst_psel (
    .req(store_entries_valid),
    .gnt_bus(store_inst_gnt_bus),
    .empty(empty)
);

// FU PSELS

psel_gen #(
    .WIDTH(`NUM_FU_MULT),
    .REQS(`NUM_FU_MULT)
) mult_fu_psel (
    .req(mult_free),
    .gnt_bus(mult_fu_gnt_bus),
    .empty(empty)
);


// CDB psel to select a total of N instructions to complete between the multi cycle FUs and the RS entries

psel_gen #(
    .WIDTH(`CDB_ARBITER_SZ),
    .REQS(`N)
) cdb_psel (
    .req({single_cycle_entries_valid, mult_cdb_req, load_cdb_req}),
    .gnt({rs_cdb_gnt, mult_cdb_gnt, load_cdb_gnt}),
    .empty(empty)
);

// Create The Branch Packets Issuing
generate
    //loop through branch gnt bus
    for (i = 0; i < `NUM_FU_BRANCH; ++i) begin : branch_loop
        logic [`RS_SZ_BITS-1:0] branch_index;
        encoder #(`RS_SZ, `RS_SZ_BITS) encoders_branch (branch_inst_gnt_bus[i], branch_index);
        
        //assign rs_data_issuing = branch_inst_gnt_bus[i] & rs_cdb_gnt;

        always_comb begin 
            issue_branch_regs_reading_1[i] = '0;
            issue_branch_regs_reading_2[i] = '0;
            branch_packets[i] = NOP_BRANCH_PACKET; //NOP
            branch_cdb_gnt[i] = 1'b0;
            if (branch_inst_gnt_bus[i] & rs_cdb_gnt) begin
                //rs_data_issuing = branch_inst_gnt_bus[i];

                //assign regfile_read_indices
                issue_branch_regs_reading_1[i] = rs_data_next[branch_index].Source1;
                issue_branch_regs_reading_2[i] = rs_data_next[branch_index].Source2;

                // TODO: get the data from rs_entries[branch_index] to form this branch packet
                branch_packets[i].inst = rs_data_next[branch_index].decoded_signals.inst;
                branch_packets[i].valid = rs_data_next[branch_index].decoded_signals.valid;
                branch_packets[i].PC = rs_data_next[branch_index].decoded_signals.PC;
                branch_packets[i].NPC = rs_data_next[branch_index].decoded_signals.NPC;
                branch_packets[i].conditional = rs_data_next[branch_index].decoded_signals.cond_branch;
                branch_packets[i].opa_select = rs_data_next[branch_index].decoded_signals.opa_select;
                branch_packets[i].opb_select = rs_data_next[branch_index].decoded_signals.opb_select;            
                branch_packets[i].dest_reg_idx = rs_data_next[branch_index].T_new;
                branch_packets[i].predict_taken = rs_data_next[branch_index].decoded_signals.predict_taken;
                branch_packets[i].branch_func = rs_data_next[branch_index].decoded_signals.inst.b.funct3;
                branch_packets[i].bmm = rs_data_next[branch_index].b_mask_mask;
                branch_packets[i].predicted_PC = rs_data_next[branch_index].decoded_signals.predicted_PC;

                // Get the data from the prf
                if (complete_list[rs_data_next[branch_index].Source1]) begin
                    branch_packets[i].source_reg_1 = issue_branch_read_data_1[i];

                // Cam the CDB to get the forwarded data
                end else begin
                    for(int j = 0; j < `N; ++j) begin
                        if (rs_data_next[branch_index].Source1 == next_cdb_reg[j].completing_reg) begin
                            branch_packets[i].source_reg_1 = next_cdb_reg[j].result;
                        end
                    end
                    for(int j = 0; j < `N; ++j) begin
                        if (rs_data_next[branch_index].Source1 == cdb_reg[j].completing_reg) begin
                            branch_packets[i].source_reg_1 = cdb_reg[j].result;
                        end
                    end
                end

                if (complete_list[rs_data_next[branch_index].Source2]) begin
                    branch_packets[i].source_reg_2 = issue_branch_read_data_2[i];
                end else begin
                    for(int j = 0; j < `N; ++j) begin
                        if(rs_data_next[branch_index].Source2 == next_cdb_reg[j].completing_reg) begin
                            branch_packets[i].source_reg_2 = next_cdb_reg[j].result;
                        end
                    end
                    for(int j = 0; j < `N; ++j) begin
                        if(rs_data_next[branch_index].Source2 == cdb_reg[j].completing_reg) begin
                            branch_packets[i].source_reg_2 = cdb_reg[j].result;
                        end
                    end
                end
                
                branch_cdb_gnt[i] = 1'b1;
            end
        end
    end
 
endgenerate

// Create The ALU Packets Issuing


generate
    //loop through alu gnt bus
    for (i = 0; i < `NUM_FU_ALU; ++i) begin : alu_loop
        logic [`RS_SZ_BITS-1:0] alu_index;
        encoder #(`RS_SZ, `RS_SZ_BITS) encoders_alu (alu_inst_gnt_bus[i], alu_index);

        // assign rs_data_issuing = alu_inst_gnt_bus[i] & rs_cdb_gnt;

        always_comb begin 
            issue_alu_regs_reading_1[i] = 1'b0;
            issue_alu_regs_reading_2[i] = 1'b0;
            alu_packets[i] = NOP_ALU_PACKET; //NOP
            alu_cdb_gnt[i] = 1'b0;
            if (alu_inst_gnt_bus[i] & rs_cdb_gnt) begin
                //regfile_read_indices
                issue_alu_regs_reading_1[i] = rs_data_next[alu_index].Source1;
                issue_alu_regs_reading_2[i] = rs_data_next[alu_index].Source2;

                alu_packets[i].inst = rs_data_next[alu_index].decoded_signals.inst;
                alu_packets[i].valid = rs_data_next[alu_index].decoded_signals.valid;
                alu_packets[i].PC = rs_data_next[alu_index].decoded_signals.PC;
                alu_packets[i].NPC = rs_data_next[alu_index].decoded_signals.NPC;
                alu_packets[i].opa_select = rs_data_next[alu_index].decoded_signals.opa_select;
                alu_packets[i].opb_select = rs_data_next[alu_index].decoded_signals.opb_select;
                alu_packets[i].dest_reg_idx = rs_data_next[alu_index].T_new;
                alu_packets[i].alu_func = rs_data_next[alu_index].decoded_signals.alu_func;

                if (complete_list[rs_data_next[alu_index].Source1]) begin
                    alu_packets[i].source_reg_1 = issue_alu_read_data_1[i];
                end else begin
                    for(int j = 0; j < `N; ++j) begin
                        if (rs_data_next[alu_index].Source1 == next_cdb_reg[j].completing_reg) begin
                            alu_packets[i].source_reg_1 = next_cdb_reg[j].result;
                        end
                    end
                    for(int j = 0; j < `N; ++j) begin
                        if (rs_data_next[alu_index].Source1 == cdb_reg[j].completing_reg) begin
                            alu_packets[i].source_reg_1 = cdb_reg[j].result;
                        end
                    end
                end

                if (complete_list[rs_data_next[alu_index].Source2]) begin
                    alu_packets[i].source_reg_2 = issue_alu_read_data_2[i];
                end else begin
                    for(int j = 0; j < `N; ++j) begin
                        if(rs_data_next[alu_index].Source2 == next_cdb_reg[j].completing_reg) begin
                            alu_packets[i].source_reg_2 = next_cdb_reg[j].result;
                        end
                    end
                    for(int j = 0; j < `N; ++j) begin
                        if(rs_data_next[alu_index].Source2 == cdb_reg[j].completing_reg) begin
                            alu_packets[i].source_reg_2 = cdb_reg[j].result;
                        end
                    end
                end
                
                alu_cdb_gnt[i] = 1'b1;
            end
        end
    end
endgenerate


// Create The Mult Packets Issuing

parameter LOG_NUM_FU_MULT = ($clog2(`NUM_FU_MULT) < 1) ? 1 : $clog2(`NUM_FU_MULT);

logic [`NUM_FU_MULT-1:0] [`RS_SZ_BITS-1:0]  mult_rs_index;
logic [`NUM_FU_MULT-1:0] [LOG_NUM_FU_MULT-1:0] mult_fu_index;
encoder #(`RS_SZ, `RS_SZ_BITS) inst_encoders_mult [`NUM_FU_MULT-1:0] (mult_inst_gnt_bus, mult_rs_index);
encoder #(`NUM_FU_MULT, LOG_NUM_FU_MULT) fu_encoders_mult [`NUM_FU_MULT-1:0] (mult_fu_gnt_bus, mult_fu_index);
// for (i = 0; i < `NUM_FU_MULT; ++i) begin 
//     assign rs_data_issuing = (mult_inst_gnt_bus[i] && mult_fu_gnt_bus[i]) ? mult_inst_gnt_bus[i] : '0;
// end

always_comb begin
    issue_mult_regs_reading_1 = '0;
    issue_mult_regs_reading_2 = '0;
    for (int i = 0; i < `NUM_FU_MULT; ++i) begin : nop_loop
        mult_packets[i] = NOP_MULT_PACKET; //NOP
    end
    for (int i = 0; i < `NUM_FU_MULT; ++i) begin : mult_loop
        //mult_packets[mult_fu_index[i]] = NOP_MULT_PACKET; //NOP
        if (mult_inst_gnt_bus[i] && mult_fu_gnt_bus[i]) begin
            // Reading RegFile
            issue_mult_regs_reading_1[i] = rs_data_next[mult_rs_index[i]].Source1;
            issue_mult_regs_reading_2[i] = rs_data_next[mult_rs_index[i]].Source2;

            mult_packets[mult_fu_index[i]].valid = rs_data_next[mult_rs_index[i]].decoded_signals.valid; // TODO: get the data from rs_entries[mult_rs_index] to form this mult packet
            mult_packets[mult_fu_index[i]].dest_reg_idx = rs_data_next[mult_rs_index[i]].T_new;
            mult_packets[mult_fu_index[i]].bm = rs_data_next[mult_rs_index[i]].b_mask;
            mult_packets[mult_fu_index[i]].mult_func = rs_data_next[mult_rs_index[i]].decoded_signals.inst.r.funct3;


            if (complete_list[rs_data_next[mult_rs_index[i]].Source1]) begin
                mult_packets[mult_fu_index[i]].source_reg_1 = issue_mult_read_data_1[i];
            end else begin
                for(int j = 0; j < `N; ++j) begin
                    if (rs_data_next[mult_rs_index[i]].Source1 == next_cdb_reg[j].completing_reg) begin
                        mult_packets[mult_fu_index[i]].source_reg_1 = next_cdb_reg[j].result;
                    end
                end
                for(int j = 0; j < `N; ++j) begin
                    if (rs_data_next[mult_rs_index[i]].Source1 == cdb_reg[j].completing_reg) begin
                        mult_packets[mult_fu_index[i]].source_reg_1 = cdb_reg[j].result;
                    end
                end
            end

            if (complete_list[rs_data_next[mult_rs_index[i]].Source2]) begin
                mult_packets[mult_fu_index[i]].source_reg_2 = issue_mult_read_data_2[i];
            end else begin
                for(int j = 0; j < `N; ++j) begin
                    if(rs_data_next[mult_rs_index[i]].Source2 == next_cdb_reg[j].completing_reg) begin
                        mult_packets[mult_fu_index[i]].source_reg_2 = next_cdb_reg[j].result;
                    end
                end
                for(int j = 0; j < `N; ++j) begin
                    if(rs_data_next[mult_rs_index[i]].Source2 == cdb_reg[j].completing_reg) begin
                        mult_packets[mult_fu_index[i]].source_reg_2 = cdb_reg[j].result;
                    end
                end
            end
        end
    end
end

// Create The Load Packets Issuing
generate
    //loop through load gnt bus
    for (i = 0; i < `NUM_FU_LOAD; ++i) begin : load_loop
        logic [`RS_SZ_BITS-1:0] load_index;
        encoder #(`RS_SZ, `RS_SZ_BITS) encoders_load (load_inst_gnt_bus[i], load_index);

        always_comb begin 
            issue_load_regs_reading_1[i] = 1'b0;
            load_addr_packets[i] = NOP_LOAD_ADDR_PACKET; //NOP
            if (load_inst_gnt_bus[i] && load_free) begin
                //regfile_read_indices
                issue_load_regs_reading_1[i] = rs_data_next[load_index].Source1;
                load_addr_packets[i].valid = rs_data_next[load_index].decoded_signals.valid;
                load_addr_packets[i].bm = rs_data_next[load_index].b_mask;
                load_addr_packets[i].sq_tail = rs_data_next[load_index].sq_tail;
                load_addr_packets[i].load_func = rs_data_next[load_index].decoded_signals.inst.r.funct3;
                load_addr_packets[i].dest_reg_idx = rs_data_next[load_index].T_new;

                if (complete_list[rs_data_next[load_index].Source1]) begin
                    load_addr_packets[i].source_reg_1 = issue_load_read_data_1[i];
                end else begin
                    for(int j = 0; j < `N; ++j) begin
                        if (rs_data_next[load_index].Source1 == next_cdb_reg[j].completing_reg) begin
                            load_addr_packets[i].source_reg_1 = next_cdb_reg[j].result;
                        end
                    end
                    for(int j = 0; j < `N; ++j) begin
                        if (rs_data_next[load_index].Source1 == cdb_reg[j].completing_reg) begin
                            load_addr_packets[i].source_reg_1 = cdb_reg[j].result;
                        end
                    end
                end

                load_addr_packets[i].source_reg_2 = `RV32_signext_Iimm(rs_data_next[load_index].decoded_signals.inst);
            end
        end
    end
endgenerate

// Create The Store Packets Issuing
generate
    //loop through store gnt bus
    for (i = 0; i < `NUM_FU_STORE; ++i) begin : store_loop
        logic [`RS_SZ_BITS-1:0] store_index;
        encoder #(`RS_SZ, `RS_SZ_BITS) encoders_store (store_inst_gnt_bus[i], store_index);

        always_comb begin 
            issue_store_regs_reading_1[i] = 1'b0;
            issue_store_regs_reading_2[i] = 1'b0;
            store_addr_packets[i] = NOP_STORE_ADDR_PACKET; //NOP
            if (store_inst_gnt_bus[i]) begin

                //regfile_read_indices
                issue_store_regs_reading_1[i] = rs_data_next[store_index].Source1;
                issue_store_regs_reading_2[i] = rs_data_next[store_index].Source2;

                store_addr_packets[i].valid = rs_data_next[store_index].decoded_signals.valid;
                store_addr_packets[i].sq_mask = rs_data_next[store_index].sq_mask;
                store_addr_packets[i].store_func = rs_data_next[store_index].decoded_signals.inst.r.funct3;
                store_addr_packets[i].dest_reg_idx = rs_data_next[store_index].T_new;

                if (complete_list[rs_data_next[store_index].Source1]) begin
                    store_addr_packets[i].source_reg_1 = issue_store_read_data_1[i];
                end else begin
                    for(int j = 0; j < `N; ++j) begin
                        if (rs_data_next[store_index].Source1 == next_cdb_reg[j].completing_reg) begin
                            store_addr_packets[i].source_reg_1 = next_cdb_reg[j].result;
                        end
                    end
                    for(int j = 0; j < `N; ++j) begin
                        if (rs_data_next[store_index].Source1 == cdb_reg[j].completing_reg) begin
                            store_addr_packets[i].source_reg_1 = cdb_reg[j].result;
                        end
                    end
                end

                if (complete_list[rs_data_next[store_index].Source2]) begin
                    store_addr_packets[i].source_reg_2 = issue_store_read_data_2[i];
                end else begin
                    for(int j = 0; j < `N; ++j) begin
                        if (rs_data_next[store_index].Source2 == next_cdb_reg[j].completing_reg) begin
                            store_addr_packets[i].source_reg_2 = next_cdb_reg[j].result;
                        end
                    end
                    for(int j = 0; j < `N; ++j) begin
                        if (rs_data_next[store_index].Source2 == cdb_reg[j].completing_reg) begin
                            store_addr_packets[i].source_reg_2 = cdb_reg[j].result;
                        end
                    end
                end

                store_addr_packets[i].store_imm = `RV32_signext_Simm(rs_data_next[store_index].decoded_signals.inst);

            end
        end
    end
endgenerate

//Final Complete selector
psel_gen #(
    .WIDTH(`NUM_FU_TOTAL),
    .REQS(`N)
) complete_psel (
    .req({branch_cdb_gnt, alu_cdb_gnt, mult_cdb_gnt , load_cdb_gnt}), //TODO change ordering later!! optimize!!!!! 
    .gnt_bus(next_complete_gnt_bus),
    .empty(empty)
);

always_ff @(posedge clock) begin
    if(reset) begin
        complete_gnt_bus <= '0;
    end else begin
        complete_gnt_bus <= next_complete_gnt_bus;
        // $display("------ ISSUE STAGE --------");
        // for (int i = 0; i < `RS_SZ; ++i) begin
        //     $display("rs_data_next.: %b", store_addr_packets[0].sq_mask);
        // end
        // $display("store_addr_packet.sq_mask: %b", store_addr_packets[0].sq_mask);
        // $display("rs_data_issuing  : %b", rs_data_issuing);
        // $display("rs_cdb_gnt  : %b", rs_cdb_gnt);
        // $display("single_cycle_inst : %b", {single_cycle_entries_valid, mult_cdb_req, 1'b0});
        // for (int i = 0; i < `NUM_FU_ALU; ++i) begin
        //     $display("alu_inst_gnt_bus[%d]  : %b", i, alu_inst_gnt_bus[i]);
        // end
        // for (int i = 0; i < `NUM_FU_BRANCH; ++i) begin
        //     $display("branch_inst_gnt_bus[%d]  : %b", i, branch_inst_gnt_bus[i]);
        // end
        // for (int i = 0; i < `NUM_FU_MULT; ++i) begin
        //     $display("mult_inst_gnt_bus[%d]  : %b", i, mult_inst_gnt_bus[i]);
        // end
        // for (int i = 0; i < `NUM_FU_STORE; ++i) begin
        //     $display("store_addr_packet[%d].source_reg_1: %b", i, store_addr_packet[i].source_reg_1);
        //     $display("store_addr_packet[%d].source_reg_2: %b", i, store_addr_packet[i].source_reg_2);
        // end
    end
end

endmodule