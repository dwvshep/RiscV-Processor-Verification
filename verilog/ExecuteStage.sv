`include "verilog/sys_defs.svh"

module ExecuteStage (
    input   logic                                clock,
    input   logic                                reset,

    // --------------- TO/FROM ISSUE --------------- //
    input MULT_PACKET         [`NUM_FU_MULT-1:0] mult_packets_issuing_in, 
    input ALU_PACKET           [`NUM_FU_ALU-1:0] alu_packets_issuing_in,
    input BRANCH_PACKET     [`NUM_FU_BRANCH-1:0] branch_packets_issuing_in,
    input LOAD_ADDR_PACKET    [`NUM_FU_LOAD-1:0] load_packets_issuing_in,

    input logic               [`NUM_FU_MULT-1:0] mult_cdb_gnt,
    input logic            [`LOAD_BUFFER_SZ-1:0] load_cdb_gnt,
    input logic [`N-1:0]     [`NUM_FU_TOTAL-1:0] complete_gnt_bus,

    output logic              [`NUM_FU_MULT-1:0] mult_free,
    output logic              [`NUM_FU_LOAD-1:0] load_free,

    output logic              [`NUM_FU_MULT-1:0] mult_cdb_valid,
    output logic           [`LOAD_BUFFER_SZ-1:0] load_cdb_valid,


    // ------------ TO ALL DATA STRUCTURES ------------- //
    output CDB_ETB_PACKET               [`N-1:0] cdb_completing,
    output CDB_REG_PACKET               [`N-1:0] cdb_reg,
    output CDB_REG_PACKET               [`N-1:0] next_cdb_reg,

    // --------------- TO/FROM BRANCH STACK --------------- //
    input B_MASK_MASK                            b_mm_resolve,        // b_mm_out
    input logic                                  b_mm_mispred,        // restore_valid
    output BRANCH_REG_PACKET                     branch_reg,

    // ------------ TO/FROM CACHE --------------//

    input LOAD_DATA_CACHE_PACKET                 load_data_cache_packet,
    input LOAD_BUFFER_CACHE_PACKET               load_buffer_cache_packet,
    output ADDR                                  load_req_addr,
    output logic                                 load_req_valid,

    // ------------ TO/FROM STORE QUEUE ------------- //
    input DATA                                   sq_load_data,
    input BYTE_MASK                              sq_data_mask,
    output SQ_POINTER                            load_sq_tail
);

    // MULT_PACKET   mult_packets_issuing;
    ALU_PACKET   [`NUM_FU_ALU-1:0] alu_packets_issuing;
    BRANCH_PACKET [`NUM_FU_BRANCH-1:0] branch_packets_issuing;

    CDB_REG_PACKET [`NUM_FU_ALU-1:0] alu_result;
    CDB_REG_PACKET [`NUM_FU_MULT-1:0] mult_result;
    CDB_REG_PACKET [`NUM_FU_BRANCH-1:0] branch_result;
    CDB_REG_PACKET [`LOAD_BUFFER_SZ-1:0] load_result;

    BRANCH_REG_PACKET next_branch_reg;

    always_ff @(posedge clock) begin
        if (reset) begin
            for(int i = 0; i < `NUM_FU_ALU; ++i) begin
                alu_packets_issuing[i] <= NOP_ALU_PACKET;
            end
            for(int i = 0; i < `NUM_FU_BRANCH; ++i) begin
                branch_packets_issuing[i] <= NOP_BRANCH_PACKET;
            end
        end else begin
            alu_packets_issuing <= alu_packets_issuing_in;
            branch_packets_issuing <= branch_packets_issuing_in;
        end
    end

    CDB_REG_PACKET [`NUM_FU_TOTAL-1:0] fu_result;

    assign fu_result = {branch_result, alu_result, mult_result, load_result};

    always_comb begin
        next_cdb_reg = '0;
        cdb_completing = '0;
        for (int i = 0; i < `N; ++i) begin
            for (int j = 0; j < `NUM_FU_TOTAL; ++j) begin
                if (complete_gnt_bus[i][j]) begin
                    // $display("completing!!!!!: %d", fu_result[j].completing_reg);
                    next_cdb_reg[i] = fu_result[j];
                    cdb_completing[i].completing_reg = next_cdb_reg[i].completing_reg;
                    cdb_completing[i].valid = next_cdb_reg[i].valid;
                end
            end
        end
    end

    always_ff @(posedge clock) begin
        if (reset) begin
            cdb_reg <= '0;        
        end else begin
            cdb_reg <= next_cdb_reg;

            // for (int i = 0; i < `N; ++i) begin
            //     $display("cdb_reg[%d].completing_reg : %d", i, cdb_reg[i].completing_reg);
            //     $display("mult_cdb_valid: %b", mult_cdb_valid);
            // end

        end
    end

    alu alu_fus [`NUM_FU_ALU-1:0](
        // Inputs
        .alu_packet(alu_packets_issuing),

        // Output
        .alu_result(alu_result)
    );

    // Instantiate the multiplier
    mult mult_fus [`NUM_FU_MULT-1:0](
        // Inputs
        .clock(clock),
        .reset(reset),
        .mult_packet_in(mult_packets_issuing_in),
        .cdb_gnt(mult_cdb_gnt),
        .b_mm_resolve(b_mm_resolve),
        .b_mm_mispred(b_mm_mispred),

        // Output
        .fu_free(mult_free),
        .cdb_valid(mult_cdb_valid),
        .mult_result(mult_result)
    );

    // Instantiate the conditional branch module
    branch branch_fus [`NUM_FU_BRANCH-1:0] (
        // Inputs
        .clock(clock),
        .branch_packet(branch_packets_issuing),

        // Output
        .branch_reg_result(next_branch_reg),
        .branch_result(branch_result)
    );

    load load_fu [`NUM_FU_LOAD-1:0] (
        .clock(clock),
        .reset(reset), 
    
        // ------------ TO/FROM EXECUTE ------------- //
        .load_addr_packet(load_packets_issuing_in),
        .load_addr_free(load_free),

        // ------------ TO/FROM ISSUE ------------- //
        .load_cdb_en(load_cdb_gnt),
        .load_cdb_req(load_cdb_valid),

        // ------------ TO CDB ------------- //
        .load_result(load_result),

        // ------------ FROM BRANCH STACK --------------//
        .b_mm_resolve(b_mm_resolve),
        .b_mm_mispred(b_mm_mispred),

        // ------------ TO/FROM CACHE --------------//
        .load_data_cache_packet(load_data_cache_packet),
        .load_buffer_cache_packet(load_buffer_cache_packet),
        .load_req_valid(load_req_valid),

        // ------------ TO/FROM STORE QUEUE ------------- //
        .sq_load_data(sq_load_data),
        .sq_data_mask(sq_data_mask),
        .load_sq_tail(load_sq_tail),
        .load_req_addr(load_req_addr) //also goes to cache
    );

    always_ff @(posedge clock) begin
        if(reset) begin
            branch_reg <= '0;
        end else begin
            branch_reg <= next_branch_reg;
            // for (int i = 0; i < `NUM_FU_TOTAL; ++i) begin
            //     $display(
            //         "fu_result[%d].completing_reg: %d\nfu_result[%d].result: %h",
            //         i, fu_result[i].completing_reg, i, fu_result[i].result
            //     );
            // end
            // $display("branch_reg.bm_mispred: %b", branch_reg.bm_mispred);
        end
    end
    //add logic to set the mispredict signal

    // mispredict = prediction XOR actual 
    


endmodule // stage_ex