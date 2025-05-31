`include "verilog/sys_defs.svh"

module Fetch #() (
    input  logic                        clock, 
    input  logic                        reset,

    // ------------ TO I-CACHE + BP + BTB ------------- //
    output ADDR                    [`N-1:0] PCs_out, 

    // ------------ TO/FROM I-CACHE ------------- //
    input  INST                    [`N-1:0] cache_data,
    input  logic                   [`N-1:0] cache_miss,
    
    // ------------- FROM BRANCH STACK -------------- //
    input  ADDR                             PC_restore,                      
    input  logic                            restore_valid,
  
    // ------------ TO/FROM INSTRUCTION BUFFER -------- //
    input  logic     [`NUM_SCALAR_BITS-1:0] inst_buffer_spots,    //number of spots in instruction buffer
    output FETCH_PACKET            [`N-1:0] inst_buffer_inputs,   //instructions going to instruction buffer
    output logic     [`NUM_SCALAR_BITS-1:0] inst_valid,           //number of valid instructions fetch sends to instruction buffer 

    // ------------ TO/FROM BRANCH PREDICTOR -------- //
    input  BRANCH_PREDICTOR_PACKET [`N-1:0] bp_packets,
    input  logic                   [`N-1:0] branches_taken,
    output logic [`N-1:0]          [`N-1:0] branch_gnt_bus,
    output logic                   [`N-1:0] final_branch_gnt_line,
    output logic                            no_branches_fetched,
   
   // ------------ FROM BTB -------- //
    input  ADDR                    [`N-1:0] target_PCs,       //<-- just set this somewhere?
    input  logic                   [`N-1:0] btb_hits
);

    ADDR   [`N:0] PCs;
    ADDR Next_PC_reg, PC_reg;
    logic [`N-1:0] valid_jump;

    logic [`N-1:0] valid_branch, masked_valid_branch, shifted_branches, shifted_jumps;
    logic [`N-1:0] valid_store;

    logic [`NUM_SCALAR_BITS-1:0] final_valid_inst_idx;

    logic no_limiting_inst;

    logic [`N-1:0] right_most_inst;
    logic [`NUM_SCALAR_BITS-1:0] right_most_inst_idx;
    logic [`NUM_SCALAR_BITS-1:0] inst_valid_temp;           //number of valid instructions fetch sends to instruction buffer 
    

    lsb_psel_gen #(
        .WIDTH(`N),
        .REQS(`N)
    ) branch_inst_psel (
        .req(valid_branch),
        .gnt_bus(branch_gnt_bus)
    );

    assign shifted_branches = branches_taken << 1;
    assign shifted_jumps = valid_jump << 1;

    lsb_psel_gen #(
        .WIDTH(`N),
        .REQS(1)
    ) right_most_inst_psel (
        .req(cache_miss | shifted_branches | shifted_jumps),
        .gnt(right_most_inst),
        .empty(no_limiting_inst)
    );

    msb_psel_gen #(
        .WIDTH(`N),
        .REQS(1)
    ) final_branch_inst_psel (
        .req(masked_valid_branch),
        .gnt(final_branch_gnt_line),
        .empty(no_branches_fetched)
    );

    encoder #(`N, `NUM_SCALAR_BITS) final_inst_encoder (right_most_inst, right_most_inst_idx);

    assign inst_valid_temp = no_limiting_inst ? `N : right_most_inst_idx;
    assign inst_valid = restore_valid ? 0 : (inst_valid_temp <= inst_buffer_spots) ? inst_valid_temp : inst_buffer_spots;
    assign PCs_out = PCs[`N-1:0];

    always_comb begin
        masked_valid_branch = '0;
        for (int i = 0; i < `N; ++i) begin
            if (i < inst_valid && valid_branch[i]) begin
                masked_valid_branch[i] = 1'b1;
            end
        end
    end

    always_comb begin
        inst_buffer_inputs = '0;
        valid_branch = '0;
        valid_jump = '0;
        valid_store = '0;
        // Next_PC_reg = restore_valid ? PC_restore : PC_reg;
        Next_PC_reg = PC_reg;
        
        //creating array of N PCs that will be sent to ICache
        for (int i = 0; i <= `N; ++i) begin
            PCs[i] = Next_PC_reg + (4 * i);
        end
        
        //fetching N instructions from I cache if they are a hit
        for (int i = 0; i < `N; ++i) begin
            valid_branch[i] = (cache_data[i].r.opcode == `RV32_BRANCH);

            valid_jump[i] = (cache_data[i].r.opcode == `RV32_JALR_OP) 
                            || (cache_data[i].r.opcode == `RV32_JAL_OP);
                            
            inst_buffer_inputs[i].inst = cache_data[i];
            inst_buffer_inputs[i].PC = PCs[i];
            inst_buffer_inputs[i].predict_taken = (valid_branch[i] && branches_taken[i]) || valid_jump[i]; //should put branch predictor prediction here
            inst_buffer_inputs[i].bp_packet = bp_packets[i];
            inst_buffer_inputs[i].predicted_PC = btb_hits[i] ? target_PCs[i] : PCs[i + 1];
            inst_buffer_inputs[i].is_jump = valid_jump[i];
        end

        if(inst_valid && (branches_taken[inst_valid - 1] || valid_jump[inst_valid - 1])) begin
            // Next_PC_reg = target_PCs[inst_valid - 1];
            Next_PC_reg = inst_buffer_inputs[inst_valid - 1].predicted_PC;
        end else begin
            Next_PC_reg = PCs[inst_valid];
        end

    end

    always_ff @(posedge clock) begin
        if (reset) begin
            PC_reg <= 0;             // initial PC value is 0 (the memory address where our program starts)
        end else if (restore_valid) begin
            PC_reg <= PC_restore;    // or transition to next PC if valid
        end else begin
            PC_reg <= Next_PC_reg;
        end
        // $display("branches_taken: %b", branches_taken);
        // for (int i = 0; i <= `N; ++i) begin
        //     $display("PCs[%d]: %h", i, PCs[i]);
        // end
        // $display("inst_valid_temp: %d", inst_valid_temp);
        // $display("no_limiting_inst: %b", no_limiting_inst);
        // $display("cache_miss_in_fetch: %b", cache_miss);
        // $display("PC_restore: %h", PC_restore);

        // $display(
        //     "inst_buffer_inputs[%d].inst : %b\ninst_buffer_inputs[%d].PC : %b\ninst_buffer_inputs[%d].taken : %b\inst_valid: %b\n", 
        //     i, inst_buffer_inputs[i].inst, 
        //     i, inst_buffer_inputs[i].PC, 
        //     i, inst_buffer_inputs[i].taken,
        //     inst_valid
        // );
    end
endmodule
