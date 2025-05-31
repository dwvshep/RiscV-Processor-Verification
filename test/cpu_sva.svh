/////////////////////////////////////////////////////////////////////////

//                                                                     //
//   Modulename :  cpu.sv                                              //
//                                                                     //
//  Description :  Top-level module of the verisimple processor;       //
//                 This instantiates and connects the 5 stages of the  //
//                 Verisimple pipeline together.                       //
//                                                                     //
/////////////////////////////////////////////////////////////////////////

`include "verilog/sys_defs.svh"
`include "verilog/ISA.svh"
`include "test/rob_sva.svh"
`include "test/rs_sva.svh"
`include "test/branchstack_sva.svh"


module cpu_sva (
    input logic                         clock,
    input logic                         reset,
    /*------- ROB WIRES ----------*/

    input logic  [`NUM_SCALAR_BITS-1:0] rob_spots,
    input logic      [`ROB_SZ_BITS-1:0] rob_tail,
    input ROB_PACKET           [`N-1:0] rob_outputs;
    input logic  [`NUM_SCALAR_BITS-1:0] rob_outputs_valid,

`ifdef DEBUG
    input ROB_DEBUG                   rob_debug,
`endif

    /*------- RS WIRES ----------*/

    input logic  [`NUM_SCALAR_BITS-1:0] rs_spots,
    input RS_PACKET       [`RS_SZ-1:0] rs_data,             // The entire RS data 
    input logic           [`RS_SZ-1:0] rs_valid_next,        // 1 if RS data is valid <-- Coded

`ifdef DEBUG
    input RS_DEBUG               rs_debug,
`endif


    /*------- FREDDYLIST WIRES ----------*/  
    
    input PHYS_REG_IDX           [`N-1:0] phys_reg_completing, // decoded signal from cdb_reg
    input logic                  [`N-1:0] completing_valid, // decoded signal from cdb_reg

    input PHYS_REG_IDX           [`N-1:0] regs_to_use,       // physical register indices for dispatch to use
    input logic   [`PHYS_REG_SZ_R10K-1:0] free_list,              // bitvector of the phys reg that are complete

    input logic   [`PHYS_REG_SZ_R10K-1:0] next_complete_list,          // bitvector of the phys reg that are complete
    input logic   [`PHYS_REG_SZ_R10K-1:0] complete_list,
    

    /*------- BRANCH STACK WIRES ----------*/
    input logic                                restore_valid,
    input ADDR                                 PC_restore,
    input logic             [`ROB_SZ_BITS-1:0] rob_tail_restore,
    input logic        [`PHYS_REG_SZ_R10K-1:0] free_list_restore,
    input PHYS_REG_IDX [`ARCH_REG_SZ_R10K-1:0] map_table_restore,     
    input B_MASK                               b_mask_combinational,
    input B_MASK                               b_mm_out,
    `ifdef DEBUG
    input BS_DEBUG                             bs_debug,
    `endif

    /*------- REGFILE WIRES ----------*/
    
    input DATA        [`N-1:0] retire_read_data;
    input DATA        [`NUM_FU_ALU-1:0] issue_alu_read_data_1,
    input DATA        [`NUM_FU_ALU-1:0] issue_alu_read_data_2,
    input DATA        [`NUM_FU_BRANCH-1:0] issue_branch_read_data_1,
    input DATA        [`NUM_FU_BRANCH-1:0] issue_branch_read_data_2,
    input DATA        [`NUM_FU_MULT-1:0] issue_mult_read_data_1,
    input DATA        [`NUM_FU_MULT-1:0] issue_mult_read_data_2,

    /*------- FETCH WIRES ----------*/  
    input FETCH_PACKET         [`N-1:0] inst_buffer_inputs,   //instructions going to instruction buffer
    input logic  [`NUM_SCALAR_BITS-1:0] instructions_valid,

    /*------- FETCH BUFFER WIRES ----------*/    
    input logic  [`NUM_SCALAR_BITS-1:0] inst_buffer_spots,
    input FETCH_PACKET         [`N-1:0] inst_buffer_outputs,   
    input logic  [`NUM_SCALAR_BITS-1:0] inst_buffer_outputs_valid,


    /*------- DECODER WIRES ----------*/
    input FETCH_PACKET  [`N-1:0] inst_buffer_input,
    input DECODE_PACKET [`N-1:0] decoder_out,
    input logic         [`N-1:0] is_rs1_used,
    input logic         [`N-1:0] is_rs2_used,
    input ARCH_REG_IDX  [`N-1:0] source1_arch_reg,
    input ARCH_REG_IDX  [`N-1:0] source2_arch_reg,
    input ARCH_REG_IDX  [`N-1:0] dest_arch_reg,

    /*------- DISPATCH WIRES ----------*/

    input BS_ENTRY_PACKET [`B_MASK_WIDTH-1:0] branch_stack_entries,
    input B_MASK next_b_mask,
    input ROB_PACKET [`N-1:0] rob_entries,
    input RS_PACKET [`N-1:0] rs_entries,
    input logic [`PHYS_REG_SZ_R10K-1:0] updated_free_list,
    input logic [`NUM_SCALAR_BITS-1:0] num_dispatched,
    `ifdef DEBUG
        input DISPATCH_DEBUG dispatch_debug,
    `endif

    /*------- ISSUE WIRES ----------*/

    input wor                    [`RS_SZ-1:0] rs_data_issuing,     // set index to 1 when a rs_data is selected to be issued
    input PHYS_REG_IDX      [`NUM_FU_ALU-1:0] issue_alu_regs_reading_1,
    input PHYS_REG_IDX      [`NUM_FU_ALU-1:0] issue_alu_regs_reading_2,
    input PHYS_REG_IDX     [`NUM_FU_MULT-1:0] issue_mult_regs_reading_1,
    input PHYS_REG_IDX     [`NUM_FU_MULT-1:0] issue_mult_regs_reading_2,
    input PHYS_REG_IDX   [`NUM_FU_BRANCH-1:0] issue_branch_regs_reading_1,
    input PHYS_REG_IDX   [`NUM_FU_BRANCH-1:0] issue_branch_regs_reading_2,
    input logic            [`NUM_FU_MULT-1:0] mult_cdb_gnt,
    input logic            [`NUM_FU_LDST-1:0] ldst_cdb_gnt,
    input ALU_PACKET        [`NUM_FU_ALU-1:0] alu_packets,
    input MULT_PACKET      [`NUM_FU_MULT-1:0] mult_packets,
    input BRANCH_PACKET  [`NUM_FU_BRANCH-1:0] branch_packets,
    input LDST_PACKET      [`NUM_FU_LDST-1:0] ldst_packets,
    input logic [`N-1:0]  [`NUM_FU_TOTAL-1:0] complete_gnt_bus,
    
    /*----------EXECUTE WIRES -------------*/
    input logic              [`NUM_FU_MULT-1:0] mult_free,
    input logic              [`NUM_FU_LDST-1:0] ldst_free,
    input CDB_ETB_PACKET               [`N-1:0] cdb_completing,
    input CDB_REG_PACKET               [`N-1:0] cdb_reg,
    input BRANCH_REG_PACKET                     branch_reg,
    input logic              [`NUM_FU_MULT-1:0] mult_cdb_valid,
    input logic              [`NUM_FU_LDST-1:0] ldst_cdb_valid,

    /*------- RETIRE WIRES ----------*/

    input logic [`NUM_SCALAR_BITS-1:0] num_retiring,
    input PHYS_REG_IDX [`N-1:0] phys_regs_retiring,
    input PHYS_REG_IDX [`N-1:0] retire_phys_regs_reading

);

    //////////////////////////////////////////////////
    //                                              //
    //               DATA STRUCTURES                //
    //                                              //
    //////////////////////////////////////////////////


    /*----------------Reorder Buffer----------------*/

    ROB_sva rob_instance (
        .clock             (clock),
        .reset             (reset),
        .rob_inputs        (rob_entries),
        .rob_inputs_valid  (num_dispatched), 
        .rob_spots         (rob_spots),
        .rob_tail          (rob_tail),
        .num_retiring      (num_retiring),
        .rob_outputs       (rob_outputs),
        .rob_outputs_valid (rob_outputs_valid),
        .tail_restore_valid(restore_valid),
        .tail_restore      (rob_tail_restore)
    `ifdef DEBUG
        ,.rob_debug         (rob_debug)
    `endif
    );


    /*---------------Reservation Station------------*/

    RS_sva rs_instance (
        .clock             (clock),
        .reset             (reset),
        .num_dispatched    (num_dispatched),
        .rs_entries        (rs_entries), 
        .rs_spots          (rs_spots),
        .ETB_tags          (cdb_completing),
        .rs_data_issuing   (rs_data_issuing),
        .rs_data           (rs_data),
        .rs_valid_next     (rs_valid_next),
        .b_mm_resolve      (b_mm_out),
        .b_mm_mispred      (restore_valid)
    `ifdef DEBUG
        ,.rs_debug          (rs_debug)
    `endif
    );


    /*-------------Freddy List--------------------*/

    FreddyList_sva fl_instance (
        .clock                  (clock),
        .reset                  (reset),
        .phys_reg_completing    (phys_reg_completing),
        .completing_valid       (completing_valid), 
        .phys_regs_retiring     (phys_regs_retiring),
        .num_retiring_valid     (num_retiring),
        .free_list_restore      (free_list_restore),
        .restore_flag           (restore_valid),
        .updated_free_list      (updated_free_list),
        .regs_to_use            (regs_to_use),
        .free_list              (free_list),
        .next_complete_list     (next_complete_list),
        .complete_list          (complete_list)
    );


    /*-------------Branch Stack--------------------*/

    BranchStack_sva bs_instance (
        .clock                  (clock),
        .reset                  (reset),
        .restore_valid          (restore_valid),
        .PC_restore             (PC_restore),
        .branch_completing      (branch_reg),
        .rob_tail_restore       (rob_tail_restore),
        .free_list_in           (free_list),
        .free_list_restore      (free_list_restore),
        .branch_stack_entries   (branch_stack_entries),
        .next_b_mask            (next_b_mask),
        .map_table_restore      (map_table_restore),
        .b_mask_combinational   (b_mask_combinational),
        .b_mm_out               (b_mm_out)
        `ifdef DEBUG
        , .bs_debug(bs_debug)
        `endif
    );

    

    /*------------------Reg File --------------------*/

    regfile regfile_instance (
        .clock(clock),
        .reset(reset),
        /*---------------- FROM/TO RETIRE ---------------------------*/
        .retire_phys_regs_reading(retire_phys_regs_reading),
        .retire_read_data(retire_read_data),
        /*---------------- FROM/TO ISSUE ---------------------------*/
        .issue_alu_regs_reading_1(issue_alu_regs_reading_1),
        .issue_alu_regs_reading_2(issue_alu_regs_reading_2),
        .issue_alu_read_data_1(issue_alu_read_data_1),
        .issue_alu_read_data_2(issue_alu_read_data_2),
        .issue_branch_regs_reading_1(issue_branch_regs_reading_1),
        .issue_branch_regs_reading_2(issue_branch_regs_reading_2),
        .issue_branch_read_data_1(issue_branch_read_data_1),
        .issue_branch_read_data_2(issue_branch_read_data_2),
        .issue_mult_regs_reading_1(issue_mult_regs_reading_1),
        .issue_mult_regs_reading_2(issue_mult_regs_reading_2),
        .issue_mult_read_data_1(issue_mult_read_data_1),
        .issue_mult_read_data_2(issue_mult_read_data_2),
        .cdb_reg(cdb_reg)
    );

    /*------------------ Inst Buffer --------------------*/

    instbuffer inst_buffer_instance (
        .clock                      (clock), 
        .reset                      (reset),

        // ------------ TO/FROM FETCH ------------- //
        .inst_buffer_inputs         (inst_buffer_inputs),
        .instructions_valid         (instructions_valid), //number of valid instructions fetch sends to instruction buffer     // New instructions from Dispatch, MUST BE IN ORDER FROM OLDEST TO NEWEST INSTRUCTIONS
        .inst_buffer_spots          (inst_buffer_spots),

        // ------------ FROM EXECUTE ------------- //
        .restore_valid              (restore_valid),

        // ------------ TO/FROM DISPATCH -------- //
        .num_dispatched             (num_dispatched),     //number of spots available in dispatch
        .inst_buffer_outputs        (inst_buffer_outputs),   // For retire to check eligibility
        .inst_buffer_outputs_valid  (inst_buffer_outputs_valid) // If not all N FB entries are valid entries they should not be considered 
    );
    

    //////////////////////////////////////////////////
    //                                              //
    //                  FETCH                       //
    //                                              //
    //////////////////////////////////////////////////

    Fetch fetch_stage(

        .clock(clock), 
        .reset(reset),

        // ------------ TO/FROM MEMORY ------------- //
        // New instructions from Dispatch, MUST BE IN ORDER FROM OLDEST TO NEWEST INSTRUCTIONS
        .inst(inst),  // To distinguish invalid instructions being passed in from Dispatch (A number, NOT one hot)
        .PC_reg(PC),
        
        // ------------- FROM BRANCH STACK -------------- //
        .PC_restore(PC_restore),  // Retire module tells the ROB how many entries can be cleared
        .restore_valid(restore_valid),

        // ------------ TO/FROM FETCH BUFFER ------------- //
        .inst_buffer_spots(inst_buffer_spots),     //number of spots in instruction buffer
        .inst_buffer_inputs(inst_buffer_inputs),   //instructions going to instruction buffer
        .instructions_valid(instructions_valid) //number of valid instructions fetch sends to instruction buffer   
    );


    //////////////////////////////////////////////////
    //                                              //
    //                  DECODER                     //
    //                                              //
    //////////////////////////////////////////////////
    
    decoder #() decode [`N-1:0] (
        .inst_buffer_input(inst_buffer_outputs),
        .decoder_out(decoder_out),
        .is_rs1_used(is_rs1_used),
        .is_rs2_used(is_rs2_used),
        .source1_arch_reg(source1_arch_reg),
        .source2_arch_reg(source2_arch_reg),
        .dest_arch_reg(dest_arch_reg)
    );


    //////////////////////////////////////////////////
    //                                              //
    //                  DISPATCH                    //
    //                                              //
    //////////////////////////////////////////////////

    Dispatch_sva dispatch_instance (
        .clock(clock),
        .reset(reset),
        // ------------ FROM INST BUFFER ------------- //
        .inst_buffer_instructions_valid(inst_buffer_outputs_valid),
        // ------------ FROM DECODER ------------- //
        .decoder_out(decoder_out),
        .is_rs1_used(is_rs1_used),
        .is_rs2_used(is_rs2_used),
        .source1_arch_reg(source1_arch_reg),
        .source2_arch_reg(source2_arch_reg),
        .dest_arch_reg(dest_arch_reg),
        // ------------ TO/FROM BRANCH STACK ------------- //
        .map_table_restore(map_table_restore),
        .restore_valid(restore_valid),
        .b_mask_combinational(b_mask_combinational),
        .branch_stack_entries(branch_stack_entries),
        .next_b_mask(next_b_mask),
        // ------------ TO/FROM ROB ------------- //
        .rob_tail(rob_tail),
        .rob_spots(rob_spots),
        .rob_entries(rob_entries),
        // ------------ TO/FROM RS ------------- // 
        .rs_spots(rs_spots),
        .rs_entries(rs_entries),
        // ------------ TO/FROM FREDDY LIST ------------- //
        .next_complete_list(next_complete_list),
        .regs_to_use(regs_to_use),
        .free_list_copy(free_list),
        .updated_free_list(updated_free_list),
        // ------------ FROM EXECUTE ------------- //
        .cdb_completing(cdb_completing),
        // ------------ TO ALL DATA STRUCTURES ------------- //
        .num_dispatched(num_dispatched)
        `ifdef DEBUG
            , .dispatch_debug(dispatch_debug)
        `endif
    );



    //////////////////////////////////////////////////
    //                                              //
    //                  ISSUE                       //
    //                                              //
    //////////////////////////////////////////////////
    
   

    Issue issue_instance (
        .clock(clock),
        .reset(reset),
        // ------------- FROM FREDDY -------------- //
        .complete_list(complete_list),

        // ------------- TO/FROM RS -------------- //
        .rs_data(rs_data),
        .rs_valid_next(rs_valid_next),
        .rs_data_issuing(rs_data_issuing),
        // ------------- TO/FROM REGFILE -------------- //
        .issue_alu_read_data_1(issue_alu_read_data_1),
        .issue_alu_read_data_2(issue_alu_read_data_2),
        .issue_mult_read_data_1(issue_mult_read_data_1),
        .issue_mult_read_data_2(issue_mult_read_data_2),
        .issue_branch_read_data_1(issue_branch_read_data_1),
        .issue_branch_read_data_2(issue_branch_read_data_2),
        .issue_alu_regs_reading_1(issue_alu_regs_reading_1),
        .issue_alu_regs_reading_2(issue_alu_regs_reading_2),
        .issue_mult_regs_reading_1(issue_mult_regs_reading_1),
        .issue_mult_regs_reading_2(issue_mult_regs_reading_2),
        .issue_branch_regs_reading_1(issue_branch_regs_reading_1),
        .issue_branch_regs_reading_2(issue_branch_regs_reading_2),
         // ------------- FROM CDB -------------- //
        .cdb_reg(cdb_reg),
        // ------------- TO/FROM EXECUTE -------------- //
        .mult_free(mult_free),
        .ldst_free(ldst_free),
        .mult_cdb_req(mult_cdb_valid),
        .ldst_cdb_req(ldst_cdb_valid),
        .mult_cdb_gnt(mult_cdb_gnt),
        .ldst_cdb_gnt(ldst_cdb_gnt),
        .alu_packets(alu_packets),
        .mult_packets(mult_packets),
        .branch_packets(branch_packets),
        .ldst_packets(ldst_packets),
        .complete_gnt_bus(complete_gnt_bus)
    );
    
    //////////////////////////////////////////////////
    //                                              //
    //                  EXECUTE                     //
    //                                              //
    //////////////////////////////////////////////////

    ExecuteStage execute_instance (
        .clock(clock),
        .reset(reset),
        .mult_packets_issuing_in(mult_packets),
        .alu_packets_issuing_in(alu_packets),
        .branch_packets_issuing_in(branch_packets),
        .mult_cdb_en(mult_cdb_gnt),
        .ldst_cdb_en(ldst_cdb_gnt),
        .complete_gnt_bus(complete_gnt_bus),
        .mult_free(mult_free),
        .ldst_free(ldst_free),
        .mult_cdb_valid(mult_cdb_valid),
        .ldst_cdb_valid(ldst_cdb_valid),
        .cdb_completing(cdb_completing),
        .cdb_reg(cdb_reg),
        .b_mm_resolve(b_mm_out),
        .b_mm_mispred(restore_valid),
        .branch_reg(branch_reg)
    );

    //////////////////////////////////////////////////
    //                                              //
    //                  RETIRE                      //
    //                                              //
    //////////////////////////////////////////////////

    retire retire_instance (
        .clock(clock),
        .reset(reset),
        // ------------- TO/FROM ROB -------------- //
        .rob_outputs(rob_outputs),
        .rob_outputs_valid(rob_outputs_valid),
        .num_retiring(num_retiring),
        // ------------- TO/FROM FREDDYLIST -------------- //
        .complete_list_exposed(complete_list),
        .phys_regs_retiring(phys_regs_retiring),
        // ------------- TO CPU -------------- //
        .committed_insts(committed_insts),
        //---------------- FROM/TO REGFILE ---------------------------//
        .retire_phys_regs_reading(retire_phys_regs_reading),
        .retire_read_data(retire_read_data)
    );

    //////////////////////////////////////////////////
    //                                              //
    //               Pipeline Outputs               //
    //                                              //
    //////////////////////////////////////////////////

    // Output the committed instruction to the testbench for counting
    // assign committed_insts[0] = wb_packet;

endmodule // pipeline
