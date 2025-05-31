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

module cpu (
    input clock, // System clock
    input reset, // System reset

    
    input MEM_TAG   mem2proc_transaction_tag, // Memory tag for current transaction
    input MEM_BLOCK mem2proc_data,            // Data coming back from memory
    input MEM_TAG   mem2proc_data_tag,        // Tag for which transaction data is for

    output MEM_COMMAND proc2mem_command, // Command sent to memory
    output ADDR        proc2mem_addr,    // Address sent to memory
    output MEM_BLOCK   proc2mem_data,     // Data sent to memory
    `ifndef CACHE_MODE
    output MEM_SIZE    proc2mem_size,    // Data size sent to memory
    `endif

    // Note: these are assigned at the very bottom of the module
    // input  INST          [`N-1:0] inst,
    output COMMIT_PACKET [`N-1:0] committed_insts
    // output ADDR          [`N-1:0] PCs_out,

    // Debug outputs: these signals are solely used for debugging in testbenches
    // Do not change for project 3
    // You should definitely change these for project 4
`ifdef DEBUG
    , output logic [`DCACHE_LINES-1:0][$bits(MEM_BLOCK)-1:0] debug_mem_data_dcache,
    output logic [`VCACHE_LINES-1:0][$bits(MEM_BLOCK)-1:0] debug_mem_data_vcache,
    output DCACHE_META_DATA [`DCACHE_NUM_SETS-1:0] [`DCACHE_NUM_WAYS-1:0] debug_dcache_meta_data,
    output VCACHE_META_DATA                           [`VCACHE_LINES-1:0] debug_vcache_meta_data, 
    output MSHR_IDX                                                       debug_mshr_true_head,
    output logic                             [`MSHR_NUM_ENTRIES_BITS-1:0] debug_mshr_spots,
    output DCACHE_MSHR_ENTRY                               [`MSHR_SZ-1:0] debug_mshrs,
    output WB_IDX                                                         debug_wb_head,
    output logic                               [`WB_NUM_ENTRIES_BITS-1:0] debug_wb_spots,
    output WB_ENTRY                                       [`WB_LINES-1:0] debug_wb_buffer,
    output SQ_POINTER                                                     debug_sq_true_head, 
    output SQ_POINTER                                                     debug_sq_head,
    output logic                               [`SQ_NUM_ENTRIES_BITS-1:0] debug_store_buffer_entries,
    output STORE_QUEUE_PACKET                                [`SQ_SZ-1:0] debug_store_queue
`endif

);

    // ONLY OUTPUTS ARE UNCOMMENTED

    /*------- ROB WIRES ----------*/

    logic  [`NUM_SCALAR_BITS-1:0] rob_spots;
    logic      [`ROB_SZ_BITS-1:0] rob_tail;
    ROB_PACKET           [`N-1:0] rob_outputs;
    logic  [`NUM_SCALAR_BITS-1:0] rob_outputs_valid;

`ifdef DEBUG
    ROB_DEBUG                   rob_debug;
`endif

    /*------- RS WIRES ----------*/

    logic [`NUM_SCALAR_BITS-1:0] rs_spots;
    RS_PACKET       [`RS_SZ-1:0] rs_data_next;              // The entire RS data 
    logic           [`RS_SZ-1:0] rs_valid_issue;        // 1 if RS data is valid <-- Coded

`ifdef DEBUG
    RS_DEBUG               rs_debug;
`endif


    /*------- FREDDYLIST WIRES ----------*/  
    
    PHYS_REG_IDX           [`N-1:0] phys_reg_completing; // decoded signal from cdb_reg
    logic                  [`N-1:0] completing_valid; // decoded signal from cdb_reg

    PHYS_REG_IDX           [`N-1:0] regs_to_use;       // physical register indices for dispatch to use
    logic   [`PHYS_REG_SZ_R10K-1:0] free_list;              // bitvector of the phys reg that are complete

    logic   [`PHYS_REG_SZ_R10K-1:0] next_complete_list;          // bitvector of the phys reg that are complete
    logic   [`PHYS_REG_SZ_R10K-1:0] complete_list;
    

    /*------- BRANCH STACK WIRES ----------*/
    logic                                restore_valid;
    ADDR                                 PC_restore;
    logic             [`ROB_SZ_BITS-1:0] rob_tail_restore;
    logic        [`PHYS_REG_SZ_R10K-1:0] free_list_restore;
    PHYS_REG_IDX [`ARCH_REG_SZ_R10K-1:0] map_table_restore;     
    B_MASK                               b_mask_combinational;
    B_MASK                               b_mm_out;
    BRANCH_PREDICTOR_PACKET              bs_bp_packet;
    logic                                resolving_valid_branch;
    logic                                resolving_valid;
    ADDR                                 resolving_target_PC;
    ADDR                                 resolving_branch_PC;
    SQ_POINTER                           sq_tail_restore;
    SQ_MASK                              sq_mask_restore;
    
    `ifdef DEBUG
    BS_DEBUG                             bs_debug;
    `endif

    /*------- BRANCH PREDICTOR WIRES ----------*/
    BRANCH_PREDICTOR_PACKET  [`N-1:0]   bp_packets;
    logic                    [`N-1:0]   branches_taken;
    logic                               actual_taken;
    logic                               mispred;
    `ifdef DEBUG
    BP_DEBUG                            bp_debug;
    `endif

    /*------- BTB WIRES ----------*/
    ADDR                     [`N-1:0] target_PCs;
    logic                    [`N-1:0] btb_hits;
    `ifdef DEBUG
    BTB_DEBUG                         btb_debug;
    `endif
    
    /*------- REGFILE WIRES ----------*/
    DATA        [`N-1:0] retire_read_data;
    DATA        [`NUM_FU_ALU-1:0] issue_alu_read_data_1;
    DATA        [`NUM_FU_ALU-1:0] issue_alu_read_data_2;
    DATA        [`NUM_FU_BRANCH-1:0] issue_branch_read_data_1;
    DATA        [`NUM_FU_BRANCH-1:0] issue_branch_read_data_2;
    DATA        [`NUM_FU_MULT-1:0] issue_mult_read_data_1;
    DATA        [`NUM_FU_MULT-1:0] issue_mult_read_data_2;                   
    DATA        [`NUM_FU_LOAD-1:0] issue_load_read_data_1;
    DATA       [`NUM_FU_STORE-1:0] issue_store_read_data_1;
    DATA       [`NUM_FU_STORE-1:0] issue_store_read_data_2;

    /*------- FETCH WIRES ----------*/  
    FETCH_PACKET         [`N-1:0] inst_buffer_inputs;   //instructions going to instruction buffer
    logic  [`NUM_SCALAR_BITS-1:0] inst_valid;
    logic [`N-1:0]       [`N-1:0] branch_gnt_bus;
    logic                [`N-1:0] final_branch_gnt_line;
    logic                         no_branches_fetched;
    ADDR                 [`N-1:0] PCs_out;

    /*------- INST BUFFER WIRES ----------*/    
    logic  [`NUM_SCALAR_BITS-1:0] inst_buffer_spots;
    FETCH_PACKET         [`N-1:0] inst_buffer_outputs;   
    logic  [`NUM_SCALAR_BITS-1:0] inst_buffer_outputs_valid;


    /*------- DECODER WIRES ----------*/
    FETCH_PACKET  [`N-1:0] inst_buffer_input;
    DECODE_PACKET [`N-1:0] decoder_out;
    logic         [`N-1:0] is_rs1_used;
    logic         [`N-1:0] is_rs2_used;
    ARCH_REG_IDX  [`N-1:0] source1_arch_reg;
    ARCH_REG_IDX  [`N-1:0] source2_arch_reg;
    ARCH_REG_IDX  [`N-1:0] dest_arch_reg;

    /*------- DISPATCH WIRES ----------*/

    BS_ENTRY_PACKET [`B_MASK_WIDTH-1:0] branch_stack_entries;
    B_MASK                              next_b_mask;
    ROB_PACKET                 [`N-1:0] rob_entries;
    RS_PACKET                  [`N-1:0] rs_entries;
    logic       [`PHYS_REG_SZ_R10K-1:0] updated_free_list;
    logic        [`NUM_SCALAR_BITS-1:0] num_dispatched;
    SQ_MASK                             dispatch_sq_mask;
    logic        [`NUM_SCALAR_BITS-1:0] stores_dispatching;
    `ifdef DEBUG
        DISPATCH_DEBUG                  dispatch_debug;
    `endif

    /*------- ISSUE WIRES ----------*/

    logic                  [`RS_SZ-1:0] rs_data_issuing;     // set index to 1 when a rs_data is selected to be issued
    PHYS_REG_IDX      [`NUM_FU_ALU-1:0] issue_alu_regs_reading_1;
    PHYS_REG_IDX      [`NUM_FU_ALU-1:0] issue_alu_regs_reading_2;
    PHYS_REG_IDX     [`NUM_FU_MULT-1:0] issue_mult_regs_reading_1;
    PHYS_REG_IDX     [`NUM_FU_MULT-1:0] issue_mult_regs_reading_2;
    PHYS_REG_IDX   [`NUM_FU_BRANCH-1:0] issue_branch_regs_reading_1;
    PHYS_REG_IDX   [`NUM_FU_BRANCH-1:0] issue_branch_regs_reading_2;
    PHYS_REG_IDX     [`NUM_FU_LOAD-1:0] issue_load_regs_reading_1;
    PHYS_REG_IDX    [`NUM_FU_STORE-1:0] issue_store_regs_reading_1;
    PHYS_REG_IDX    [`NUM_FU_STORE-1:0] issue_store_regs_reading_2;
    logic            [`NUM_FU_MULT-1:0] mult_cdb_gnt;
    logic            [`LOAD_BUFFER_SZ-1:0] load_cdb_gnt;
    ALU_PACKET        [`NUM_FU_ALU-1:0] alu_packets;
    MULT_PACKET      [`NUM_FU_MULT-1:0] mult_packets;
    BRANCH_PACKET  [`NUM_FU_BRANCH-1:0] branch_packets;
    LOAD_ADDR_PACKET      [`NUM_FU_LOAD-1:0] load_addr_packets;
    logic [`N-1:0]  [`NUM_FU_TOTAL-1:0] complete_gnt_bus;
    STORE_ADDR_PACKET     [`NUM_FU_STORE-1:0] store_addr_packets;
    
    /*----------EXECUTE WIRES -------------*/
    logic              [`NUM_FU_MULT-1:0] mult_free;
    logic              [`NUM_FU_LOAD-1:0] load_free;
    CDB_ETB_PACKET               [`N-1:0] cdb_completing;
    CDB_REG_PACKET               [`N-1:0] cdb_reg;
    CDB_REG_PACKET               [`N-1:0] next_cdb_reg;
    BRANCH_REG_PACKET                     branch_reg;
    logic              [`NUM_FU_MULT-1:0] mult_cdb_valid;
    logic              [`LOAD_BUFFER_SZ-1:0] load_cdb_valid;
    ADDR                                  load_req_addr;
    logic                                 load_req_valid;
    logic                                 load_valid;
    SQ_POINTER                            load_sq_tail;

    always_comb begin
        for (int i = 0; i < `N; ++i) begin
            phys_reg_completing[i] = cdb_reg[i].completing_reg; // decoding cdb_reg for freddylist
            completing_valid[i] = cdb_reg[i].valid; // decoding cdb_reg for freddylist
        end
    end

    always_comb begin
        mispred = branch_reg.bm_mispred; //decoding mispred for branch predictor
        actual_taken = branch_reg.actual_taken; //decoding taken for branch predictor
    end

    /*------- STORE ADDR STAGE WIRES ------ */
    SQ_MASK                     resolving_sq_mask;
    STORE_QUEUE_PACKET          sq_packet;

    /*------- STORE QUEUE WIRES ------ */
    logic        [`NUM_SQ_BITS-1:0] sq_spots;
    SQ_POINTER                      sq_tail;
    SQ_MASK                         sq_mask_combinational;
    DATA                             sq_load_data;
    BYTE_MASK                        sq_data_mask;
    logic                            store_req_valid;
    DATA                             store_req_data; 
    ADDR                             store_req_addr;
    BYTE_MASK                        store_req_byte_mask;

    /*------- RETIRE WIRES ----------*/

    logic [`NUM_SCALAR_BITS-1:0] num_retiring;
    PHYS_REG_IDX [`N-1:0] phys_regs_retiring;
    PHYS_REG_IDX [`N-1:0] retire_phys_regs_reading;
    logic  [`NUM_SCALAR_BITS-1:0] num_store_retiring;

    /*----------- DCACHE ---------------*/
    LOAD_DATA_CACHE_PACKET           load_data_cache_packet;        
    LOAD_BUFFER_CACHE_PACKET         load_buffer_cache_packet;
    logic                            store_req_accepted;
    MEM_REQ_PACKET                   dcache_mem_req_packet;

    /*----------- ICACHE ---------------*/
    DATA                  [`N-1:0] cache_data; //instructions being sent to Fetch
    logic                 [`N-1:0] cache_miss;
    MEM_REQ_PACKET                 icache_mem_req_packet;

    /*----------- MEM ARBITER ---------------*/
    logic                             dcache_mem_req_accepted;
    logic                             icache_mem_req_accepte;
    MEM_TAG                           mem_trxn_tag;
    MEM_DATA_PACKET                   mem_data_packet;
          


    //////////////////////////////////////////////////
    //                                              //
    //               DATA STRUCTURES                //
    //                                              //
    //////////////////////////////////////////////////


    /*----------------Reorder Buffer----------------*/

    rob rob_instance (
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

    rs rs_instance (
        .clock             (clock),
        .reset             (reset),
        .num_dispatched    (num_dispatched),
        .rs_entries        (rs_entries), 
        .rs_spots          (rs_spots),
        .ETB_tags          (cdb_completing),
        .resolving_sq_mask (resolving_sq_mask),
        .rs_data_issuing   (rs_data_issuing),
        .rs_data_next      (rs_data_next),
        .rs_valid_issue    (rs_valid_issue),
        .b_mm_resolve      (b_mm_out),
        .b_mm_mispred      (restore_valid)
    `ifdef DEBUG
        ,.rs_debug          (rs_debug)
    `endif
    );


    /*-------------Freddy List--------------------*/

    freddylist fl_instance (
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
        .complete_list          (complete_list),
        .store_reg_completing   (sq_packet.dest_reg_idx),
        .store_valid            (sq_packet.valid)
    );


    /*-------------Branch Stack--------------------*/

    branchstack bs_instance (
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
        .b_mm_out               (b_mm_out), 
        .bs_bp_packet           (bs_bp_packet),
        .resolving_valid_branch (resolving_valid_branch),
        .resolving_valid        (resolving_valid),
        .resolving_target_PC    (resolving_target_PC),
        .resolving_branch_PC    (resolving_branch_PC),
        .sq_mask_resolving      (resolving_sq_mask),
        .sq_tail_restore        (sq_tail_restore),
        .sq_mask_restore        (sq_mask_restore)
        `ifdef DEBUG
        , .bs_debug(bs_debug)
        `endif
    );

    /*-------------Branch Predictor--------------------*/

    branchpredictor bp_instance (
        .clock(clock), 
        .reset(reset),
        .PCs_out(PCs_out),
        .branch_gnt_bus(branch_gnt_bus),
        .final_branch_gnt_line(final_branch_gnt_line),
        .no_branches_fetched(no_branches_fetched),
        .btb_hits(btb_hits),
        .bp_packets(bp_packets),
        .branches_taken(branches_taken),
        .bs_bp_packet(bs_bp_packet),
        .resolving_valid_branch(resolving_valid_branch),
        .actual_taken(actual_taken),                                       
        .mispred(mispred)                        
`ifdef DEBUG
    , .bp_debug(bp_debug) //define BP_DEBUG later sys defs
`endif
    );


    /*----------------- BTB ------------------*/
    btb btb_instance (
        .clock(clock),
        .reset(reset),
        .PCs(PCs_out),
        .target_PCs(target_PCs),
        .btb_hits(btb_hits),
        .resolving_valid(resolving_valid), //need branch stack to add these
        .resolving_target_PC(resolving_target_PC),
        .resolving_branch_PC(resolving_branch_PC)
        `ifdef DEBUG
        , .btb_debug(btb_debug)
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
        .issue_load_regs_reading_1(issue_load_regs_reading_1),
        .issue_load_read_data_1(issue_load_read_data_1),
        .issue_store_regs_reading_1(issue_store_regs_reading_1),
        .issue_store_regs_reading_2(issue_store_regs_reading_2),
        .issue_store_read_data_1(issue_store_read_data_1),
        .issue_store_read_data_2(issue_store_read_data_2),
        .cdb_reg(cdb_reg)
    );

    /*------------------ Inst Buffer --------------------*/

    instbuffer inst_buffer_instance (
        .clock                      (clock), 
        .reset                      (reset),

        // ------------ TO/FROM FETCH ------------- //
        .inst_buffer_inputs         (inst_buffer_inputs),
        .inst_valid                 (inst_valid), //number of valid instructions fetch sends to instruction buffer     // New instructions from Dispatch, MUST BE IN ORDER FROM OLDEST TO NEWEST INSTRUCTIONS
        .inst_buffer_spots          (inst_buffer_spots),

        // ------------ FROM EXECUTE ------------- //
        .restore_valid              (restore_valid),

        // ------------ TO/FROM DISPATCH -------- //
        .num_dispatched             (num_dispatched),     //number of spots available in dispatch
        .inst_buffer_outputs        (inst_buffer_outputs),   // For retire to check eligibility
        .inst_buffer_outputs_valid  (inst_buffer_outputs_valid) // If not all N FB entries are valid entries they should not be considered 
    );

    /*------------------ Store Queue --------------------*/

    store_queue store_queue_instance (
        .reset(reset),
        .clock(clock),
        .sq_packet(sq_packet),
        .resolving_sq_mask(resolving_sq_mask),                    
        .stores_dispatching(stores_dispatching),
        .dispatch_sq_mask(dispatch_sq_mask),
        .sq_spots(sq_spots),
        .sq_tail(sq_tail),
        .sq_mask_combinational(sq_mask_combinational),
        .load_sq_tail(load_sq_tail),
        .load_req_addr(load_req_addr),
        .sq_load_data(sq_load_data),
        .sq_data_mask(sq_data_mask),
        .sq_restore_valid(restore_valid),
        .sq_tail_restore(sq_tail_restore),
        .sq_mask_restore(sq_mask_restore),
        .store_req_accepted(store_req_accepted),
        .store_req_valid(store_req_valid),
        .store_req_data(store_req_data), 
        .store_req_addr(store_req_addr),
        .store_req_byte_mask(store_req_byte_mask),        
        .num_store_retiring(num_store_retiring)
    `ifdef DEBUG
        , .debug_sq_true_head(debug_sq_true_head),
        .debug_sq_head(debug_sq_head),
        .debug_store_buffer_entries(debug_store_buffer_entries),
        .debug_store_queue(debug_store_queue)
    `endif
    );

    dcache dcache_instance (
        .clock(clock),
        .reset(reset),
        .load_req_valid(load_req_valid),
        .load_req_addr(load_req_addr),
        .load_data_cache_packet(load_data_cache_packet),
        .load_buffer_cache_packet(load_buffer_cache_packet),
        .store_req_valid(store_req_valid),
        .store_req_addr(store_req_addr),
        .store_req_data(store_req_data),
        .store_req_byte_mask(store_req_byte_mask),
        .store_req_accepted(store_req_accepted),
        .dcache_mem_req_accepted(dcache_mem_req_accepted),
        .dcache_mem_trxn_tag(mem_trxn_tag),
        .mem_data_packet(mem_data_packet),                  //NEED TO INSTANTIATE MEM DATA PACKET 
        .dcache_mem_req_packet(dcache_mem_req_packet)
    `ifdef DEBUG
        , .debug_mem_data_dcache(debug_mem_data_dcache),
        .debug_mem_data_vcache(debug_mem_data_vcache),
        .debug_dcache_meta_data(debug_dcache_meta_data),
        .debug_vcache_meta_data(debug_vcache_meta_data),
        .debug_mshr_true_head(debug_mshr_true_head),
        .debug_mshr_spots(debug_mshr_spots),
        .debug_mshrs(debug_mshrs),
        .debug_wb_head(debug_wb_head),
        .debug_wb_spots(debug_wb_spots),
        .debug_wb_buffer(debug_wb_buffer)
    `endif
    );


    icache icache_instance (
        .clock(clock),
        .reset(reset),
        .PCs_out(PCs_out),
        .cache_data(cache_data), 
        .cache_miss(cache_miss),
        .icache_mem_req_accepted(icache_mem_req_accepted),
        .icache_mem_trxn_tag(mem_trxn_tag),
        .mem_data_packet(mem_data_packet),
        .icache_mem_req_packet(icache_mem_req_packet), 
        .restore_valid(restore_valid)
    );

    memarbiter memarbiter_instance (
        .clock(clock),
        .reset(reset),
        .dcache_mem_req_packet(dcache_mem_req_packet),
        .dcache_mem_req_accepted(dcache_mem_req_accepted),
        .icache_mem_req_packet(icache_mem_req_packet),
        .icache_mem_req_accepted(icache_mem_req_accepted),
        .mem_trxn_tag(mem_trxn_tag),
        .mem_data_packet(mem_data_packet),
        .mem2proc_transaction_tag(mem2proc_transaction_tag),
        .mem2proc_data(mem2proc_data),
        .mem2proc_data_tag(mem2proc_data_tag),
        .proc2mem_addr(proc2mem_addr),
        .proc2mem_data(proc2mem_data),
        .proc2mem_command(proc2mem_command)
    );

    // mem main_memory (
    //     .clock(clock),         
    //     .proc2mem_addr(proc2mem_addr),             
    //     .proc2mem_data(proc2mem_data),
    //     `ifndef CACHE_MODE
    //     .proc2mem_size(proc2mem_size),
    //     `endif
    //     .proc2mem_command(proc2mem_command),
    //     .mem2proc_transaction_tag(mem2proc_transaction_tag), // Memory tag for current transaction (0 = can't accept)
    //     .mem2proc_data(mem2proc_data),            // Data for a load
    //     .mem2proc_data_tag(mem2proc_data_tag)         // Tag for finished transactions (0 = no value)
    // );
    

    //////////////////////////////////////////////////
    //                                              //
    //                  FETCH                       //
    //                                              //
    //////////////////////////////////////////////////

    Fetch fetch_stage(
        .clock(clock), 
        .reset(reset),
        .PCs_out(PCs_out),
        .cache_data(cache_data),
        .cache_miss(cache_miss),
        .PC_restore(PC_restore),  // Retire module tells the ROB how many entries can be cleared
        .restore_valid(restore_valid),
        .inst_buffer_spots(inst_buffer_spots),     //number of spots in instruction buffer
        .inst_buffer_inputs(inst_buffer_inputs),   //instructions going to instruction buffer
        .inst_valid(inst_valid), //number of valid instructions fetch sends to instruction buffer   
        .bp_packets(bp_packets),
        .branches_taken(branches_taken),
        .branch_gnt_bus(branch_gnt_bus),
        .final_branch_gnt_line(final_branch_gnt_line),
        .no_branches_fetched(no_branches_fetched),
        .target_PCs(target_PCs),       //<-- just set this somewhere?
        .btb_hits(btb_hits)
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

    Dispatch dispatch_instance (
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
        // ------------ TO/FROM SQ ------------- // 
        .sq_spots(sq_spots),
        .sq_tail(sq_tail),
        .sq_mask_combinational(sq_mask_combinational),
        .dispatch_sq_mask(dispatch_sq_mask),
        .stores_dispatching(stores_dispatching),
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
        .rs_data_next(rs_data_next),
        .rs_valid_issue(rs_valid_issue),
        .rs_data_issuing(rs_data_issuing),
        // ------------- TO/FROM REGFILE -------------- //
        .issue_alu_read_data_1(issue_alu_read_data_1),
        .issue_alu_read_data_2(issue_alu_read_data_2),
        .issue_mult_read_data_1(issue_mult_read_data_1),
        .issue_mult_read_data_2(issue_mult_read_data_2),
        .issue_branch_read_data_1(issue_branch_read_data_1),
        .issue_branch_read_data_2(issue_branch_read_data_2),
        .issue_load_read_data_1(issue_load_read_data_1),
        .issue_store_read_data_1(issue_store_read_data_1),
        .issue_store_read_data_2(issue_store_read_data_2),
        .issue_alu_regs_reading_1(issue_alu_regs_reading_1),
        .issue_alu_regs_reading_2(issue_alu_regs_reading_2),
        .issue_mult_regs_reading_1(issue_mult_regs_reading_1),
        .issue_mult_regs_reading_2(issue_mult_regs_reading_2),
        .issue_branch_regs_reading_1(issue_branch_regs_reading_1),
        .issue_branch_regs_reading_2(issue_branch_regs_reading_2),
        .issue_load_regs_reading_1(issue_load_regs_reading_1),
        .issue_store_regs_reading_1(issue_store_regs_reading_1),
        .issue_store_regs_reading_2(issue_store_regs_reading_2),
         // ------------- FROM CDB -------------- //
        .cdb_reg(cdb_reg),
        .next_cdb_reg(next_cdb_reg),
        // ------------- TO/FROM EXECUTE -------------- //
        .mult_free(mult_free),
        .load_free(load_free),
        .mult_cdb_req(mult_cdb_valid),
        .load_cdb_req(load_cdb_valid),
        .mult_cdb_gnt(mult_cdb_gnt),
        .load_cdb_gnt(load_cdb_gnt),
        .alu_packets(alu_packets),
        .mult_packets(mult_packets),
        .branch_packets(branch_packets),
        .load_addr_packets(load_addr_packets),
        .complete_gnt_bus(complete_gnt_bus),
        .store_addr_packets(store_addr_packets)
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
        .load_packets_issuing_in(load_addr_packets),
        .mult_cdb_gnt(mult_cdb_gnt),
        .load_cdb_gnt(load_cdb_gnt),
        .complete_gnt_bus(complete_gnt_bus),
        .mult_free(mult_free),
        .load_free(load_free),
        .mult_cdb_valid(mult_cdb_valid),
        .load_cdb_valid(load_cdb_valid),
        .cdb_completing(cdb_completing),
        .cdb_reg(cdb_reg),
        .next_cdb_reg(next_cdb_reg),
        .b_mm_resolve(b_mm_out),
        .b_mm_mispred(restore_valid),
        .branch_reg(branch_reg),
        .load_data_cache_packet(load_data_cache_packet),
        .load_buffer_cache_packet(load_buffer_cache_packet),
        .load_req_addr(load_req_addr),
        .load_req_valid(load_req_valid),
        .sq_load_data(sq_load_data),
        .sq_data_mask(sq_data_mask),
        .load_sq_tail(load_sq_tail)
    );

    store_addr_stage sas_instance (
        .clock(clock),
        .reset(reset),
        .store_addr_packet_in(store_addr_packets),
        .resolving_sq_mask(resolving_sq_mask),
        .sq_packet(sq_packet)
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
        // ------------- TO SQ -------------- //
        .num_store_retiring(num_store_retiring),
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
