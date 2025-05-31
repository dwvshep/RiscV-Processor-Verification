/////////////////////////////////////////////////////////////////////////
//                                                                     //
//  Modulename :  cpu_test.sv                                          //
//                                                                     //
//  Description :  Testbench module for the VeriSimpleV processor.     //
//                                                                     //
/////////////////////////////////////////////////////////////////////////

`include "verilog/sys_defs.svh"
//`include "test/branchstack_sva.svh"
//`include "test/issue_sva.svh"
`include "test/rob_sva.svh"
`include "test/rs_sva.svh"
`include "test/freddylist_sva.svh"
//`include "test/dispatch_sva.svh"

// P4 TODO: Add your own debugging framework. Basic printing of data structures
//          is an absolute necessity for the project. You can use C functions 
//          like in test/pipeline_print.c or just do everything in verilog.
//          Be careful about running out of space on CAEN printing lots of state
//          for longer programs (alexnet, outer_product, etc.)

// These link to the pipeline_print.c file in this directory, and are used below to print
// detailed output to the pipeline_output_file, initialized by open_pipeline_output_file()
import "DPI-C" function string decode_inst(int inst);
//import "DPI-C" function void open_pipeline_output_file(string file_name);
//import "DPI-C" function void print_header();
//import "DPI-C" function void print_cycles(int clock_count);
//import "DPI-C" function void print_stage(int inst, int npc, int valid_inst);
//import "DPI-C" function void print_reg(int wb_data, int wb_idx, int wb_en);
//import "DPI-C" function void print_membus(int proc2mem_command, int proc2mem_addr,
//                                          int proc2mem_data_hi, int proc2mem_data_lo);
//import "DPI-C" function void close_pipeline_output_file();


`define TB_MAX_CYCLES 50000000
`define DEBUG
// `define SIM


module testbench;
    // string inputs for loading memory and output files
    // run like: cd build && ./simv +MEMORY=../programs/mem/<my_program>.mem +OUTPUT=../output/<my_program>
    // this testbench will generate 4 output files based on the output
    // named OUTPUT.{out cpi, wb, ppln} for the memory, cpi, writeback, and pipeline outputs.
    string program_memory_file, output_name;
    string out_outfile, cpi_outfile, writeback_outfile;//, pipeline_outfile;
    int out_fileno, cpi_fileno, wb_fileno; // verilog uses integer file handles with $fopen and $fclose

    // variables used in the testbench
    logic        clock;
    logic        reset;
    
    logic [31:0] clock_count; // also used for terminating infinite loops
    logic [31:0] instr_count;

    
    MEM_COMMAND proc2mem_command;
    ADDR        proc2mem_addr;
    MEM_BLOCK   proc2mem_data;
    MEM_TAG     mem2proc_transaction_tag;
    MEM_BLOCK   mem2proc_data;
    MEM_TAG     mem2proc_data_tag;
    MEM_SIZE    proc2mem_size;
    
    EXCEPTION_CODE error_status = NO_ERROR;

    // ADDR  if_NPC_dbg;
    // DATA  if_inst_dbg;
    // logic if_valid_dbg;
    // ADDR  if_id_NPC_dbg;
    // DATA  if_id_inst_dbg;
    // logic if_id_valid_dbg;
    // ADDR  id_ex_NPC_dbg;
    // DATA  id_ex_inst_dbg;
    // logic id_ex_valid_dbg;
    // ADDR  ex_mem_NPC_dbg;
    // DATA  ex_mem_inst_dbg;
    // logic ex_mem_valid_dbg;
    // ADDR  mem_wb_NPC_dbg;
    // DATA  mem_wb_inst_dbg;
    // logic mem_wb_valid_dbg;
    
    // INST          [`N-1:0] insts;
    // ADDR          [`N-1:0] PCs;
    COMMIT_PACKET [`N-1:0] committed_insts;

//     logic  [`NUM_SCALAR_BITS-1:0] rob_spots;
//     logic      [`ROB_SZ_BITS-1:0] rob_tail;
//     ROB_PACKET           [`N-1:0] rob_outputs;
//     logic  [`NUM_SCALAR_BITS-1:0] rob_outputs_valid;

// `ifdef DEBUG
//     ROB_DEBUG                   rob_debug;
// `endif

//     /*------- RS WIRES ----------*/

//     logic  [`NUM_SCALAR_BITS-1:0] rs_spots;
//     RS_PACKET       [`RS_SZ-1:0] rs_data;              // The entire RS data 
//     logic           [`RS_SZ-1:0] rs_valid_next;        // 1 if RS data is valid <-- Coded

// `ifdef DEBUG
//     RS_DEBUG               rs_debug;
// `endif


//     /*------- FREDDYLIST WIRES ----------*/  
    
//     PHYS_REG_IDX           [`N-1:0] phys_reg_completing; // decoded signal from cdb_reg
//     logic                  [`N-1:0] completing_valid; // decoded signal from cdb_reg

//     PHYS_REG_IDX           [`N-1:0] regs_to_use;       // physical register indices for dispatch to use
//     logic   [`PHYS_REG_SZ_R10K-1:0] free_list;              // bitvector of the phys reg that are complete

//     logic   [`PHYS_REG_SZ_R10K-1:0] next_complete_list;          // bitvector of the phys reg that are complete
//     logic   [`PHYS_REG_SZ_R10K-1:0] complete_list;
    

//     /*------- BRANCH STACK WIRES ----------*/
//     logic                                restore_valid;
//     ADDR                                 PC_restore;
//     logic             [`ROB_SZ_BITS-1:0] rob_tail_restore;
//     logic        [`PHYS_REG_SZ_R10K-1:0] free_list_restore;
//     PHYS_REG_IDX [`ARCH_REG_SZ_R10K-1:0] map_table_restore;     
//     B_MASK                               b_mask_combinational;
//     B_MASK                               b_mm_out;
//     `ifdef DEBUG
//     BS_DEBUG                             bs_debug;
//     `endif

//     /*------- REGFILE WIRES ----------*/
    
//     DATA        [`N-1:0] retire_read_data;
//     DATA        [`NUM_FU_ALU-1:0] issue_alu_read_data_1;
//     DATA        [`NUM_FU_ALU-1:0] issue_alu_read_data_2;
//     DATA        [`NUM_FU_BRANCH-1:0] issue_branch_read_data_1;
//     DATA        [`NUM_FU_BRANCH-1:0] issue_branch_read_data_2;
//     DATA        [`NUM_FU_MULT-1:0] issue_mult_read_data_1;
//     DATA        [`NUM_FU_MULT-1:0] issue_mult_read_data_2;

//     /*------- FETCH WIRES ----------*/  
//     FETCH_PACKET         [`N-1:0] inst_buffer_inputs;   //instructions going to instruction buffer
//     logic  [`NUM_SCALAR_BITS-1:0] instructions_valid;

//     /*------- FETCH BUFFER WIRES ----------*/    
//     logic  [`NUM_SCALAR_BITS-1:0] inst_buffer_spots;
//     FETCH_PACKET         [`N-1:0] inst_buffer_outputs;   
//     logic  [`NUM_SCALAR_BITS-1:0] inst_buffer_outputs_valid;


//     /*------- DECODER WIRES ----------*/
//     FETCH_PACKET  [`N-1:0] inst_buffer_input;
//     DECODE_PACKET [`N-1:0] decoder_out;
//     logic         [`N-1:0] is_rs1_used;
//     logic         [`N-1:0] is_rs2_used;
//     ARCH_REG_IDX  [`N-1:0] source1_arch_reg;
//     ARCH_REG_IDX  [`N-1:0] source2_arch_reg;
//     ARCH_REG_IDX  [`N-1:0] dest_arch_reg;

//     /*------- DISPATCH WIRES ----------*/

//     BS_ENTRY_PACKET [`B_MASK_WIDTH-1:0] branch_stack_entries;
//     B_MASK next_b_mask;
//     ROB_PACKET [`N-1:0] rob_entries;
//     RS_PACKET [`N-1:0] rs_entries;
//     logic [`PHYS_REG_SZ_R10K-1:0] updated_free_list;
//     logic [`NUM_SCALAR_BITS-1:0] num_dispatched;
//     `ifdef DEBUG
//         DISPATCH_DEBUG dispatch_debug;
//     `endif

//     /*------- ISSUE WIRES ----------*/

//     wor                    [`RS_SZ-1:0] rs_data_issuing;     // set index to 1 when a rs_data is selected to be issued
//     PHYS_REG_IDX      [`NUM_FU_ALU-1:0] issue_alu_regs_reading_1;
//     PHYS_REG_IDX      [`NUM_FU_ALU-1:0] issue_alu_regs_reading_2;
//     PHYS_REG_IDX     [`NUM_FU_MULT-1:0] issue_mult_regs_reading_1;
//     PHYS_REG_IDX     [`NUM_FU_MULT-1:0] issue_mult_regs_reading_2;
//     PHYS_REG_IDX   [`NUM_FU_BRANCH-1:0] issue_branch_regs_reading_1;
//     PHYS_REG_IDX   [`NUM_FU_BRANCH-1:0] issue_branch_regs_reading_2;
//     logic            [`NUM_FU_MULT-1:0] mult_cdb_gnt;
//     logic            [`NUM_FU_LDST-1:0] ldst_cdb_gnt;
//     ALU_PACKET        [`NUM_FU_ALU-1:0] alu_packets;
//     MULT_PACKET      [`NUM_FU_MULT-1:0] mult_packets;
//     BRANCH_PACKET  [`NUM_FU_BRANCH-1:0] branch_packets;
//     LDST_PACKET      [`NUM_FU_LDST-1:0] ldst_packets;
//     logic [`N-1:0]  [`NUM_FU_TOTAL-1:0] complete_gnt_bus;
    
//     /*----------EXECUTE WIRES -------------*/
//     logic              [`NUM_FU_MULT-1:0] mult_free;
//     logic              [`NUM_FU_LDST-1:0] ldst_free;
//     CDB_ETB_PACKET               [`N-1:0] cdb_completing;
//     CDB_REG_PACKET               [`N-1:0] cdb_reg;
//     BRANCH_REG_PACKET                     branch_reg;
//     logic              [`NUM_FU_MULT-1:0] mult_cdb_valid;
//     logic              [`NUM_FU_LDST-1:0] ldst_cdb_valid;

//     always_comb begin
//         for (int i = 0; i < `N; ++i) begin
//             phys_reg_completing[i] = cdb_reg[i].completing_reg; // decoding cdb_reg for freddylist
//             completing_valid[i] = cdb_reg[i].valid; // decoding cdb_reg for freddylist
//         end
//     end

//     /*------- RETIRE WIRES ----------*/

//     logic [`NUM_SCALAR_BITS-1:0] num_retiring;
//     PHYS_REG_IDX [`N-1:0] phys_regs_retiring;
//     PHYS_REG_IDX [`N-1:0] retire_phys_regs_reading;

    // UPDATED MEMORY
    DATA [1:0] updated_memory [`MEM_64BIT_LINES-1:0];

    localparam WIDTH = $bits(MEM_BLOCK);

    // DCACHE DATA EXPOSED
    logic [`DCACHE_LINES-1:0][WIDTH-1:0] dcache_info;
    DCACHE_META_DATA [`DCACHE_NUM_SETS-1:0] [`DCACHE_NUM_WAYS-1:0] dcache_meta_data;

    //VCACHE DATA EXPOSED
    logic [`VCACHE_LINES-1:0][WIDTH-1:0] vcache_info;
    VCACHE_META_DATA [`VCACHE_LINES-1:0] vcache_meta_data;

    //MSHRs DATA EXPOSED
    MSHR_IDX mshr_true_head;
    logic [`MSHR_NUM_ENTRIES_BITS-1:0] mshr_spots;
    DCACHE_MSHR_ENTRY [`MSHR_SZ-1:0] dcache_mshrs;

    //WB BUFFER DATA EXPOSED
    
    WB_IDX wb_head;
    logic [`WB_NUM_ENTRIES_BITS-1:0] wb_spots;
    WB_ENTRY [`WB_LINES-1:0] dcache_wb_buffer;

    // STORE BUFFER DATA EXPOSED
    SQ_POINTER sq_true_head, sq_head;
    logic [`SQ_NUM_ENTRIES_BITS-1:0] store_buffer_entries;
    STORE_QUEUE_PACKET [`SQ_SZ-1:0] store_queue;
    
    // Instantiate the Pipeline
    cpu verisimpleV (
        // Inputs
        .clock (clock),
        .reset (reset),
        
        .mem2proc_transaction_tag (mem2proc_transaction_tag),
        .mem2proc_data            (mem2proc_data),
        .mem2proc_data_tag        (mem2proc_data_tag),

        // Outputs
        .proc2mem_command (proc2mem_command),
        .proc2mem_addr    (proc2mem_addr),
        .proc2mem_data    (proc2mem_data),
`ifndef CACHE_MODE
        .proc2mem_size    (proc2mem_size),
`endif
        // .inst(insts),
        .committed_insts(committed_insts),
        // .PCs_out(PCs)
        .debug_mem_data_dcache(dcache_info), // DEBUG ALWAYS HIGH
        .debug_mem_data_vcache(vcache_info),
        .debug_dcache_meta_data(dcache_meta_data),
        .debug_vcache_meta_data(vcache_meta_data),
        .debug_mshr_true_head(mshr_true_head),
        .debug_mshr_spots(mshr_spots),
        .debug_mshrs(dcache_mshrs),
        .debug_wb_head(wb_head),
        .debug_wb_spots(wb_spots),
        .debug_wb_buffer(dcache_wb_buffer),
        .debug_sq_true_head(sq_true_head),
        .debug_sq_head(sq_head),
        .debug_store_buffer_entries(store_buffer_entries),
        .debug_store_queue(store_queue)
    );

    // cpu_sva cpu_sva (
    //     // Inputs
    //     .clock (clock),
    //     .reset (reset),

        
    //     .inst(insts),
    //     .committed_insts(committed_insts),
    //     .PC(PCs)
    // );

    // Instantiate the Data Memory
    mem memory (
        // Inputs
        .clock            (clock),
        .proc2mem_command (proc2mem_command),
        .proc2mem_addr    (proc2mem_addr),
        .proc2mem_data    (proc2mem_data),
`ifndef CACHE_MODE
        .proc2mem_size    (proc2mem_size),
`endif

        // Outputs
        .mem2proc_transaction_tag (mem2proc_transaction_tag),
        .mem2proc_data            (mem2proc_data),
        .mem2proc_data_tag        (mem2proc_data_tag)
    );

    

`ifdef SIM
    ROB_sva rob_instance (
        .clock             (clock),
        .reset             (reset),
        .rob_inputs        (verisimpleV.rob_entries),
        .rob_inputs_valid  (verisimpleV.num_dispatched), 
        .rob_spots         (verisimpleV.rob_spots),
        .rob_tail          (verisimpleV.rob_tail),
        .num_retiring      (verisimpleV.num_retiring),
        .rob_outputs       (verisimpleV.rob_outputs),
        .rob_outputs_valid (verisimpleV.rob_outputs_valid),
        .tail_restore_valid(verisimpleV.restore_valid),
        .tail_restore      (verisimpleV.rob_tail_restore)
    `ifdef DEBUG
        ,.rob_debug        (verisimpleV.rob_debug)
    `endif
    );

    RS_sva rs_instance (
        .clock             (clock),
        .reset             (reset),
        .num_dispatched    (verisimpleV.num_dispatched),
        .rs_entries        (verisimpleV.rs_entries), 
        .rs_spots          (verisimpleV.rs_spots),
        .ETB_tags          (verisimpleV.cdb_completing),
        .rs_data_issuing   (verisimpleV.rs_data_issuing),
        .rs_data           (verisimpleV.rs_data_next),
        .rs_valid_next     (verisimpleV.rs_valid_issue),
        .b_mm_resolve      (verisimpleV.b_mm_out),
        .b_mm_mispred      (verisimpleV.restore_valid)
    `ifdef DEBUG
        ,.rs_debug         (verisimpleV.rs_debug)
    `endif
    );

    FreddyList_sva fl_instance (
        .clock                  (clock),
        .reset                  (reset),
        .phys_reg_completing    (verisimpleV.phys_reg_completing),
        .completing_valid       (verisimpleV.completing_valid), 
        .phys_regs_retiring     (verisimpleV.phys_regs_retiring),
        .num_retiring_valid     (verisimpleV.num_retiring),
        .free_list_restore      (verisimpleV.free_list_restore),
        .restore_flag           (verisimpleV.restore_valid),
        .updated_free_list      (verisimpleV.updated_free_list),
        .regs_to_use            (verisimpleV.regs_to_use),
        .free_list              (verisimpleV.free_list),
        .next_complete_list     (verisimpleV.next_complete_list),
        .complete_list          (verisimpleV.complete_list)
    );

    BranchStack_sva dut_sva(
        .clock                  (clock),
        .reset                  (reset),
        .restore_valid          (verisimpleV.restore_valid),
        .PC_restore             (verisimpleV.PC_restore),
        .branch_completing      (verisimpleV.branch_reg),
        .rob_tail_restore       (verisimpleV.rob_tail_restore),
        .free_list_in           (verisimpleV.free_list),
        .free_list_restore      (verisimpleV.free_list_restore),
        .branch_stack_entries   (verisimpleV.branch_stack_entries),
        .next_b_mask            (verisimpleV.next_b_mask),
        .map_table_restore      (verisimpleV.map_table_restore),
        .b_mask_combinational   (verisimpleV.b_mask_combinational),
        .b_mm_out               (verisimpleV.b_mm_out), 
        .bs_bp_packet           (verisimpleV.bs_bp_packet),
        .resolving_valid_branch (verisimpleV.resolving_valid_branch),
        .resolving_valid        (verisimpleV.resolving_valid),
        .resolving_target_PC    (verisimpleV.resolving_target_PC),
       debug_mem_data_vcache  .resolving_branch_PC    (verisimpleV.resolving_branchPC)
        `ifdef DEBUG
        , .bs_debug(bs_debug)
        `endif
    );

    Dispatch_sva dispatch_instance (
        .clock(clock),
        .reset(reset),
        .inst_buffer_instructions_valid         (verisimpleV.inst_buffer_outputs_valid),
        .decoder_out                            (verisimpleV.decoder_out),
        .is_rs1_used                            (verisimpleV.is_rs1_used),
        .is_rs2_used                            (verisimpleV.is_rs2_used),
        .source1_arch_reg                       (verisimpleV.source1_arch_reg),
        .source2_arch_reg                       (verisimpleV.source2_arch_reg),
        .dest_arch_reg                          (verisimpleV.dest_arch_reg),
        .map_table_restore                      (verisimpleV.map_table_restore),
        .restore_valid                          (verisimpleV.restore_valid),
        .b_mask_combinational                   (verisimpleV.b_mask_combinational),
        .branch_stack_entries                   (verisimpleV.branch_stack_entries),
        .next_b_mask                            (verisimpleV.next_b_mask),
        .rob_tail                               (verisimpleV.rob_tail),
        .rob_spots                              (verisimpleV.rob_spots),
        .rob_entries                            (verisimpleV.rob_entries),
        .rs_spots                               (verisimpleV.rs_spots),
        .rs_entries                             (verisimpleV.rs_entries),
        .next_complete_list                     (verisimpleV.next_complete_list),
        .regs_to_use                            (verisimpleV.regs_to_use),
        .free_list_copy                         (verisimpleV.free_list),
        .updated_free_list                      (verisimpleV.updated_free_list),
        .cdb_completing                         (verisimpleV.cdb_completing),
        .num_dispatched                         (verisimpleV.num_dispatched)
        `ifdef DEBUG
            , .dispatch_debug                   (verisimpleV.dispatch_debug)
        `endif
    );

    Issue_sva issue_instance (
        .clock(clock),
        .reset(reset),
        .complete_list                  (verisimpleV.complete_list),
        .rs_data_next                   (verisimpleV.rs_data_next),
        .rs_valid_next                  (verisimpleV.rs_valid_next),
        .rs_data_issuing                (verisimpleV.rs_data_issuing),
        .issue_alu_read_data_1          (verisimpleV.issue_alu_read_data_1),
        .issue_alu_read_data_2          (verisimpleV.issue_alu_read_data_2),
        .issue_mult_read_data_1         (verisimpleV.issue_mult_read_data_1),
        .issue_mult_read_data_2         (verisimpleV.issue_mult_read_data_2),
        .issue_branch_read_data_1       (verisimpleV.issue_branch_read_data_1),
        .issue_branch_read_data_2       (verisimpleV.issue_branch_read_data_2),
        .issue_alu_regs_reading_1       (verisimpleV.issue_alu_regs_reading_1),
        .issue_alu_regs_reading_2       (verisimpleV.issue_alu_regs_reading_2),
        .issue_mult_regs_reading_1      (verisimpleV.issue_mult_regs_reading_1),
        .issue_mult_regs_reading_2      (verisimpleV.issue_mult_regs_reading_2),
        .issue_branch_regs_reading_1    (verisimpleV.issue_branch_regs_reading_1),
        .issue_branch_regs_reading_2    (verisimpleV.issue_branch_regs_reading_2),
        .cdb_reg                        (verisimpleV.cdb_reg),
        .mult_free                      (verisimpleV.mult_free),
        .ldst_free                      (verisimpleV.ldst_free),
        .mult_cdb_req                   (verisimpleV.mult_cdb_valid),
        .ldst_cdb_req                   (verisimpleV.ldst_cdb_valid),
        .mult_cdb_gnt                   (verisimpleV.mult_cdb_gnt),
        .ldst_cdb_gnt                   (verisimpleV.ldst_cdb_gnt),
        .alu_packets                    (verisimpleV.alu_packets),
        .mult_packets                   (verisimpleV.mult_packets),
        .branch_packets                 (verisimpleV.branch_packets),
        .ldst_packets                   (verisimpleV.ldst_packets),
        .complete_gnt_bus               (verisimpleV.complete_gnt_bus)
    );
`endif 

    

    // Generate System Clock
    always begin
        #(`CLOCK_PERIOD/2.0);
        clock = ~clock;
    end

    // generate
    // genvar i;
    //     for(i = 0; i < `N; ++i) begin
    //         logic [63:0] mem_block;
    //         assign mem_block = memory.unified_memory[PCs[i][15:3]];
    //         assign insts[i] = PCs[i][2] ? mem_block[63:32] : mem_block[31:0];
    //     end
    // endgenerate

    initial begin
        $dumpfile("../cpu.vcd");
        $dumpvars(0, testbench.verisimpleV);
        $display("\n---- Starting CPU Testbench ----\n");

        // set paramterized strings, see comment at start of module
        if ($value$plusargs("MEMORY=%s", program_memory_file)) begin
            $display("Using memory file  : %s", program_memory_file);
        end else begin
            $display("Did not receive '+MEMORY=' argument. Exiting.\n");
            $finish;
        end
        if ($value$plusargs("OUTPUT=%s", output_name)) begin
            $display("Using output files : %s.{out, cpi, wb, ppln}", output_name);
            out_outfile       = {output_name,".out"}; // this is how you concatenate strings in verilog
            cpi_outfile       = {output_name,".cpi"};
            writeback_outfile = {output_name,".wb"};
            //pipeline_outfile  = {output_name,".ppln"};
        end else begin
            $display("\nDid not receive '+OUTPUT=' argument. Exiting.\n");
            $finish;
        end

        clock = 1'b0;
        reset = 1'b0;

        $display("\n  %16t : Asserting Reset", $realtime);
        reset = 1'b1;

        @(posedge clock);
        @(posedge clock);

        $display("  %16t : Loading Unified Memory", $realtime);
        // load the compiled program's hex data into the memory module
        $readmemh(program_memory_file, memory.unified_memory);

        @(posedge clock);
        @(posedge clock);
        #1; // This reset is at an odd time to avoid the pos & neg clock edges
        $display("  %16t : Deasserting Reset", $realtime);
        reset = 1'b0;

        wb_fileno = $fopen(writeback_outfile);
        $fdisplay(wb_fileno, "Register writeback output (hexadecimal)");

        // Open pipeline output file AFTER throwing the reset otherwise the reset state is displayed
        // open_pipeline_output_file(pipeline_outfile);
        // print_header();

        out_fileno = $fopen(out_outfile);

        $display("  %16t : Running Processor", $realtime);
    end

    task show_curr_mem_and_status;
        int showing_data;
        updated_memory = memory.unified_memory;
        $display("Current memory state and exit status:");
        $display("@@@ Unified Memory contents hex on left, decimal on right: ");
        $display("@@@");
        showing_data = 0;
        for (int k = 0; k <= `MEM_64BIT_LINES - 1; k = k+1) begin
            //that sh is in memory

            for (int l = 0; l < `DCACHE_NUM_SETS; ++l) begin
                for (int m = 0; m < `DCACHE_NUM_WAYS; ++m) begin
                    if (dcache_meta_data[l][m].valid && dcache_meta_data[l][m].addr.dw.addr == k) begin
                        updated_memory[k] = dcache_info[(l * `DCACHE_NUM_WAYS) + m];
                    end
                end
            end

            //is the most updated version of k in vcache?
            for (int l = 0; l < `VCACHE_LINES; ++l) begin
                if(vcache_meta_data[l].valid && (vcache_meta_data[l].addr.dw.addr == k)) begin
                    updated_memory[k] = vcache_info[l];
                end 
            end

            //is the most updated version of k in wb_buffer?
            for (int l = 0; l < `WB_LINES; ++l) begin
                if (l < `WB_LINES - wb_spots) begin
                    if (dcache_wb_buffer[(wb_head + l) % `WB_LINES].addr.dw.addr == k) begin
                        updated_memory[k] = dcache_wb_buffer[(wb_head + l) % `WB_LINES].data;
                    end
                end
            end

            // $display("mshr_spots: %d", mshr_spots);
            // $display("mshr_true_head: %d", mshr_true_head);
            //is the most updated version of k in mshrs?
            for(int l = 0; l < `MSHR_SZ; ++l) begin
                if (l < `MSHR_SZ - mshr_spots) begin
                    if (dcache_mshrs[(mshr_true_head + l) % `MSHR_SZ].addr.dw.addr == k) begin
                        for(int m = 0; m < 2; ++m) begin
                            for(int n = 0; n < 4; ++n) begin
                                if(dcache_mshrs[(mshr_true_head + l) % `MSHR_SZ].byte_mask[m][n]) begin
                                    updated_memory[k][m].bytes[n] = dcache_mshrs[(mshr_true_head + l) % `MSHR_SZ].data[m].bytes[n];
                                end
                            end
                        end
                    end
                end
            end
            
            for(int l = 0; l < `SQ_SZ; ++l) begin
                if(l < store_buffer_entries) begin
                    if (store_queue[(sq_true_head.sq_idx + l) % `SQ_SZ].addr.dw.addr == k) begin
                        for(int m = 0; m < 4; ++m) begin
                            if(store_queue[(sq_true_head.sq_idx + l) % `SQ_SZ].byte_mask[m]) begin
                                updated_memory[k][store_queue[(sq_true_head.sq_idx + l) % `SQ_SZ].addr.dw.w_idx].bytes[m] = store_queue[(sq_true_head.sq_idx + l) % `SQ_SZ].result.bytes[m];
                            end
                        end
                    end
                end
            end

            if (updated_memory[k] != 0) begin
                $display("@@@ mem[%h] = %x : %0d", k*8, updated_memory[k],
                                                        updated_memory[k]);
                showing_data = 1;
            end else if (showing_data != 0) begin
                $display("@@@");
                showing_data = 0;
            end
        end
        $display("@@@");
    endtask

    always @(negedge clock) begin
        if (reset) begin
            // Count the number of cycles and number of instructions committed
            clock_count = 0;
            instr_count = 0;
        end else begin
            #2; // wait a short time to avoid a clock edge

            clock_count = clock_count + 1;

            if (clock_count % 10000 == 0) begin
                $display("  %16t : %d cycles", $realtime, clock_count);
            end

            // print the pipeline debug outputs via c code to the pipeline output file
            // print_cycles(clock_count - 1);
            // print_stage(if_inst_dbg,     if_NPC_dbg,     {31'b0,if_valid_dbg});
            // print_stage(if_id_inst_dbg,  if_id_NPC_dbg,  {31'b0,if_id_valid_dbg});
            // print_stage(id_ex_inst_dbg,  id_ex_NPC_dbg,  {31'b0,id_ex_valid_dbg});
            // print_stage(ex_mem_inst_dbg, ex_mem_NPC_dbg, {31'b0,ex_mem_valid_dbg});
            // print_stage(mem_wb_inst_dbg, mem_wb_NPC_dbg, {31'b0,mem_wb_valid_dbg});
            // print_reg(committed_insts[0].data, {27'b0,committed_insts[0].reg_idx},
            //           {31'b0,committed_insts[0].valid});
            // print_membus({30'b0,proc2mem_command}, proc2mem_addr[31:0],
            //              proc2mem_data[63:32], proc2mem_data[31:0]);

            // print_custom_data();

            output_reg_writeback_and_maybe_halt();

            // show_curr_mem_and_status();

            // stop the processor
            if (error_status != NO_ERROR || clock_count > `TB_MAX_CYCLES) begin

                $display("  %16t : Processor Finished", $realtime);

                // close the writeback and pipeline output files
                // close_pipeline_output_file();
                $fclose(wb_fileno);

                // display the final memory and status
                $display("FRICK U");
                @(negedge clock);
                show_final_mem_and_status(error_status);
                // output the final CPI
                output_cpi_file();

                $display("\n---- Finished CPU Testbench ----\n");

                #100 $finish;
            end
        end // if(reset)
    end


    // Task to output register writeback data and potentially halt the processor.
    task output_reg_writeback_and_maybe_halt;
        ADDR pc;
        DATA inst;
        MEM_BLOCK block;
        for (int n = 0; n < `N; ++n) begin
            if (committed_insts[n].valid) begin
                // update the count for every committed instruction
                instr_count = instr_count + 1;

                pc = committed_insts[n].NPC - 4;
                block = memory.unified_memory[pc[31:3]];
                inst = block.word_level[pc[2]];
                // print the committed instructions to the writeback output file
                if (committed_insts[n].reg_idx == `ZERO_REG) begin
                    $fdisplay(wb_fileno, "PC %4x:%-8s| ---", pc, decode_inst(inst));
                end else begin
                    $fdisplay(wb_fileno, "PC %4x:%-8s| r%02d=%-8x",
                              pc,
                              decode_inst(inst),
                              committed_insts[n].reg_idx,
                              committed_insts[n].data);
                end

                // exit if we have an illegal instruction or a halt
                if (committed_insts[n].illegal) begin
                    error_status = ILLEGAL_INST;
                    break;
                end else if(committed_insts[n].halt) begin
                    error_status = HALTED_ON_WFI;
                    break;
                end
            end // if valid
        end
    endtask // task output_reg_writeback_and_maybe_halt


    // Task to output the final CPI and # of elapsed clock edges
    task output_cpi_file;
        real cpi;
        begin
            cpi = $itor(clock_count) / instr_count; // must convert int to real
            cpi_fileno = $fopen(cpi_outfile);
            $fdisplay(cpi_fileno, "@@@  %0d cycles / %0d instrs = %f CPI",
                      clock_count, instr_count, cpi);
            $fdisplay(cpi_fileno, "@@@  %4.2f ns total time to execute",
                      clock_count * `CLOCK_PERIOD);
            $fclose(cpi_fileno);
        end
    endtask // task output_cpi_file


    // Show contents of Unified Memory in both hex and decimal
    // Also output the final processor status
    task show_final_mem_and_status;
        input EXCEPTION_CODE final_status;
        int showing_data;
        
        begin
            
            updated_memory = memory.unified_memory;
            $fdisplay(out_fileno, "\nFinal memory state and exit status:\n");
            $fdisplay(out_fileno, "@@@ Unified Memory contents hex on left, decimal on right: ");
            $fdisplay(out_fileno, "@@@");
            showing_data = 0;
            for (int k = 0; k < `MEM_64BIT_LINES; ++k) begin
                // is the most updated version of k in dcache?
                for (int l = 0; l < `DCACHE_NUM_SETS; ++l) begin
                    for (int m = 0; m < `DCACHE_NUM_WAYS; ++m) begin
                        if (dcache_meta_data[l][m].valid && dcache_meta_data[l][m].addr.dw.addr == k) begin
                            updated_memory[k] = dcache_info[(l * `DCACHE_NUM_WAYS) + m];
                        end
                    end
                end

                //is the most updated version of k in vcache?
                for (int l = 0; l < `VCACHE_LINES; ++l) begin
                    if(vcache_meta_data[l].valid && (vcache_meta_data[l].addr.dw.addr == k)) begin
                        updated_memory[k] = vcache_info[l];
                    end 
                end

                //is the most updated version of k in wb_buffer?
                for (int l = 0; l < `WB_LINES; ++l) begin
                    if (l < `WB_LINES - wb_spots) begin
                        if (dcache_wb_buffer[(wb_head + l) % `WB_LINES].addr.dw.addr == k) begin
                            updated_memory[k] = dcache_wb_buffer[(wb_head + l) % `WB_LINES].data;
                        end
                    end
                end

                // $display("mshr_spots: %d", mshr_spots);
                // $display("mshr_true_head: %d", mshr_true_head);
                //is the most updated version of k in mshrs?
                for(int l = 0; l < `MSHR_SZ; ++l) begin
                    if (l < `MSHR_SZ - mshr_spots) begin
                        if (dcache_mshrs[(mshr_true_head + l) % `MSHR_SZ].addr.dw.addr == k) begin
                            for(int m = 0; m < 2; ++m) begin
                                for(int n = 0; n < 4; ++n) begin
                                    if(dcache_mshrs[(mshr_true_head + l) % `MSHR_SZ].byte_mask[m][n]) begin
                                        updated_memory[k][m].bytes[n] = dcache_mshrs[(mshr_true_head + l) % `MSHR_SZ].data[m].bytes[n];
                                    end
                                end
                            end
                        end
                    end
                end
                
                for(int l = 0; l < `SQ_SZ; ++l) begin
                    if(l < store_buffer_entries) begin
                        if (store_queue[(sq_true_head.sq_idx + l) % `SQ_SZ].addr.dw.addr == k) begin
                            for(int m = 0; m < 4; ++m) begin
                                if(store_queue[(sq_true_head.sq_idx + l) % `SQ_SZ].byte_mask[m]) begin
                                    updated_memory[k][store_queue[(sq_true_head.sq_idx + l) % `SQ_SZ].addr.dw.w_idx].bytes[m] = store_queue[(sq_true_head.sq_idx + l) % `SQ_SZ].result.bytes[m];
                                end
                            end
                        end
                    end
                end
                
                //that sh is in memory
                if (updated_memory[k] != 0) begin
                    $fdisplay(out_fileno, "@@@ mem[%5d] = %x : %0d", k*8, updated_memory[k],
                                                            updated_memory[k]);
                    showing_data = 1;
                end else if (showing_data != 0) begin
                    $fdisplay(out_fileno, "@@@");
                    showing_data = 0;
                end
            end
            $fdisplay(out_fileno, "@@@");

            case (final_status)
                LOAD_ACCESS_FAULT: $fdisplay(out_fileno, "@@@ System halted on memory error");
                HALTED_ON_WFI:     $fdisplay(out_fileno, "@@@ System halted on WFI instruction");
                ILLEGAL_INST:      $fdisplay(out_fileno, "@@@ System halted on illegal instruction");
                default:           $fdisplay(out_fileno, "@@@ System halted on unknown error code %x", final_status);
            endcase
            $fdisplay(out_fileno, "@@@");
            $fclose(out_fileno);
        end
    endtask // task show_final_mem_and_status

    



    // OPTIONAL: Print our your data here
    // It will go to the $program.log file
    task print_custom_data;
        $display("%3d: YOUR DATA HERE", 
           clock_count-1
        );
    endtask


endmodule // module testbench
