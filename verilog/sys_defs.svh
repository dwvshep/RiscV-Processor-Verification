/////////////////////////////////////////////////////////////////////////
//                                                                     //
//   Modulename :  sys_defs.svh                                        //
//                                                                     //
//  Description :  This file defines macros and data structures used   //
//                 throughout the processor.                           //
//                                                                     //
/////////////////////////////////////////////////////////////////////////

`ifndef __SYS_DEFS_SVH__
`define __SYS_DEFS_SVH__

// all files should `include "sys_defs.svh" to at least define the timescale
`timescale 1ns/100ps

///////////////////////////////////
// ---- Starting Parameters ---- //
///////////////////////////////////
`define DEBUG //Comment out when synthesizing
//`define SIM

// some starting parameters that you should set
// this is *your* processor, you decide these values (try analyzing which is best!)

// superscalar width
`define N 2
`define B_MASK_WIDTH 4
`define NUM_B_MASK_BITS $clog2(`B_MASK_WIDTH + 1)
`define CDB_SZ `N // This MUST match your superscalar width
`define NUM_SCALAR_BITS $clog2(`N+1) // Number of bits to represent [0, NUM_SCALAR_BITS]
`define HISTORY_BITS 5
`define BTB_NUM_WAYS 8

// functional units (you should decide if you want more or fewer types of FUs)
`define NUM_FU_BRANCH 1
`define NUM_FU_ALU `N
`define NUM_FU_MULT `N
`define NUM_FU_LOAD 1
`define NUM_FU_STORE 1
`define NUM_FU_TOTAL `NUM_FU_ALU + `NUM_FU_MULT + `NUM_FU_BRANCH + `LOAD_BUFFER_SZ

// sizes
`define FB_SZ 32
`define FB_SZ_BITS $clog2(`FB_SZ)
`define ROB_SZ 32
`define ROB_SZ_BITS $clog2(`ROB_SZ)
`define ROB_NUM_ENTRIES_BITS $clog2(`ROB_SZ + 1)
`define RS_SZ 32
`define MSHR_SZ 16
`define SQ_SZ 8
`define SQ_IDX_BITS $clog2(`SQ_SZ)
`define SQ_NUM_ENTRIES_BITS $clog2(`SQ_SZ + 1)
`define RS_SZ_BITS $clog2(`RS_SZ)
`define RS_NUM_ENTRIES_BITS $clog2(`RS_SZ + 1)
`define ARCH_REG_SZ_R10K (32)
`define PHYS_REG_SZ_P6 32
`define PHYS_REG_SZ_R10K (`ARCH_REG_SZ_R10K + `ROB_SZ)
`define PHYS_REG_NUM_ENTRIES_BITS $clog2(`PHYS_REG_SZ_R10K + 1)
`define CDB_ARBITER_SZ `RS_SZ + `NUM_FU_MULT + `LOAD_BUFFER_SZ
`define BTB_SZ 64
`define BTB_NUM_SETS `BTB_SZ / `BTB_NUM_WAYS
`define BTB_SET_IDX_BITS $clog2(`BTB_NUM_SETS)
`define BTB_TAG_BITS 32 - `BTB_SET_IDX_BITS - 2
`define BTB_NUM_ENTRIES_BITS $clog2(`BTB_NUM_WAYS + 1)    
`define BTB_LRU_BITS $clog2(`BTB_NUM_WAYS)
`define NUM_SQ_BITS $clog2(`SQ_SZ+1)
`define MSHR_IDX_BITS $clog2(`MSHR_SZ)
`define MSHR_NUM_ENTRIES_BITS $clog2(`MSHR_SZ+1)
`define LOAD_BUFFER_SZ 8
`define PHT_SZ 2 ** `HISTORY_BITS
`define CTR_SZ 2 


// EDITED HERE
`define ROB_ENTRY_ID_BITS $clog2(`ROB_SZ)
`define PHYS_REG_ID_BITS $clog2(`PHYS_REG_SZ_R10K)
`define B_MASK_ID_BITS $clog2(`B_MASK_WIDTH)
`define ARCH_REG_ID_BITS $clog2(32) // Assuming # arch reg = 32
`define FU_ID_BITS $clog2(`NUM_FU_TOTAL)

typedef logic [`ROB_ENTRY_ID_BITS-1:0]      ROB_ENTRY_ID;
typedef logic [`PHYS_REG_ID_BITS-1:0]       PHYS_REG_IDX;
typedef logic [`ARCH_REG_ID_BITS-1:0]       ARCH_REG_IDX;
typedef logic [`MSHR_IDX_BITS-1:0]          MSHR_IDX;
typedef logic [6:0]                         OPCODE;
typedef logic [`B_MASK_WIDTH-1:0]           B_MASK;
typedef logic [`B_MASK_WIDTH-1:0]           B_MASK_MASK;
typedef logic [2:0]                         BRANCH_FUNC;
typedef logic [2:0]                         LOAD_FUNC;
typedef logic [`SQ_SZ-1:0]                  SQ_MASK;
typedef logic [`SQ_IDX_BITS-1:0]            SQ_IDX;
typedef logic [2:0]                         STORE_FUNC;
typedef logic [11:0]                 STORE_IMM;
typedef logic [3:0]                         BYTE_MASK;
typedef logic [`FU_ID_BITS-1:0]             FU_IDX;
typedef logic [`HISTORY_BITS-1:0]           PHT_IDX;
typedef logic [`HISTORY_BITS-1:0]           BHR;
typedef logic [`BTB_SET_IDX_BITS-1:0]       BTB_SET_IDX;
typedef logic [`BTB_TAG_BITS-1:0]           BTB_TAG;
typedef logic [`BTB_LRU_BITS-1:0]           BTB_LRU;
typedef logic [`BTB_NUM_ENTRIES_BITS-1:0]   BTB_NUM_ENTRY;

typedef enum logic [2:0] {
    ALU   = 3'b000,
    MULT  = 3'b001,
    BU    = 3'b010,
    LOAD  = 3'b011,
    STORE = 3'b100
} FU_TYPE;

// STRONGLY_NOT_TAKEN   = 2'h0,
// WEAKLY_NOT_TAKEN   = 2'h1,
// WEAKLY_TAKEN   = 2'h2,
// STRONGLY_TAKEN = 2'h3
typedef logic [1:0] TWO_BIT_PREDICTOR; 


// STRONGLY_SIMPLE   = 2'h0,
// WEAKLY_SIMPLE   = 2'h1,
// WEAKLY_GSHARE   = 2'h2,
// STRONGLY_GSHARE = 2'h3
typedef logic [1:0] CHOOSER;

// EDITED END

// worry about these later


// number of mult stages (2, 4) (you likely don't need 8)
`define MULT_STAGES 8

///////////////////////////////
// ---- Basic Constants ---- //
///////////////////////////////

// NOTE: the global CLOCK_PERIOD is defined in the Makefile

// useful boolean single-bit definitions
`define FALSE 1'h0
`define TRUE  1'h1
// word and register sizes

typedef logic [19:0] IMM;
typedef logic [4:0] REG_IDX;

typedef union packed {
    logic [31:0]        data;
    logic [3:0][7:0]    bytes;
    logic [1:0][15:0]   halfs;
} DATA;

typedef struct packed {
    logic parity;
    SQ_IDX sq_idx;
} SQ_POINTER;

// the zero register
// In RISC-V, any read of this register returns zero and any writes are thrown away
`define ZERO_REG 5'd0

// Basic NOP instruction. Allows pipline registers to clearly be reset with
// an instruction that does nothing instead of Zero which is really an ADDI x0, x0, 0
`define NOP 32'h00000013

//////////////////////////////////
// ---- Memory Definitions ---- //
//////////////////////////////////

// Cache mode removes the byte-level interface from memory, so it always returns
// a double word. The original processor won't work with this defined. Your new
// processor will have to account for this effect on mem.
// Notably, you can no longer write data without first reading.
// TODO: uncomment this line once you've implemented your cache
`define CACHE_MODE

// you are not allowed to change this definition for your final processor
// the project 3 processor has a massive boost in performance just from having no mem latency
// see if you can beat it's CPI in project 4 even with a 100ns latency!
//`define MEM_LATENCY_IN_CYCLES  0
`define MEM_LATENCY_IN_CYCLES (100.0/`CLOCK_PERIOD+0.49999)
// the 0.49999 is to force ceiling(100/period). The default behavior for
// float to integer conversion is rounding to nearest

// memory tags represent a unique id for outstanding mem transactions
// 0 is a sentinel value and is not a valid tag
`define NUM_MEM_TAGS 15
typedef logic [3:0] MEM_TAG;

`define MEM_SIZE_IN_BYTES (64*1024)
`define MEM_64BIT_LINES   (`MEM_SIZE_IN_BYTES/8)

`define DCACHE_SET_IDX_BITS $clog2(`DCACHE_NUM_SETS)
`define ICACHE_SET_IDX_BITS $clog2(`ICACHE_NUM_SETS)

// icache definitions
`define ICACHE_NUM_WAYS 1 //LEAVE THIS SHI
`define ICACHE_NUM_BANKS 2
`define ICACHE_LINES 32 / `ICACHE_NUM_BANKS
`define ICACHE_NUM_SETS `ICACHE_LINES / `ICACHE_NUM_WAYS
`define ICACHE_NUM_BANKS_BITS $clog2(`ICACHE_NUM_BANKS)
`define ICACHE_LINE_BITS $clog2(`ICACHE_LINES)
`define ICACHE_TAG_BITS 32 - `ICACHE_NUM_BANKS_BITS - `ICACHE_SET_IDX_BITS - 3
`define ICACHE_WAY_IDX_BITS $clog2(`ICACHE_NUM_WAYS)
`define PREFETCH_DIST 32

typedef logic [`ICACHE_TAG_BITS-1:0] ICACHE_TAG;
typedef logic [`ICACHE_WAY_IDX_BITS-1:0] ICACHE_LRU;
typedef logic [`ICACHE_WAY_IDX_BITS-1:0] ICACHE_WAY_IDX;
typedef logic [`ICACHE_LINE_BITS-1:0] ICACHE_IDX;

// dcache definitions
`define DCACHE_NUM_WAYS 16
`define DCACHE_LINES 32
`define DCACHE_NUM_SETS `DCACHE_LINES / `DCACHE_NUM_WAYS
`define DCACHE_LINE_BITS $clog2(`DCACHE_LINES)
`define DCACHE_TAG_BITS 32 - `DCACHE_SET_IDX_BITS - 3
`define DCACHE_WAY_IDX_BITS $clog2(`DCACHE_NUM_WAYS)
typedef logic [`DCACHE_TAG_BITS-1:0] DCACHE_TAG; 
typedef logic [`DCACHE_WAY_IDX_BITS-1:0] DCACHE_LRU;
typedef logic [`DCACHE_WAY_IDX_BITS-1:0] DCACHE_WAY_IDX;
typedef logic [`DCACHE_LINE_BITS-1:0] DCACHE_IDX;

// vcache definitions
`define VCACHE_NUM_WAYS 4
`define VCACHE_LINES 4
`define VCACHE_NUM_SETS `VCACHE_LINES / `VCACHE_NUM_WAYS
`define VCACHE_LINE_BITS $clog2(`VCACHE_LINES)
`define VCACHE_WAY_IDX_BITS $clog2(`VCACHE_NUM_WAYS)
typedef logic [`VCACHE_LINE_BITS-1:0] VCACHE_LRU;
typedef logic [`VCACHE_LINE_BITS-1:0] VCACHE_IDX;

// WB buffer definitions
`define WB_LINES 4 //restricted to 4 mem blocks (lines)
`define WB_NUM_ENTRIES_BITS $clog2(`WB_LINES+1)
`define WB_LINE_BITS $clog2(`WB_LINES)
typedef logic [`WB_LINE_BITS-1:0] WB_IDX;

typedef union packed {
    logic [31:0] addr;

    struct packed {
        logic [31:`BTB_SET_IDX_BITS+2] tag;
        logic  [`BTB_SET_IDX_BITS+1:2] set_idx;
        logic                    [1:0] byte_offset;
    } btb;

    struct packed {
        logic                    [31:2]  addr;
        logic                     [1:0]  offset;
    } w;

    struct packed {
        logic                    [31:3]  addr;
        logic                     [2:2]  w_idx;
        logic                     [1:0]  offset;
    } dw;

    struct packed {
        logic                    [31:`DCACHE_SET_IDX_BITS+3] tag;
        logic                    [`DCACHE_SET_IDX_BITS+3-1:3] set_idx;
        logic                    [2:0] offset;
    } dcache;

    struct packed {
        logic                    [31:`ICACHE_SET_IDX_BITS+`ICACHE_NUM_BANKS_BITS+3] tag;
        logic                    [`ICACHE_SET_IDX_BITS+`ICACHE_NUM_BANKS_BITS+3-1:`ICACHE_NUM_BANKS_BITS+3] set_idx;
        logic                    [`ICACHE_NUM_BANKS_BITS+3-1:3] bank_idx;
        logic                    [2:0] offset;
    } icache;

    // struct packed {
    //     logic [31:] tag;
    //     logic  [`BTB_SET_IDX_BITS+1:2] set_idx;
    // } cache;
} ADDR; // ADDER UNION

// A memory or cache block
typedef union packed {
    logic [7:0][7:0]  byte_level;
    logic [3:0][15:0] half_level;
    logic [1:0][31:0] word_level;
    logic      [63:0] dbbl_level;
} MEM_BLOCK;

typedef enum logic [1:0] {
    BYTE   = 2'h0,
    HALF   = 2'h1,
    WORD   = 2'h2,
    DOUBLE = 2'h3
} MEM_SIZE;

// Memory bus commands
typedef enum logic [1:0] {
    MEM_NONE   = 2'h0,
    MEM_LOAD   = 2'h1,
    MEM_STORE  = 2'h2
} MEM_COMMAND;

// icache tag struct
// typedef struct packed {
//     logic [12-`ICACHE_LINE_BITS:0] tags;
//     logic                          valid;
// } ICACHE_TAG;

///////////////////////////////
// ---- Exception Codes ---- //
///////////////////////////////

/**
 * Exception codes for when something goes wrong in the processor.
 * Note that we use HALTED_ON_WFI to signify the end of computation.
 * It's original meaning is to 'Wait For an Interrupt', but we generally
 * ignore interrupts in 470
 *
 * This mostly follows the RISC-V Privileged spec
 * except a few add-ons for our infrastructure
 * The majority of them won't be used, but it's good to know what they are
 */

typedef enum logic [3:0] {
    INST_ADDR_MISALIGN  = 4'h0,
    INST_ACCESS_FAULT   = 4'h1,
    ILLEGAL_INST        = 4'h2,
    BREAKPOINT          = 4'h3,
    LOAD_ADDR_MISALIGN  = 4'h4,
    LOAD_ACCESS_FAULT   = 4'h5,
    STORE_ADDR_MISALIGN = 4'h6,
    STORE_ACCESS_FAULT  = 4'h7,
    ECALL_U_MODE        = 4'h8,
    ECALL_S_MODE        = 4'h9,
    NO_ERROR            = 4'ha, // a reserved code that we use to signal no errors
    ECALL_M_MODE        = 4'hb,
    INST_PAGE_FAULT     = 4'hc,
    LOAD_PAGE_FAULT     = 4'hd,
    HALTED_ON_WFI       = 4'he, // 'Wait For Interrupt'. In 470, signifies the end of computation
    STORE_PAGE_FAULT    = 4'hf
} EXCEPTION_CODE;

///////////////////////////////////
// ---- Instruction Typedef ---- //
///////////////////////////////////

// from the RISC-V ISA spec
typedef union packed {
    logic [31:0] inst;
    struct packed {
        logic [6:0] funct7;
        logic [4:0] rs2; // source register 2
        logic [4:0] rs1; // source register 1
        logic [2:0] funct3;
        logic [4:0] rd; // destination register
        logic [6:0] opcode;
    } r; // register-to-register instructions
    struct packed {
        logic [11:0] imm; // immediate value for calculating address
        logic [4:0]  rs1; // source register 1 (used as address base)
        logic [2:0]  funct3;
        logic [4:0]  rd;  // destination register
        logic [6:0]  opcode;
    } i; // immediate or load instructions
    struct packed {
        logic [6:0] off; // offset[11:5] for calculating address
        logic [4:0] rs2; // source register 2
        logic [4:0] rs1; // source register 1 (used as address base)
        logic [2:0] funct3;
        logic [4:0] set; // offset[4:0] for calculating address
        logic [6:0] opcode;
    } s; // store instructions
    struct packed {
        logic       of;  // offset[12]
        logic [5:0] s;   // offset[10:5]
        logic [4:0] rs2; // source register 2
        logic [4:0] rs1; // source register 1
        logic [2:0] funct3;
        logic [3:0] et;  // offset[4:1]
        logic       f;   // offset[11]
        logic [6:0] opcode;
    } b; // branch instructions
    struct packed {
        logic [19:0] imm; // immediate value
        logic [4:0]  rd; // destination register
        logic [6:0]  opcode;
    } u; // upper-immediate instructions
    struct packed {
        logic       of; // offset[20]
        logic [9:0] et; // offset[10:1]
        logic       s;  // offset[11]
        logic [7:0] f;  // offset[19:12]
        logic [4:0] rd; // destination register
        logic [6:0] opcode;
    } j;  // jump instructions

    

// extensions for other instruction types
`ifdef ATOMIC_EXT
    struct packed {
        logic [4:0] funct5;
        logic       aq;
        logic       rl;
        logic [4:0] rs2;
        logic [4:0] rs1;
        logic [2:0] funct3;
        logic [4:0] rd;
        logic [6:0] opcode;
    } a; // atomic instructions
`endif
`ifdef SYSTEM_EXT
    struct packed {
        logic [11:0] csr;
        logic [4:0]  rs1;
        logic [2:0]  funct3;
        logic [4:0]  rd;
        logic [6:0]  opcode;
    } sys; // system call instructions
`endif

} INST; // instruction typedef, this should cover all types of instructions



////////////////////////////////////////
// ---- Datapath Control Signals ---- //
////////////////////////////////////////

// ALU opA input mux selects
typedef enum logic [1:0] {
    OPA_IS_RS1  = 2'h0,
    OPA_IS_NPC  = 2'h1,
    OPA_IS_PC   = 2'h2,
    OPA_IS_ZERO = 2'h3
} ALU_OPA_SELECT;

// ALU opB input mux selects
typedef enum logic [3:0] {
    OPB_IS_RS2    = 4'h0,
    OPB_IS_I_IMM  = 4'h1,
    OPB_IS_S_IMM  = 4'h2,
    OPB_IS_B_IMM  = 4'h3,
    OPB_IS_U_IMM  = 4'h4,
    OPB_IS_J_IMM  = 4'h5
} ALU_OPB_SELECT;

// ALU function code
typedef enum logic [3:0] {
    ALU_ADD     = 4'h0,
    ALU_SUB     = 4'h1,
    ALU_SLT     = 4'h2,
    ALU_SLTU    = 4'h3,
    ALU_AND     = 4'h4,
    ALU_OR      = 4'h5,
    ALU_XOR     = 4'h6,
    ALU_SLL     = 4'h7,
    ALU_SRL     = 4'h8,
    ALU_SRA     = 4'h9
} ALU_FUNC;

// MULT funct3 code
// we don't include division or rem options
typedef enum logic [2:0] {
    M_MUL,
    M_MULH,
    M_MULHSU,
    M_MULHU
} MULT_FUNC;

////////////////////////////////
// ---- Datapath Packets ---- //
////////////////////////////////

/**
 * Packets are used to move many variables between modules with
 * just one datatype, but can be cumbersome in some circumstances.
 *
 * Define new ones in project 4 at your own discretion
 */

/**
 * IF_ID Packet:
 * Data exchanged from the IF to the ID stage
 */
typedef struct packed {
    INST  inst;
    ADDR  PC;
    ADDR  NPC; // PC + 4
    logic valid;
} IF_ID_PACKET;

/**
 * ID_EX Packet:
 * Data exchanged from the ID to the EX stage
 */
typedef struct packed {
    INST inst;
    ADDR PC;
    ADDR NPC; // PC + 4

    DATA rs1_value; // reg A value
    DATA rs2_value; // reg B value

    ALU_OPA_SELECT opa_select; // ALU opa mux select (ALU_OPA_xxx *)
    ALU_OPB_SELECT opb_select; // ALU opb mux select (ALU_OPB_xxx *)

    REG_IDX  dest_reg_idx;  // destination (writeback) register index
    ALU_FUNC alu_func;      // ALU function select (ALU_xxx *)
    logic    mult;          // Is inst a multiply instruction?
    logic    rd_mem;        // Does inst read memory?
    logic    wr_mem;        // Does inst write memory?
    logic    cond_branch;   // Is inst a conditional branch?
    logic    uncond_branch; // Is inst an unconditional branch?
    logic    halt;          // Is this a halt?
    logic    illegal;       // Is this instruction illegal?
    logic    csr_op;        // Is this a CSR operation? (we only used this as a cheap way to get return code)

    logic    valid;
} ID_EX_PACKET;

/**
 * EX_MEM Packet:
 * Data exchanged from the EX to the MEM stage
 */
typedef struct packed {
    DATA alu_result;
    ADDR NPC;

    logic    take_branch; // Is this a taken branch?
    // Pass-through from decode stage
    DATA     rs2_value;
    logic    rd_mem;
    logic    wr_mem;
    REG_IDX  dest_reg_idx;
    logic    halt;
    logic    illegal;
    logic    csr_op;
    logic    rd_unsigned; // Whether proc2Dmem_data is signed or unsigned
    MEM_SIZE mem_size;
    logic    valid;
} EX_MEM_PACKET;

/**
 * MEM_WB Packet:
 * Data exchanged from the MEM to the WB stage
 *
 * Does not include data sent from the MEM stage to memory
 */
typedef struct packed {
    DATA    result;
    ADDR    NPC;
    REG_IDX dest_reg_idx; // writeback destination (ZERO_REG if no writeback)
    logic   take_branch;
    logic   halt;    // not used by wb stage
    logic   illegal; // not used by wb stage
    logic   valid;
} MEM_WB_PACKET;

/**
 * Commit Packet:
 * This is an output of the processor and used in the testbench for counting
 * committed instructions
 *
 * It also acts as a "WB_PACKET", and can be reused in the final project with
 * some slight changes
 */
typedef struct packed {
    ADDR    NPC;
    DATA    data; 
    ARCH_REG_IDX reg_idx;
    logic   halt;
    logic   illegal;
    logic   valid;
} COMMIT_PACKET;

// EDIED HERE

typedef struct packed {
    ADDR            NPC;
    logic           illegal;
    logic           halt;
    PHYS_REG_IDX    T_new; // Use as unique rob id
    PHYS_REG_IDX    T_old;
    ARCH_REG_IDX    arch_reg;
    logic           is_store; 
} ROB_PACKET;

typedef struct packed {
    logic             gshare_predict_taken;
    logic             simple_predict_taken; 
    PHT_IDX           meta_PHT_idx;
    PHT_IDX           gshare_PHT_idx;
    BHR               BHR_state;
} BRANCH_PREDICTOR_PACKET;

typedef struct packed {
    logic place_holder;
} BP_DEBUG;

typedef struct packed{
    INST                    inst;
    logic                   valid; // when low, ignore inst. Output will look like a NOP
    logic                   predict_taken;
    ADDR                    PC;
    ADDR                    NPC;
    ALU_OPA_SELECT          opa_select;
    ALU_OPB_SELECT          opb_select;
    logic                   has_dest; // if there is a destination register
    ALU_FUNC                alu_func;
    logic                   mult; 
    logic                   rd_mem; 
    logic                   wr_mem; 
    logic                   cond_branch; 
    logic                   uncond_branch;
    logic                   csr_op; // used for CSR operations, we only use this as a cheap way to get the return code out
    logic                   halt;   // non-zero on a halt
    logic                   illegal; // non-zero on an illegal instruction
    FU_TYPE                 FU_type;
    BRANCH_PREDICTOR_PACKET bp_packet;
    ADDR                    predicted_PC; //only necessary for jumps
    logic                   is_jump;
} DECODE_PACKET;

//TODO: CHANGE FOR RS
typedef struct packed {  
    DECODE_PACKET       decoded_signals;
    PHYS_REG_IDX        T_new; // Use as unique RS id ???
    PHYS_REG_IDX        Source1;
    logic               Source1_ready;
    PHYS_REG_IDX        Source2;
    logic               Source2_ready;
    B_MASK              b_mask;
    B_MASK_MASK         b_mask_mask;
    SQ_POINTER          sq_tail;
    SQ_MASK             sq_mask;
} RS_PACKET;

typedef struct packed {
    ADDR                               recovery_PC;
    logic           [`ROB_SZ_BITS-1:0] rob_tail;
    logic      [`PHYS_REG_SZ_R10K-1:0] free_list;
    PHYS_REG_IDX [`ARCH_REG_SZ_R10K:0] map_table;
    B_MASK                             b_m;
    // lsq_tail
    SQ_POINTER                         sq_tail;
    SQ_MASK                            sq_mask;
    BRANCH_PREDICTOR_PACKET            bp_packet;
    logic                              is_jump;
    ADDR                               original_PC;
} BS_ENTRY_PACKET;

typedef struct packed {
    // ADDR            PC;
    ROB_PACKET         [`N-1:0] rob_inputs; // Use as unique rob id
    logic       [$clog2(`ROB_SZ)-1:0] head;
    logic          [`ROB_SZ_BITS-1:0] rob_tail;
    logic      [`NUM_SCALAR_BITS-1:0] rob_spots;
    logic      [`NUM_SCALAR_BITS-1:0] rob_outputs_valid;
    ROB_PACKET          [`N-1:0] rob_outputs;
    logic [`ROB_NUM_ENTRIES_BITS-1:0] rob_num_entries;
} ROB_DEBUG;

typedef struct packed {
    logic [`RS_SZ-1:0] rs_valid;
    logic [`RS_SZ-1:0] rs_reqs;
} RS_DEBUG;

typedef struct packed {
    BS_ENTRY_PACKET [`B_MASK_WIDTH-1:0] branch_stack;
    BS_ENTRY_PACKET [`B_MASK_WIDTH-1:0] next_branch_stack;
    B_MASK b_mask_reg;
} BS_DEBUG;

// TODO: UPDATE FU PACKETS

typedef struct packed {
    INST            inst;
    logic           valid;
    ADDR            PC;
    ADDR            NPC; // PC + 4
    ALU_OPA_SELECT  opa_select; // ALU opa mux select (ALU_OPA_xxx *)
    ALU_OPB_SELECT  opb_select; // ALU opb mux select (ALU_OPB_xxx *)
    DATA            source_reg_1;
    DATA            source_reg_2;
    PHYS_REG_IDX    dest_reg_idx;
    ALU_FUNC        alu_func;
} ALU_PACKET;

const ALU_PACKET NOP_ALU_PACKET = '{
    inst:          `NOP,   // Assuming 0 represents a NOP instruction
    valid:         '0,
    PC:            '0,   // No valid program counter
    NPC:           '0,   // No valid next PC
    opa_select:    OPA_IS_RS1, // Assuming ALU_OPA_ZERO means no operation
    opb_select:    OPB_IS_RS2, // Assuming ALU_OPB_ZERO means no operation
    source_reg_1:  '0,   // No valid source register
    source_reg_2:  '0,   // No valid source register
    dest_reg_idx:  '0,   // No valid destination register
    alu_func:       0
};

typedef struct packed {
    logic           valid;
    DATA            source_reg_1;
    DATA            source_reg_2;
    PHYS_REG_IDX    dest_reg_idx;
    B_MASK          bm;
    MULT_FUNC       mult_func;   
} MULT_PACKET;

typedef struct packed {
    logic            valid;
    logic [63:0]     prev_sum;
    logic [63:0]     mplier;
    logic [63:0]     mcand;
    PHYS_REG_IDX     dest_reg_idx;
    B_MASK           bm;
    MULT_FUNC        func;
} INTERNAL_MULT_PACKET;

const MULT_PACKET NOP_MULT_PACKET = '{
    valid:         '0,
    source_reg_1:  '0,   // No valid source register
    source_reg_2:  '0,   // No valid source register
    dest_reg_idx:  '0,   // No valid destination register
    bm:            '0,   // No valid branch mask
    mult_func:      0   
};

typedef struct packed {
    INST            inst;
    logic           valid;
    ADDR            PC;
    ADDR            NPC; // PC + 4
    ADDR            predicted_PC;
    logic           conditional;
    ALU_OPA_SELECT  opa_select; // ALU opa mux select (ALU_OPA_xxx *)
    ALU_OPB_SELECT  opb_select; // ALU opb mux select (ALU_OPB_xxx *)
    DATA            source_reg_1;
    DATA            source_reg_2;
    PHYS_REG_IDX    dest_reg_idx;       // not used but might be good for identification purposes
    logic           predict_taken;
    BRANCH_FUNC     branch_func;    // comparator used for branch
    B_MASK_MASK     bmm;            // this branch's corresponding mask
} BRANCH_PACKET;

const BRANCH_PACKET NOP_BRANCH_PACKET = '{
    inst:               `NOP,
    valid:              '0,
    PC:                 '0,
    NPC:                '0, // PC + 4
    predicted_PC:       '0,
    conditional:        '0,
    opa_select:         OPA_IS_RS1, // ALU opa mux select (ALU_OPA_xxx *)
    opb_select:         OPB_IS_RS2, // ALU opb mux select (ALU_OPB_xxx *)
    source_reg_1:       '0,
    source_reg_2:       '0,
    dest_reg_idx:       '0,       // not used but might be good for identification purposes
    predict_taken:      '0,
    branch_func:        '0,    // comparator used for branch
    bmm:                '0            // this branch's corresponding mask
};

typedef struct packed {
    INST                     inst;
    ADDR                     PC;
    logic                    predict_taken;
    BRANCH_PREDICTOR_PACKET  bp_packet;
    ADDR                     predicted_PC; //only necessary for jumps
    logic                    is_jump;
} FETCH_PACKET;

typedef struct packed {
    PHYS_REG_IDX  completing_reg;
    logic         valid;
} CDB_ETB_PACKET;

typedef struct packed {
    DATA          result;
    PHYS_REG_IDX  completing_reg;
    logic         valid;
} CDB_REG_PACKET;

typedef struct packed {
    ADDR          target_PC;
    B_MASK        bmm;
    logic         bm_mispred;
    logic         predict_taken;
    logic         actual_taken;
    logic         valid;
} BRANCH_REG_PACKET;

typedef struct packed {
    PHYS_REG_IDX [`ARCH_REG_SZ_R10K-1:0] map_table;
    PHYS_REG_IDX [`ARCH_REG_SZ_R10K-1:0] next_map_table;
    FU_TYPE                     [`N-1:0] fu_type;
} DISPATCH_DEBUG;

// typedef struct packed {
//     BTB_TAG         btb_tag;
//     BTB_LRU         btb_lru;
//     logic           valid;
//     ADDR            target_PC;
// } BTB_ENTRY;

// typedef struct packed {
//     BTB_ENTRY [`BTB_NUM_WAYS-1:0] btb_entries;
//     BTB_NUM_ENTRY num_entry;
// } BTB_SET_PACKET;

typedef struct packed {
    logic place_holder_btb;
} BTB_DEBUG;

typedef struct packed {
    logic           valid;
    DATA            source_reg_1;
    DATA            source_reg_2;
    PHYS_REG_IDX    dest_reg_idx;
    B_MASK          bm;
    SQ_POINTER      sq_tail;
    LOAD_FUNC       load_func;
} LOAD_ADDR_PACKET;

const LOAD_ADDR_PACKET NOP_LOAD_ADDR_PACKET = '{
    valid:              '0,
    source_reg_1:       '0,
    source_reg_2:       '0,
    dest_reg_idx:       '0,       // not used but might be good for identification purposes
    bm:                 '0,
    sq_tail:            '0,
    load_func:          '0
};

typedef struct packed {
    logic           valid;
    PHYS_REG_IDX    dest_reg_idx;
    BYTE_MASK       byte_mask;
    ADDR            load_addr;
    B_MASK          bm;
    SQ_POINTER          sq_tail;
    LOAD_FUNC       load_func;
} LOAD_DATA_PACKET;

const LOAD_DATA_PACKET NOP_LOAD_DATA_PACKET = '{
    valid:         '0,
    dest_reg_idx:  '0,
    byte_mask:     '0,
    load_addr:     '0,
    bm:            '0,
    sq_tail:       '0,
    load_func:     '0
};

typedef struct packed {
    BYTE_MASK       byte_mask;
    MSHR_IDX        mshr_idx;
    logic           valid;
    ADDR            load_addr;
    DATA            result;
    B_MASK          bm;
    PHYS_REG_IDX    dest_reg_idx;
    LOAD_FUNC       load_func;
} LOAD_BUFFER_PACKET; 

const LOAD_BUFFER_PACKET NOP_LOAD_BUFFER_PACKET = '{
    byte_mask:          '0,
    mshr_idx:           '0,
    valid:              '0,
    load_addr:          '0,
    result:             '0,
    bm:                 '0,
    dest_reg_idx:       '0,
    load_func:          '0
};

typedef struct packed {
    logic           valid;
    DATA            source_reg_1;
    DATA            source_reg_2;
    DATA            store_imm;
    SQ_MASK         sq_mask;
    STORE_FUNC      store_func;
    PHYS_REG_IDX    dest_reg_idx;
} STORE_ADDR_PACKET;

const STORE_ADDR_PACKET NOP_STORE_ADDR_PACKET = '{
    valid:              '0,
    source_reg_1:       '0,
    source_reg_2:       '0,
    store_imm:          '0,
    sq_mask:            '0,
    store_func:         '0,
    dest_reg_idx:           '0
};

typedef struct packed {
    logic           valid;
    ADDR            addr;
    DATA            result;
    BYTE_MASK       byte_mask;
    PHYS_REG_IDX    dest_reg_idx;
} STORE_QUEUE_PACKET;

const STORE_QUEUE_PACKET NOP_STORE_QUEUE_PACKET = '{
    valid:              '0,
    addr:               '0,
    result:             '0,
    byte_mask:          '0,
    dest_reg_idx:       '0
};

typedef struct packed {
    logic           valid;
    BYTE_MASK [1:0] byte_mask;
    DATA      [1:0] data;
    MSHR_IDX        mshr_idx;
} LOAD_DATA_CACHE_PACKET;

typedef struct packed {
    logic           valid;
    MSHR_IDX        mshr_idx;
    DATA      [1:0] data;
} LOAD_BUFFER_CACHE_PACKET;

typedef struct packed {
    logic           valid;
    logic           prior;
    ADDR            addr;
    DATA      [1:0] data;
} MEM_REQ_PACKET;

typedef struct packed {
    MEM_TAG         mem_tag;
    DATA      [1:0] data;
} MEM_DATA_PACKET;

typedef struct packed {
    ADDR            addr;
    DATA      [1:0] data;
} WB_ENTRY;

typedef struct packed {
    MEM_TAG         mem_tag;
    ADDR            addr;
} ICACHE_MSHR_ENTRY;

typedef struct packed {
    logic           valid;
    logic           dirty;
    MEM_TAG         mem_tag;
    ADDR            addr;
    DATA      [1:0] data;
    BYTE_MASK [1:0] byte_mask;
} DCACHE_MSHR_ENTRY;

typedef struct packed {
    logic           valid;
    ADDR            addr;
} ICACHE_META_DATA;

typedef struct packed {
    logic           valid;
    ADDR            addr;
    DCACHE_LRU      lru;
    logic           dirty;
} DCACHE_META_DATA;

typedef struct packed {
    logic           valid;
    ADDR            addr;
    VCACHE_LRU      lru;
    logic           dirty;
} VCACHE_META_DATA;

typedef struct packed {
    BTB_TAG         btb_tag;
    BTB_LRU         btb_lru;
    logic           valid;
    ADDR            target_PC;
} BTB_ENTRY;

typedef struct packed {
    logic nothong;
} LDST_PACKET;
`endif // __SYS_DEFS_SVH__