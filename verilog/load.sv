`include "verilog/sys_defs.svh"

// This is a pipelined multiplier that multiplies two 64-bit integers and
// returns the low 64 bits of the result.
// This is not an ideal multiplier but is sufficient to allow a faster clock
// period than straight multiplication.

module load # (
) (
    input logic                                 clock,
    input logic                                 reset, 
    
    // ------------ TO/FROM EXECUTE ------------- //
    input LOAD_ADDR_PACKET                      load_addr_packet,
    output logic                                load_addr_free,

    // ------------ TO/FROM ISSUE ------------- //
    input logic           [`LOAD_BUFFER_SZ-1:0] load_cdb_en,
    output logic          [`LOAD_BUFFER_SZ-1:0] load_cdb_req,

    // ------------ TO CDB ------------- //
    output CDB_REG_PACKET [`LOAD_BUFFER_SZ-1:0] load_result,

    // ------------ FROM BRANCH STACK --------------//
    input B_MASK                                b_mm_resolve,
    input logic                                 b_mm_mispred,

    // ------------ TO/FROM CACHE --------------//
    input LOAD_DATA_CACHE_PACKET                load_data_cache_packet,
    input LOAD_BUFFER_CACHE_PACKET              load_buffer_cache_packet,
    output logic                                load_req_valid,

    // ------------ TO/FROM STORE QUEUE ------------- //
    input DATA                      sq_load_data,
    input BYTE_MASK                 sq_data_mask,
    output SQ_POINTER               load_sq_tail,
    output ADDR                     load_req_addr //also goes to cache
);

    logic load_data_free;
    LOAD_DATA_PACKET load_data_packet;
    logic load_buffer_free;
    LOAD_BUFFER_PACKET load_buffer_packet;

    // instantiate an array of mult_stage modules
    // this uses concatenation syntax for internal wiring, see lab 2 slides
    load_addr_stage load_addr_stage (
        .clock (clock),
        .reset (reset),
        .load_addr_packet_in (load_addr_packet),
        .load_addr_free (load_addr_free),
        .load_data_free (load_data_free),
        .load_data_packet (load_data_packet),
        .load_buffer_free (load_buffer_free),
        .b_mm_mispred (b_mm_mispred),
        .b_mm_resolve (b_mm_resolve)
    );

    load_data_stage load_data_stage (
        .clock(clock),
        .reset(reset),
        .load_data_packet_in(load_data_packet),
        .load_data_free(load_data_free),
        .load_data_cache_packet(load_data_cache_packet),
        .load_req_valid(load_req_valid),
        .sq_load_data(sq_load_data), //input from SQ
        .sq_data_mask(sq_data_mask), //input from SQ
        .load_sq_tail(load_sq_tail),    //output to SQ
        .load_req_addr(load_req_addr), //goes to SQ and CACHE
        .load_buffer_packet(load_buffer_packet), //to Load Buffer
        .b_mm_mispred(b_mm_mispred),
        .b_mm_resolve(b_mm_resolve)
    );

    load_buffer load_buffer (
        .clock(clock), 
        .reset(reset),
        .load_buffer_packet_in(load_buffer_packet), // New instructions from Dispatch, MUST BE IN ORDER FROM OLDEST TO NEWEST INSTRUCTIONS
        .load_buffer_free(load_buffer_free),
        .load_buffer_cache_packet(load_buffer_cache_packet),
        .load_cdb_gnt(load_cdb_en),
        .load_cdb_req(load_cdb_req),
        .load_result(load_result),
        .b_mm_mispred(b_mm_mispred),
        .b_mm_resolve(b_mm_resolve)
    );
endmodule // mult