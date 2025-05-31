interface rs_interface(
    input logic clock,
    input logic reset
    );

    // ------ TO/FROM: DISPATCH ------- //
    logic [`NUM_SCALAR_BITS-1:0] num_dispatched;      // Number of input RS packets actually coming from dispatch
    RS_PACKET           [`N-1:0] rs_entries;          // Input RS packets data
    logic [`NUM_SCALAR_BITS-1:0] rs_spots;            // Number of spots
    
    // --------- FROM: CDB ------------ //
    CDB_ETB_PACKET      [`N-1:0] ETB_tags;            // Tags that are broadcasted from the CDB
    
    // --------- FROM: STORE UNIT ------------ //
    SQ_MASK                      resolving_sq_mask;

    // ------- TO/FROM: ISSUE --------- //
    logic           [`RS_SZ-1:0] rs_data_issuing;      // bit vector of rs_data that is being issued by issue stage
    RS_PACKET       [`RS_SZ-1:0] rs_data_next;        // The entire RS data 
    logic           [`RS_SZ-1:0] rs_valid_issue;       // 1 if RS data is valid, seperate from next_rs_valid since it shouldn't include dispatched instructions

    // ------- FROM: BRANCH STACK --------- //
    B_MASK_MASK                   b_mm_resolve;         // b_mask_mask to resolve
    logic                         b_mm_mispred;          // 1 if mispredict happens
    RS_DEBUG                      rs_debug;

endinterface: rs_interface