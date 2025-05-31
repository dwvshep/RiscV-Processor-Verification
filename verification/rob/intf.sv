interface rob_interface(
    input logic clock,
    input logic reset
    );

    // ------------ TO/FROM DISPATCH ------------- //
    ROB_PACKET           [`N-1:0] rob_inputs;        // New instructions from Dispatch, MUST BE IN ORDER FROM OLDEST TO NEWEST INSTRUCTIONS
    logic  [`NUM_SCALAR_BITS-1:0] rob_inputs_valid;  // To distinguish invalid instructions being passed in from Dispatch (A number, NOT one hot)
    logic  [`NUM_SCALAR_BITS-1:0] rob_spots;         //number of spots available, saturated at N
    logic      [`ROB_SZ_BITS-1:0] rob_tail;

    // ------------- TO/FROM RETIRE -------------- //
    logic  [`NUM_SCALAR_BITS-1:0] num_retiring;      // Retire module tells the ROB how many entries can be cleared
    ROB_PACKET           [`N-1:0] rob_outputs;       // For retire to check eligibility
    logic  [`NUM_SCALAR_BITS-1:0] rob_outputs_valid; // If not all N rob entries are valid entries they should not be considered

    // ------------- FROM BRANCH STACK -------------- //
    logic                         tail_restore_valid;
    logic      [`ROB_SZ_BITS-1:0] tail_restore;

    ROB_DEBUG                     rob_debug;

endinterface: rob_interface