class rob_sequence_item extends uvm_sequence_item; 
    `uvm_object_utils(rob_sequence_item)

    //--------------------------------------------------------
    //Instantiation
    //--------------------------------------------------------
    //input   logic                        clock, 
    rand  logic                           reset;

    // ------------ TO/FROM DISPATCH ------------- //
    rand  ROB_PACKET             [`N-1:0] rob_inputs;        // New instructions from Dispatch, MUST BE IN ORDER FROM OLDEST TO NEWEST INSTRUCTIONS
    rand  logic    [`NUM_SCALAR_BITS-1:0] rob_inputs_valid;  // To distinguish invalid instructions being passed in from Dispatch (A number, NOT one hot)
    logic          [`NUM_SCALAR_BITS-1:0] rob_spots;  //output       //number of spots available, saturated at N
    logic              [`ROB_SZ_BITS-1:0] rob_tail;   //output

    // ------------- TO/FROM RETIRE -------------- //
    rand  logic    [`NUM_SCALAR_BITS-1:0] num_retiring;      // Retire module tells the ROB how many entries can be cleared
    ROB_PACKET                   [`N-1:0] rob_outputs;  //output     // For retire to check eligibility
    logic          [`NUM_SCALAR_BITS-1:0] rob_outputs_valid; //output // If not all N rob entries are valid entries they should not be considered

    // ------------- FROM BRANCH STACK -------------- //
    rand  logic                           tail_restore_valid;
    rand  logic        [`ROB_SZ_BITS-1:0] tail_restore;

    ROB_DEBUG                             rob_debug;  //output

    //--------------------------------------------------------
    //Default Constraints
    //--------------------------------------------------------
    constraint rob_inputs_c {
        if (!reset) 
            if (!tail_restore_valid)
                //rob_inputs_valid inside {[0:rob_spots]};
                rob_inputs_valid == rob_spots;
            else
                rob_inputs_valid == 0;
    }
    constraint num_retiring_c {if (!reset) num_retiring inside {[0:rob_outputs_valid]};}
    constraint tail_restore_valid_c {
        if (!reset) 
            if (rob_debug.rob_num_entries - num_retiring == 0) 
                tail_restore_valid == 0;
            else
                tail_restore_valid dist {0 := 90, 1 := 10};
    }
    constraint tail_restore_c {
        if (!reset)
            if (rob_debug.head < rob_debug.rob_tail)
                tail_restore inside {[rob_debug.head + 1 + num_retiring:rob_debug.rob_tail]};
            else
                if (rob_debug.head + 1 + num_retiring > `ROB_SZ)
                    tail_restore inside {[rob_debug.head + 1 + num_retiring - `ROB_SZ:rob_debug.rob_tail]};
                else
                    tail_restore inside {[rob_debug.head + 1 + num_retiring:`ROB_SZ - 1], [0:rob_debug.rob_tail]};
    }

    //--------------------------------------------------------
    //Constructor
    //--------------------------------------------------------
    function new(string name = "rob_sequence_item");
        super.new(name);

    endfunction: new

endclass: rob_sequence_item