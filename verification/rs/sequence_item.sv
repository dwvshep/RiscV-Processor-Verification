class rs_sequence_item extends uvm_sequence_item; 
    `uvm_object_utils(rs_sequence_item)

    //--------------------------------------------------------
    //Instantiation
    //--------------------------------------------------------
    //input   logic                        clock, 
    rand  logic                        reset;

    // ------ TO/FROM: DISPATCH ------- //
    rand  logic [`NUM_SCALAR_BITS-1:0] num_dispatched;      // Number of input RS packets actually coming from dispatch
    rand  RS_PACKET           [`N-1:0] rs_entries;          // Input RS packets data
    logic       [`NUM_SCALAR_BITS-1:0] rs_spots;            // Number of spots
    
    // --------- FROM: CDB ------------ //
    rand  CDB_ETB_PACKET      [`N-1:0] ETB_tags;            // Tags that are broadcasted from the CDB
    
    // --------- FROM: STORE UNIT ------------ //
    rand  SQ_MASK                      resolving_sq_mask;

    // ------- TO/FROM: ISSUE --------- //
    rand  logic           [`RS_SZ-1:0] rs_data_issuing;      // bit vector of rs_data that is being issued by issue stage
    RS_PACKET             [`RS_SZ-1:0] rs_data_next;        // The entire RS data 
    logic                 [`RS_SZ-1:0] rs_valid_issue;       // 1 if RS data is valid, seperate from next_rs_valid since it shouldn't include dispatched instructions

    // ------- FROM: BRANCH STACK --------- //
    rand B_MASK_MASK                   b_mm_resolve;         // b_mask_mask to resolve
    rand logic                         b_mm_mispred;          // 1 if mispredict happens
    RS_DEBUG                           rs_debug;

    //--------------------------------------------------------
    //Default Constraints
    //--------------------------------------------------------
    constraint num_dispatched_c {
        if (!reset) 
            //num_dispatched inside {[0:rs_spots]};
            num_dispatched == rs_spots;
    }
    constraint rs_input_sources_c {
        if (!reset) 
            foreach (rs_entries[i]) {
                rs_entries[i].Source1 inside {[0:`PHYS_REG_SZ_R10K]};
                rs_entries[i].Source2 inside {[0:`PHYS_REG_SZ_R10K]};
                foreach (ETB_tags[i])
                    if (rs_entries[i].Source1 == ETB_tags[i].completing_reg)
                        rs_entries[i].Source1_ready == 1;
                    if (rs_entries[i].Source2 == ETB_tags[i].completing_reg)
                        rs_entries[i].Source2_ready == 1;
                rs_entries[i].T_new inside {[0:`PHYS_REG_SZ_R10K]};
                (rs_entries[i].b_mask & b_mm_resolve) == 0;
            }
    }
    constraint etb_tags_c {
        if (!reset) 
            foreach (ETB_tags[i]) {
                ETB_tags[i].completing_reg inside {[0:`PHYS_REG_SZ_R10K]};
            }
    }
    constraint bmm_mispred_c {
        if (!reset)
            b_mm_mispred dist {0 := 90, 1 := 10};
    }
    constraint bmm_resolve_c {
        if (!reset)
            $onehot(b_mm_resolve);
    }
    constraint resolving_sq_mask_c {
        if (!reset)
            $onehot(resolving_sq_mask);
    }
    constraint rs_data_issuing_c {
        if (!reset)
            (rs_data_issuing & ~rs_valid_issue) == '0;
            // $countones(rs_data_issuing) inside {[0:`NUM_FU_TOTAL]};
            $countones(rs_data_issuing) dist {
                0 := 69,
                [1:`N] := 30,
                [`N+1:`NUM_FU_TOTAL] := 1
            };
    }

    //--------------------------------------------------------
    //Constructor
    //--------------------------------------------------------
    function new(string name = "rs_sequence_item");
        super.new(name);

    endfunction: new

endclass: rs_sequence_item