class rob_test extends uvm_test;
    `uvm_component_utils(rob_test)

    rob_env env;
    rob_reset_sequence reset_seq;
    rob_random_sequence rand_seq;

    
    //--------------------------------------------------------
    //Constructor
    //--------------------------------------------------------
    function new(string name = "rob_test", uvm_component parent);
        super.new(name, parent);
        `uvm_info("TEST_CLASS", "Inside Constructor!", UVM_HIGH)
    endfunction: new

    
    //--------------------------------------------------------
    //Build Phase
    //--------------------------------------------------------
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("TEST_CLASS", "Build Phase!", UVM_HIGH)

        env = rob_env::type_id::create("env", this);

    endfunction: build_phase

    
    //--------------------------------------------------------
    //Connect Phase
    //--------------------------------------------------------
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info("TEST_CLASS", "Connect Phase!", UVM_HIGH)

    endfunction: connect_phase

    
    //--------------------------------------------------------
    //Run Phase
    //--------------------------------------------------------
    task run_phase (uvm_phase phase);
        super.run_phase(phase);
        `uvm_info("TEST_CLASS", "Run Phase!", UVM_HIGH)

        phase.raise_objection(this);

        //reset_seq
        // reset_seq = rob_reset_sequence::type_id::create("reset_seq");
        // reset_seq.start(env.agnt.seqr);
        // #5;

        repeat(10000) begin
            //test_seq
            rand_seq = rob_random_sequence::type_id::create("rand_seq");
            rand_seq.start(env.agnt.seqr);
            //#10;
        end
        
        phase.drop_objection(this);

    endtask: run_phase

endclass: rob_test