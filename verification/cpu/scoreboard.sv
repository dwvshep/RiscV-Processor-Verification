class rob_scoreboard extends uvm_test;
  `uvm_component_utils(rob_scoreboard)
  
  uvm_analysis_imp #(rob_sequence_item, rob_scoreboard) scoreboard_port;
  
  rob_sequence_item transactions[$];
  
  ROB_PACKET shadow_rob[$];
  
  //--------------------------------------------------------
  //Constructor
  //--------------------------------------------------------
  function new(string name = "rob_scoreboard", uvm_component parent);
    super.new(name, parent);
    `uvm_info("SCB_CLASS", "Inside Constructor!", UVM_HIGH)
  endfunction: new
  
  
  //--------------------------------------------------------
  //Build Phase
  //--------------------------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("SCB_CLASS", "Build Phase!", UVM_HIGH)
   
    scoreboard_port = new("scoreboard_port", this);
    
  endfunction: build_phase
  
  
  //--------------------------------------------------------
  //Connect Phase
  //--------------------------------------------------------
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("SCB_CLASS", "Connect Phase!", UVM_HIGH)
    
   
  endfunction: connect_phase
  
  
  //--------------------------------------------------------
  //Write Method
  //--------------------------------------------------------
  function void write(rob_sequence_item item);
    transactions.push_back(item);
  endfunction: write 
  
  
  
  //--------------------------------------------------------
  //Run Phase
  //--------------------------------------------------------
  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("SCB_CLASS", "Run Phase!", UVM_HIGH)
   
    forever begin
      /*
      // get the packet
      // generate expected value
      // compare it with actual value
      // score the transactions accordingly
      */
      rob_sequence_item curr_trans;
      wait((transactions.size() != 0));
      curr_trans = transactions.pop_front();
      compare(curr_trans);
    end
    
  endtask: run_phase

  //--------------------------------------------------------
  //Compare : Generate Expected Result and Compare with Actual
  //--------------------------------------------------------
  task compare(rob_sequence_item curr_trans);

    //retire outputs
    for (int i = 0; i < `N; i++) begin
      if (i < curr_trans.rob_outputs_valid && i < curr_trans.num_retiring) begin
        if (shadow_rob.size() == 0) begin
          `uvm_error("ROB_SB", $sformatf("Transaction failed! Tried to retire with empty ROB!"))
        end else begin
          ROB_PACKET expected = shadow_rob.pop_front();
          if (expected !== curr_trans.rob_outputs[i]) begin
            `uvm_error("ROB_SB", $sformatf("Transaction failed! Mismatch at retire: expected dest_reg=%p, actual dest_reg=%p", expected.T_new, curr_trans.rob_outputs[i].T_new))
          end
        end
      end
    end

    //add inputs
    for (int i = 0; i < `N; i++) begin
      if (i < curr_trans.rob_inputs_valid) begin
        shadow_rob.push_back(curr_trans.rob_inputs[i]);
      end
    end

    //handle tail restoration
    if (curr_trans.tail_restore_valid) begin
      // calculate distance rolling back (d = tail_restore <= rob_tail ? rob_tail - tail_restore : rob_tail + `ROB_SZ - tail_restore)
      int d = (curr_trans.tail_restore <= curr_trans.rob_debug.rob_tail) ? (curr_trans.rob_debug.rob_tail - curr_trans.tail_restore) : (curr_trans.rob_debug.rob_tail + `ROB_SZ - curr_trans.tail_restore);
      if (d < shadow_rob.size()) begin
        shadow_rob = shadow_rob[0:shadow_rob.size() - 1 - d];
      end else begin
        `uvm_error("ROB_SB", $sformatf("Invalid tail_restore index: %0d", curr_trans.tail_restore))
      end
    end

    // handle reset
    if (curr_trans.reset) begin
        shadow_rob = {};
    end

  endtask: compare
  
  
endclass: rob_scoreboard