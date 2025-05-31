class rob_reset_sequence extends rob_base_sequence;
  `uvm_object_utils(rob_reset_sequence)
  
  rob_sequence_item reset_pkt;
  
  //--------------------------------------------------------
  //Constructor
  //--------------------------------------------------------
  function new(string name= "rob_reset_sequence");
    super.new(name);
    `uvm_info("RESET_SEQ", "Inside Constructor!", UVM_HIGH)
  endfunction
  
  
  //--------------------------------------------------------
  //Body Task
  //--------------------------------------------------------
  task body();
    `uvm_info("RESET_SEQ", "Inside body task!", UVM_HIGH)
    super.body();
    
    reset_pkt = rob_sequence_item::type_id::create("reset_pkt");
    
    @(posedge vif.clock);
    // wait(^vif.rob_spots !== 1'bx);
    // wait(^vif.rob_outputs_valid !== 1'bx);
    // wait(^vif.rob_debug !== 1'bx);
    #0;
    reset_pkt.rob_spots = vif.rob_spots;
    reset_pkt.rob_outputs_valid = vif.rob_outputs_valid;
    reset_pkt.rob_debug = vif.rob_debug;
    start_item(reset_pkt);
    reset_pkt.randomize() with {reset==1;};
    finish_item(reset_pkt);
        
  endtask: body
  
  
endclass: rob_reset_sequence