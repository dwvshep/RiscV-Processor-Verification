class rob_random_sequence extends rob_base_sequence;
  `uvm_object_utils(rob_random_sequence)
  
  rob_sequence_item rand_pkt;

  //--------------------------------------------------------
  //Constructor
  //--------------------------------------------------------
  function new(string name= "rob_random_sequence");
    super.new(name);
    `uvm_info("RAND_SEQ", "Inside Constructor!", UVM_HIGH)
  endfunction
  
  
  //--------------------------------------------------------
  //Body Task
  //--------------------------------------------------------
  virtual task body();
    `uvm_info("RAND_SEQ", "Inside body task!", UVM_HIGH)
    super.body();

    rand_pkt = rob_sequence_item::type_id::create("rand_pkt");

    @(posedge vif.clock);
    // wait(^vif.rob_spots !== 1'bx);
    // wait(^vif.rob_outputs_valid !== 1'bx);
    // wait(^vif.rob_debug !== 1'bx);
    #0;
    @(negedge vif.clock);
    rand_pkt.rob_spots = vif.rob_spots;
    rand_pkt.rob_outputs_valid = vif.rob_outputs_valid;
    rand_pkt.rob_debug = vif.rob_debug;
    start_item(rand_pkt);
    rand_pkt.randomize() with {reset==0;};
    finish_item(rand_pkt);
    
  endtask: body
  
  
endclass: rob_random_sequence