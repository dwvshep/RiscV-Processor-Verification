class rs_random_sequence extends rs_base_sequence;
  `uvm_object_utils(rs_random_sequence)
  
  rs_sequence_item rand_pkt;

  //--------------------------------------------------------
  //Constructor
  //--------------------------------------------------------
  function new(string name= "rs_random_sequence");
    super.new(name);
    `uvm_info("RAND_SEQ", "Inside Constructor!", UVM_HIGH)
  endfunction
  
  
  //--------------------------------------------------------
  //Body Task
  //--------------------------------------------------------
  virtual task body();
    `uvm_info("RAND_SEQ", "Inside body task!", UVM_HIGH)
    super.body();

    rand_pkt = rs_sequence_item::type_id::create("rand_pkt");

    //no shot this is correct
    @(posedge vif.clock);
    @(negedge vif.clock);
    rand_pkt.rs_spots = vif.rs_spots;
    rand_pkt.rs_debug = vif.rs_debug;
    rand_pkt.rs_valid_issue = vif.rs_valid_issue;
    rand_pkt.randomize() with {
      reset==0;
      rs_data_issuing==0;  
    };
    start_item(rand_pkt);
    rand_pkt.randomize() with {reset==0;};
    finish_item(rand_pkt);
    
  endtask: body
  
  
endclass: rs_random_sequence