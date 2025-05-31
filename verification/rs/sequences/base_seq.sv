class rs_base_sequence extends uvm_sequence#(rs_sequence_item);
  `uvm_object_utils(rs_base_sequence)

  virtual rs_interface vif;
  rs_sequencer seqr;
  
//   rob_sequence_item item;
//   protected logic [`NUM_SCALAR_BITS-1:0] rob_spots;
//   protected logic [`NUM_SCALAR_BITS-1:0] rob_outputs_valid;
//   protected ROB_DEBUG                    rob_debug;
  
  //--------------------------------------------------------
  //Constructor
  //--------------------------------------------------------
  function new(string name= "rs_base_sequence");
    super.new(name);
    `uvm_info("BASE_SEQ", "Inside Constructor!", UVM_HIGH)
  endfunction
  
  
  //--------------------------------------------------------
  //Body Task
  //--------------------------------------------------------
  virtual task body();
    `uvm_info("BASE_SEQ", "Inside body task!", UVM_HIGH)
    
    $cast(seqr, m_sequencer);
    vif = seqr.vif;

    // if(!(uvm_config_db #(logic  [`NUM_SCALAR_BITS-1:0])::get(this, "*", "rob_spots", rob_spots))) begin
    //     `uvm_error("BASE_SEQ", "Failed to get rob_spots from config DB!")
    // end

    // if(!(uvm_config_db #(logic  [`NUM_SCALAR_BITS-1:0])::get(this, "*", "rob_outputs_valid", rob_outputs_valid))) begin
    //     `uvm_error("BASE_SEQ", "Failed to get rob_outputs_valid from config DB!")
    // end

    // if(!(uvm_config_db #(ROB_DEBUG)::get(this, "*", "rob_debug", rob_debug))) begin
    //     `uvm_error("BASE_SEQ", "Failed to get rob_debug from config DB!")
    // end
    
  endtask: body
  
  
endclass: rs_base_sequence