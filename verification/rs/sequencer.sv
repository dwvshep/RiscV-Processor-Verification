class rs_sequencer extends uvm_sequencer#(rs_sequence_item);
  `uvm_component_utils(rs_sequencer)
  
  virtual rs_interface vif;
  
  //--------------------------------------------------------
  //Constructor
  //--------------------------------------------------------
  function new(string name = "rs_sequencer", uvm_component parent);
    super.new(name, parent);
    `uvm_info("SEQR_CLASS", "Inside Constructor!", UVM_HIGH)
  endfunction: new
  
  
  //--------------------------------------------------------
  //Build Phase
  //--------------------------------------------------------
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("SEQR_CLASS", "Build Phase!", UVM_HIGH)

    if(!(uvm_config_db #(virtual rs_interface)::get(this, "*", "vif", vif))) begin
        `uvm_error("MONITOR_CLASS", "Failed to get VIF from config DB!")
    end

  endfunction: build_phase
  
  
  //--------------------------------------------------------
  //Connect Phase
  //--------------------------------------------------------
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("SEQR_CLASS", "Connect Phase!", UVM_HIGH)
    
  endfunction: connect_phase
  
  
  
endclass: rs_sequencer