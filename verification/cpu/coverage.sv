class rob_coverage extends uvm_subscriber #(rob_sequence_item);
  `uvm_component_utils(rob_coverage)

  //virtual rob_interface vif;
  rob_sequence_item item;
  uvm_analysis_imp #(rob_sequence_item, rob_coverage) coverage_port;

  // Removed clocking -  @(posedge vif.clock) to sync with monitor writes
  covergroup rob_cg;
    // Example: Cover valid bits
    cp_inputs_valid: coverpoint item.rob_inputs_valid {
      bins zero = {0};
      bins nonzero = {[1:`N]};
    }

    cp_retiring: coverpoint item.num_retiring {
      bins zero = {0};
      bins nonzero = {[1:`N]};
    }

    // Example: Cover tail restore scenarios
    cp_tail_restore: coverpoint item.tail_restore {
      bins zero = {0};
      bins nonzero = {[1:`ROB_SZ - 1]};
    }

    cp_restore_valid: coverpoint item.tail_restore_valid;

    // Example: Cover rob_spots scenarios
    cp_spots: coverpoint item.rob_spots {
      bins zero = {0};
      bins nonzero = {[1:`N]};
    }

    // Example: Cover num_entries scenarios
    cp_num_entries: coverpoint item.rob_debug.rob_num_entries {
      bins empty = {0};
      bins few = {[1:`N]};
      bins some = {[`N:`ROB_SZ - `N - 1]};
      bins many = {[`ROB_SZ - `N : `ROB_SZ - 1]};
      bins full = {`ROB_SZ};
    }

    // Example: Cross coverage
    cross_valid_tail: cross cp_inputs_valid, cp_retiring, cp_tail_restore;
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    rob_cg = new();
  endfunction

  //--------------------------------------------------------
  //Build Phase
  //--------------------------------------------------------
  function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info("COVERAGE_CLASS", "Build Phase!", UVM_HIGH)

      coverage_port = new("coverage_port", this);
      
      // if(!(uvm_config_db #(virtual rob_interface)::get(this, "*", "vif", vif))) begin
      // `uvm_error("COVERAGE_CLASS", "Failed to get VIF from config DB!")
      // end
  endfunction: build_phase

  function void write(rob_sequence_item t);
    item = t;
    rob_cg.sample(); // sample the transaction data
  endfunction
endclass