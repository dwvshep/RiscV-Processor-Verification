class rs_coverage extends uvm_subscriber #(rs_sequence_item);
  `uvm_component_utils(rs_coverage)

  //virtual rs_interface vif;
  rs_sequence_item item;
  uvm_analysis_imp #(rs_sequence_item, rs_coverage) coverage_port;

  // Removed clocking -  @(posedge vif.clock) to sync with monitor writes
  covergroup rs_cg;
    // Example: Cover num_dispatched
    cp_num_dispatched: coverpoint item.num_dispatched {
      bins zero = {0};
      bins nonzero = {[1:`N]};
    }

    cp_rs_spots: coverpoint item.rs_spots {
      bins zero = {0};
      bins nonzero = {[1:`N]};
    }

    // Example: Cover resolving_sq_mask scenarios
    cp_resolving_sq_mask: coverpoint item.resolving_sq_mask {
      bins zero = {0};
      bins nonzero = {[1:(2 ** `SQ_SZ) - 1]};
    }

    cp_b_mm_mispred: coverpoint item.b_mm_mispred;

    cp_b_mm_resolve: coverpoint item.b_mm_resolve {
      bins zero = {0};
      bins nonzero = {[1:(2 ** `B_MASK_WIDTH) - 1]};
    }

    // Example: Cross coverage
    // cross_valid_tail: cross cp_inputs_valid, cp_retiring, cp_tail_restore;
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    rs_cg = new();
  endfunction

  //--------------------------------------------------------
  //Build Phase
  //--------------------------------------------------------
  function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info("COVERAGE_CLASS", "Build Phase!", UVM_HIGH)

      coverage_port = new("coverage_port", this);
      
      // if(!(uvm_config_db #(virtual rs_interface)::get(this, "*", "vif", vif))) begin
      // `uvm_error("COVERAGE_CLASS", "Failed to get VIF from config DB!")
      // end
  endfunction: build_phase

  function void write(rs_sequence_item t);
    item = t;
    rs_cg.sample(); // sample the transaction data
  endfunction
endclass