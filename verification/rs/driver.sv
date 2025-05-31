class rs_driver extends uvm_driver#(rs_sequence_item);
    `uvm_component_utils(rs_driver)
    
    virtual rs_interface vif;
    rs_sequence_item item;
    
    
    //--------------------------------------------------------
    //Constructor
    //--------------------------------------------------------
    function new(string name = "rs_driver", uvm_component parent);
        super.new(name, parent);
        `uvm_info("DRIVER_CLASS", "Inside Constructor!", UVM_HIGH)
    endfunction: new
    
    
    //--------------------------------------------------------
    //Build Phase
    //--------------------------------------------------------
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("DRIVER_CLASS", "Build Phase!", UVM_HIGH)
        
        if(!(uvm_config_db #(virtual rs_interface)::get(this, "*", "vif", vif))) begin
        `uvm_error("DRIVER_CLASS", "Failed to get VIF from config DB!")
        end
        
    endfunction: build_phase
    
    
    //--------------------------------------------------------
    //Connect Phase
    //--------------------------------------------------------
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info("DRIVER_CLASS", "Connect Phase!", UVM_HIGH)
        
    endfunction: connect_phase
    
    
    //--------------------------------------------------------
    //Run Phase
    //--------------------------------------------------------
    task run_phase (uvm_phase phase);
        super.run_phase(phase);
        `uvm_info("DRIVER_CLASS", "Inside Run Phase!", UVM_HIGH)
        
        forever begin
            item = rs_sequence_item::type_id::create("item");
            seq_item_port.get_next_item(item);
            drive(item);
            seq_item_port.item_done();
        end
        
    endtask: run_phase
    
    
    //--------------------------------------------------------
    //[Method] Drive
    //--------------------------------------------------------
    task drive(rs_sequence_item item);
        // @(posedge vif.clock);
        // wait(^vif.rob_spots !== 1'bx);
        // wait(^vif.rob_outputs_valid !== 1'bx);
        // wait(^vif.rob_debug !== 1'bx);
        // #0
        // vif.reset <= item.reset;
        vif.num_dispatched <= item.num_dispatched;
        vif.rs_entries <= item.rs_entries;
        vif.ETB_tags <= item.ETB_tags;
        vif.resolving_sq_mask <= item.resolving_sq_mask;
        vif.rs_data_issuing <= item.rs_data_issuing;
        vif.b_mm_resolve <= item.b_mm_resolve;
        vif.b_mm_mispred <= item.b_mm_mispred;
    endtask: drive
    
    
endclass: rs_driver