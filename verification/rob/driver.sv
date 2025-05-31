class rob_driver extends uvm_driver#(rob_sequence_item);
    `uvm_component_utils(rob_driver)
    
    virtual rob_interface vif;
    rob_sequence_item item;
    
    
    //--------------------------------------------------------
    //Constructor
    //--------------------------------------------------------
    function new(string name = "rob_driver", uvm_component parent);
        super.new(name, parent);
        `uvm_info("DRIVER_CLASS", "Inside Constructor!", UVM_HIGH)
    endfunction: new
    
    
    //--------------------------------------------------------
    //Build Phase
    //--------------------------------------------------------
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("DRIVER_CLASS", "Build Phase!", UVM_HIGH)
        
        if(!(uvm_config_db #(virtual rob_interface)::get(this, "*", "vif", vif))) begin
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
            item = rob_sequence_item::type_id::create("item");
            seq_item_port.get_next_item(item);
            drive(item);
            seq_item_port.item_done();
        end
        
    endtask: run_phase
    
    
    //--------------------------------------------------------
    //[Method] Drive
    //--------------------------------------------------------
    task drive(rob_sequence_item item);
        // @(posedge vif.clock);
        // wait(^vif.rob_spots !== 1'bx);
        // wait(^vif.rob_outputs_valid !== 1'bx);
        // wait(^vif.rob_debug !== 1'bx);
        // #0
        // vif.reset <= item.reset;
        vif.rob_inputs <= item.rob_inputs;
        vif.rob_inputs_valid <= item.rob_inputs_valid;
        vif.num_retiring <= item.num_retiring;
        vif.tail_restore_valid <= item.tail_restore_valid;
        vif.tail_restore <= item.tail_restore;
    endtask: drive
    
    
endclass: rob_driver