class rob_monitor extends uvm_monitor;
    `uvm_component_utils(rob_monitor)
    
    virtual rob_interface vif;
    rob_sequence_item item;
    
    uvm_analysis_port #(rob_sequence_item) monitor_port;
    
    
    //--------------------------------------------------------
    //Constructor
    //--------------------------------------------------------
    function new(string name = "rob_monitor", uvm_component parent);
        super.new(name, parent);
        `uvm_info("MONITOR_CLASS", "Inside Constructor!", UVM_HIGH)
    endfunction: new
    
    
    //--------------------------------------------------------
    //Build Phase
    //--------------------------------------------------------
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("MONITOR_CLASS", "Build Phase!", UVM_HIGH)
        
        monitor_port = new("monitor_port", this);
        
        if(!(uvm_config_db #(virtual rob_interface)::get(this, "*", "vif", vif))) begin
            `uvm_error("MONITOR_CLASS", "Failed to get VIF from config DB!")
        end
        
    endfunction: build_phase
    
    //--------------------------------------------------------
    //Connect Phase
    //--------------------------------------------------------
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info("MONITOR_CLASS", "Connect Phase!", UVM_HIGH)
        
    endfunction: connect_phase
    
    
    //--------------------------------------------------------
    //Run Phase
    //--------------------------------------------------------
    task run_phase (uvm_phase phase);
        super.run_phase(phase);
        `uvm_info("MONITOR_CLASS", "Inside Run Phase!", UVM_HIGH)
        
        forever begin
            item = rob_sequence_item::type_id::create("item");
            
            // wait(!vif.reset);
            
            @(posedge vif.clock);
            // if (!vif.reset) begin
            //     wait(^vif.rob_spots !== 1'bx);
            //     wait(^vif.rob_outputs_valid !== 1'bx);
            //     wait(^vif.rob_debug !== 1'bx);
            // end
            #0;
            // uvm_config_db#(logic [`NUM_SCALAR_BITS-1:0])::set(null, "*", "rob_spots", vif.rob_spots);
            // uvm_config_db#(logic [`NUM_SCALAR_BITS-1:0])::set(null, "*", "rob_outputs_valid", vif.rob_outputs_valid);
            // uvm_config_db#(ROB_DEBUG)::set(null, "*", "rob_debug", vif.rob_debug);

            //sample inputs
            item.reset = vif.reset;
            item.rob_inputs = vif.rob_inputs;
            item.rob_inputs_valid = vif.rob_inputs_valid;
            item.num_retiring = vif.num_retiring;
            item.tail_restore_valid = vif.tail_restore_valid;
            item.tail_restore = vif.tail_restore;
            
            //sample outputs
            item.rob_spots = vif.rob_spots;
            item.rob_tail = vif.rob_tail;
            item.rob_outputs = vif.rob_outputs;
            item.rob_outputs_valid = vif.rob_outputs_valid;
            item.rob_debug = vif.rob_debug;
            
            // send item to scoreboard
            monitor_port.write(item);
        end
            
    endtask: run_phase
    
endclass: rob_monitor