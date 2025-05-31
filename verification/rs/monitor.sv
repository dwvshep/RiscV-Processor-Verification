class rs_monitor extends uvm_monitor;
    `uvm_component_utils(rs_monitor)
    
    virtual rs_interface vif;
    rs_sequence_item item;
    
    uvm_analysis_port #(rs_sequence_item) monitor_port;
    
    
    //--------------------------------------------------------
    //Constructor
    //--------------------------------------------------------
    function new(string name = "rs_monitor", uvm_component parent);
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
        
        if(!(uvm_config_db #(virtual rs_interface)::get(this, "*", "vif", vif))) begin
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
            item = rs_sequence_item::type_id::create("item");
            
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
            item.num_dispatched = vif.num_dispatched;
            item.rs_entries = vif.rs_entries;
            item.ETB_tags = vif.ETB_tags;
            item.b_mm_resolve = vif.b_mm_resolve;
            item.b_mm_mispred = vif.b_mm_mispred;
            item.resolving_sq_mask = vif.resolving_sq_mask;
            item.rs_data_issuing = vif.rs_data_issuing;
            
            
            //sample outputs
            item.rs_valid_issue = vif.rs_valid_issue;
            item.rs_spots = vif.rs_spots;
            item.rs_data_next = vif.rs_data_next;
            item.rs_debug = vif.rs_debug;
            
            // send item to scoreboard
            monitor_port.write(item);
        end
            
    endtask: run_phase
    
endclass: rs_monitor