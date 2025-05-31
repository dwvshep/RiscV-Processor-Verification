// ROB Verification
// Date: 09 May 2025
`include "sys_defs.svh"
import uvm_pkg::*;
import rob_pkg::*;
`include "uvm_macros.svh"
`include "intf.sv"
`include "dut.sv"
`include "sva.svh"

//--------------------------------------------------------
//Included Files
//--------------------------------------------------------
// `include "sequence_item.sv"
// `include "driver.sv"
// `include "monitor.sv"
// `include "sequencer.sv"
// `include "agent.sv"
// `include "scoreboard.sv"
// `include "coverage.sv"
// `include "env.sv"
// `include "dut.sv"
// `include "intf.sv"
// `include "test.sv"
// `include "base_seq.sv"
// `include "reset_seq.sv"
// `include "random_seq.sv"
// `include "sva.svh"



module top;

    //--------------------------------------------------------
    //Instantiation
    //--------------------------------------------------------

    logic clock;
    logic reset;

    rob_interface intf(.clock(clock), .reset(reset));
    
    rob dut (
        .clock             (intf.clock),
        .reset             (intf.reset),
        .rob_inputs        (intf.rob_inputs),
        .rob_inputs_valid  (intf.rob_inputs_valid), 
        .rob_spots         (intf.rob_spots),
        .rob_tail          (intf.rob_tail),
        .num_retiring      (intf.num_retiring),
        .rob_outputs       (intf.rob_outputs),
        .rob_outputs_valid (intf.rob_outputs_valid),
        .tail_restore_valid(intf.tail_restore_valid),
        .tail_restore      (intf.tail_restore),
        .rob_debug         (intf.rob_debug)
    );
    
    ROB_sva DUT_sva (
        .clock             (intf.clock),
        .reset             (intf.reset),
        .rob_inputs        (intf.rob_inputs),
        .rob_inputs_valid  (intf.rob_inputs_valid), 
        .rob_spots         (intf.rob_spots),
        .rob_tail          (intf.rob_tail),
        .num_retiring      (intf.num_retiring),
        .rob_outputs       (intf.rob_outputs),
        .rob_outputs_valid (intf.rob_outputs_valid),
        .tail_restore_valid(intf.tail_restore_valid),
        .tail_restore      (intf.tail_restore),
        .rob_debug         (intf.rob_debug)
    );
    
    
    //--------------------------------------------------------
    //Interface Setting
    //--------------------------------------------------------
    initial begin
        uvm_config_db #(virtual rob_interface)::set(null, "*", "vif", intf );
        //-- Refer: https://www.synopsys.com/content/dam/synopsys/services/whitepapers/hierarchical-testbench-configuration-using-uvm.pdf
    end
    
    
    
    //--------------------------------------------------------
    //Start The Test
    //--------------------------------------------------------
    initial begin
        run_test("rob_test");
    end
    
    
    //--------------------------------------------------------
    //Clock Generation
    //--------------------------------------------------------
    initial begin
        reset = 1;
        clock = 0;
        #5;
        forever begin
            clock = ~clock;
            #5;
            reset = 0;
        end
    end
    
    
    //--------------------------------------------------------
    //Maximum Simulation Time
    //--------------------------------------------------------
    initial begin
        #5000000;
        $display("Sorry! Ran out of clock cycles!");
        $finish();
    end
    
    
    //--------------------------------------------------------
    //Generate Waveforms
    //--------------------------------------------------------
    initial begin
        $dumpfile("build/rob.vcd");
        $dumpvars();
    end
    // initial begin
    //     $vcdplusfile("build/rob.vpd");
    //     $vcdpluson(0, top);  // Replace 'top' with your top module name
    // end
    
endmodule: top