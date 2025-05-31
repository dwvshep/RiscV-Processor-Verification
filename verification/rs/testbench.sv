// RS Verification
// Date: 22 May 2025
`include "sys_defs.svh"
import uvm_pkg::*;
import rs_pkg::*;
`include "uvm_macros.svh"
`include "intf.sv"
`include "psel_gen.sv"
`include "count_ones.sv"
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

    rs_interface intf(.clock(clock), .reset(reset));
    
    rs dut (
        .clock             (intf.clock),
        .reset             (intf.reset),
        .num_dispatched    (intf.num_dispatched),
        .rs_entries        (intf.rs_entries), 
        .rs_spots          (intf.rs_spots),
        .ETB_tags          (intf.ETB_tags),
        .resolving_sq_mask (intf.resolving_sq_mask),
        .rs_data_issuing   (intf.rs_data_issuing),
        .rs_data_next      (intf.rs_data_next),
        .rs_valid_issue    (intf.rs_valid_issue),
        .b_mm_resolve      (intf.b_mm_resolve),
        .b_mm_mispred      (intf.b_mm_mispred),
        .rs_debug          (intf.rs_debug)
    );
    
    RS_sva DUT_sva (
        .clock             (intf.clock),
        .reset             (intf.reset),
        .num_dispatched    (intf.num_dispatched),
        .rs_entries        (intf.rs_entries), 
        .rs_spots          (intf.rs_spots),
        .ETB_tags          (intf.ETB_tags),
        .resolving_sq_mask (intf.resolving_sq_mask),
        .rs_data_issuing   (intf.rs_data_issuing),
        .rs_data_next      (intf.rs_data_next),
        .rs_valid_issue    (intf.rs_valid_issue),
        .b_mm_resolve      (intf.b_mm_resolve),
        .b_mm_mispred      (intf.b_mm_mispred),
        .rs_debug          (intf.rs_debug)
    );
    
    
    //--------------------------------------------------------
    //Interface Setting
    //--------------------------------------------------------
    initial begin
        uvm_config_db #(virtual rs_interface)::set(null, "*", "vif", intf );
        //-- Refer: https://www.synopsys.com/content/dam/synopsys/services/whitepapers/hierarchical-testbench-configuration-using-uvm.pdf
    end
    
    
    
    //--------------------------------------------------------
    //Start The Test
    //--------------------------------------------------------
    initial begin
        run_test("rs_test");
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
        $dumpfile("build/rs.vcd");
        $dumpvars();
    end
    // initial begin
    //     $vcdplusfile("build/rob.vpd");
    //     $vcdpluson(0, top);  // Replace 'top' with your top module name
    // end
    
endmodule: top