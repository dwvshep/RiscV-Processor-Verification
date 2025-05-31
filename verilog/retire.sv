`include "verilog/sys_defs.svh"

module retire (
    input logic                         clock,
    input logic                         reset,
    // ------------- TO/FROM ROB -------------- //
    input  ROB_PACKET           [`N-1:0] rob_outputs,                   // Coming from rob, to retrieve T_old from the packet, so that it can be retired
    input  logic  [`NUM_SCALAR_BITS-1:0] rob_outputs_valid,             // Coming from rob, to check which output is valid, only valid rob outputs can be retired
    output logic  [`NUM_SCALAR_BITS-1:0] num_retiring,                  // Send to rob, how many rob_outputs can be retired

    // ------------- TO SQ -------------- //
    output logic  [`NUM_SCALAR_BITS-1:0] num_store_retiring,                  // Send to rob, how many rob_outputs can be retired

    // ------------- TO/FROM FREDDYLIST -------------- //
    input        [`PHYS_REG_SZ_R10K-1:0] complete_list_exposed,         // Coming from freddylist, to find out which rob_output is actually completed and ready to retire
    output PHYS_REG_IDX         [`N-1:0] phys_regs_retiring,             // Send to freddylist, which physical registers are being retired

    // ------------- TO CPU -------------- //
    output COMMIT_PACKET        [`N-1:0] committed_insts,

    /*---------------- FROM/TO REGFILE ---------------------------*/
    output PHYS_REG_IDX [`N-1:0] retire_phys_regs_reading,
    input DATA          [`N-1:0] retire_read_data
);


//start at head and identify up to n instructions that are complete
    //send Told back to free list
/*
always_comb begin
    num_retiring = 0;
    // phys_regs_retiring = 0;
    for (int i = 0; i < rob_outputs_valid; i++) begin
        if (complete_list_exposed[rob_outputs[i].T_new]) begin
            phys_regs_retiring[i] = rob_outputs[i].has_dest ? rob_outputs[i].T_old : rob_outputs[i].T_new;
        end else begin
            break;
        end
        num_retiring = num_retiring + 1'b1;
    end
end*/
logic halt, next_halt;

/*
     ADDR    NPC; done
    DATA    data;
    REG_IDX reg_idx; done
    logic   halt; done
    logic   illegal; done
    logic   valid;
*/

always_comb begin
    num_retiring = '0;
    num_store_retiring = '0;
    phys_regs_retiring = '0;
    next_halt = halt;
    committed_insts = '0;
    retire_phys_regs_reading = '0;
    for (int i = 0; i < `N; i++) begin
        if (!next_halt && i < rob_outputs_valid && complete_list_exposed[rob_outputs[i].T_new]) begin
            committed_insts[i].data = retire_read_data[i];
            retire_phys_regs_reading[i] = rob_outputs[i].T_new;
            committed_insts[i].reg_idx = rob_outputs[i].arch_reg;
            committed_insts[i].halt = rob_outputs[i].halt;
            committed_insts[i].illegal = rob_outputs[i].illegal;
            committed_insts[i].NPC = rob_outputs[i].NPC;
            committed_insts[i].valid = 1'b1;
            phys_regs_retiring[num_retiring] = rob_outputs[i].T_old;
            num_retiring = num_retiring + 1;
            next_halt = rob_outputs[i].halt;
            if (rob_outputs[i].is_store) begin
                num_store_retiring += 1;
            end
        end else begin
            break;
        end
    end
end

always_ff @(posedge clock) begin
    if (reset) begin
        halt <= '0;
    end else begin
        halt <= next_halt;
        // for (int i = 0; i < `N; ++i) begin
        //     $display("complete_list_exposed[rob_outputs[%d].T_new]: %d",
        //         i, complete_list_exposed[rob_outputs[i].T_new]
        //     );
        // end

        // for (int i = 0; i < `N; ++i) begin
        //     // if (i < num_retiring) begin
        //         $display("rob_outputs[%d].T_old: %d, rob_outputs[%d].T_new: %d, rob_outputs[%d].NPC: %h, rob_outputs[%d].Arch_reg: %d",
        //             i, rob_outputs[i].T_old, i, rob_outputs[i].T_new, i, rob_outputs[i].NPC, i, rob_outputs[i].arch_reg
        //         );
        //     // end
        // end

        // $display("num_retiring: %d\nrob_outputs_valid: %d", 
        // num_retiring,
        // rob_outputs_valid);

        // $display("halt: %b", 
        // halt);
        
    end
end

endmodule