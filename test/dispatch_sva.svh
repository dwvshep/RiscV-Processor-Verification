// SystemVerilog Assertions (SVA) for use with our FIFO module
// This file is included by the testbench to separate our main module checking code
// SVA are relatively new to 470, feel free to use them in the final project if you like

`include "verilog/sys_defs.svh"

module Dispatch_sva #(
) (
    input   logic                               clock,
    input   logic                               reset,

    // ------------ FROM INST BUFFER ------------- //
    input   logic        [`NUM_SCALAR_BITS-1:0] inst_buffer_instructions_valid,

    // ------------ FROM DECODER ------------- //
    input   DECODE_PACKET              [`N-1:0] decoder_out,
    input   logic                      [`N-1:0] is_rs1_used,
    input   logic                      [`N-1:0] is_rs2_used,
    input   ARCH_REG_IDX               [`N-1:0] source1_arch_reg,
    input   ARCH_REG_IDX               [`N-1:0] source2_arch_reg,
    input   ARCH_REG_IDX               [`N-1:0] dest_arch_reg,

    // ------------ TO/FROM BRANCH STACK ------------- //
    input  PHYS_REG_IDX [`ARCH_REG_SZ_R10K-1:0] map_table_restore,
    input   logic                               restore_valid,
    input   B_MASK                              b_mask_combinational,
    input   BS_ENTRY_PACKET [`B_MASK_WIDTH-1:0] branch_stack_entries,
    input   B_MASK                              next_b_mask,

    // ------------ TO/FROM ROB ------------- //
    input   logic            [`ROB_SZ_BITS-1:0] rob_tail,
    input   logic        [`NUM_SCALAR_BITS-1:0] rob_spots,
    input   ROB_PACKET                 [`N-1:0] rob_entries,

    // ------------ TO/FROM RS ------------- // 
    input   logic        [`NUM_SCALAR_BITS-1:0] rs_spots,
    input   RS_PACKET                  [`N-1:0] rs_entries,

    // ------------ TO/FROM FREDDY LIST ------------- //
    //input   logic        [`NUM_SCALAR_BITS-1:0] num_regs_available,
    input   logic       [`PHYS_REG_SZ_R10K-1:0] next_complete_list,
    input   PHYS_REG_IDX               [`N-1:0] regs_to_use,
    input   logic       [`PHYS_REG_SZ_R10K-1:0] free_list_copy,
    input   logic       [`PHYS_REG_SZ_R10K-1:0] updated_free_list,
    
    // ------------ FROM ISSUE? ------------- //
    //input   logic        [`NUM_SCALAR_BITS-1:0] num_issuing,

    // ------------ FROM EXECUTE ------------- //
    input   CDB_ETB_PACKET             [`N-1:0] cdb_completing,

    // ------------ TO ALL DATA STRUCTURES ------------- //
    input   logic        [`NUM_SCALAR_BITS-1:0] num_dispatched
    `ifdef DEBUG
        , input DISPATCH_DEBUG                 dispatch_debug
    `endif
);

    PHYS_REG_IDX [`ARCH_REG_SZ_R10K] prev_map_table_restore;

    logic       [`PHYS_REG_SZ_R10K-1:0] prev_updated_free_list;
    logic       [`PHYS_REG_SZ_R10K-1:0] dispatching_list;
    logic       [`PHYS_REG_SZ_R10K-1:0] prev_dispatching_list;

    PHYS_REG_IDX               [`N-1:0] prev_regs_to_use;

    /*
    int branch_count;
    always_comb begin
        for(int i = 0; i < `N; ++i) begin
            if
        end
    end
    */

    assign num_dispatched_c = restore_valid ? 0 : $min(rs_spots+num_issuing, rob_spots, instructions_valid);

    always_ff @(posedge clock) begin
        if (reset) begin
            prev_map_table_restore <= '0;
            prev_regs_to_use <= 0;
            prev_dispatching_list <= 0;
        end else begin
            prev_map_table_restore <= map_table_restore;
            prev_regs_to_use <= regs_to_use;
            prev_dispatching_list <= dispatching_list;
        end
    end

    always_comb begin
        dispatching_list = 0;
        for (int i = 0; i < num_dispatched; i++) begin
            dispatching_list[regs_to_use[i]] = 1;
        end
    end
    
    clocking cb @(posedge clock);
        property map_table_restore;
            (reset || restore_valid) |=> (dispatch_debug.map_table == prev_map_table_restore);
        endproperty

        property updated_free_list_is_correct (int i);
            (i < num_dispatched) |=> (~prev_updated_free_list[prev_regs_to_use[i]]);
        endproperty

        property updated_free_list_only_changes_dispatched;
            (~reset) |=> ((prev_free_list & ~dispatching_list) == (prev_updated_free_list_copy));
        endproperty

    endclocking

    always @(posedge clock) begin
        //Check that num_dispatched is properly calculated
        assert(reset || num_dispatched == num_dispatched_c)
            else begin
                $error("num_dispatched (%0d) not equal to min (rs_spots(%0d) + num_issuing(%0d), rob_spots(%0d), instructions_valid(%0d)).", 
                num_dispatched, rs_spots, num_issuing, rob_spots, instructions_valid);
                $finish;
            end
    end
    generate
        genvar k, j;
            for(k = 0; k < `RS_SZ; ++k) begin
                for(j = 0; j < `N; ++j) begin
                    assert property (cb.cammingSrc1(k, j))
                        else begin
                            $error("RS entry #%0d did not properly match the cdb to src 1 when it should have - Current cdb idx(%0d) - RS entry src 1(%0d).", 
                            k, CDB_tags[j], rs_data[k].Source1);
                            $finish;
                        end
                    assert property (cb.cammingSrc2(k, j))
                        else begin
                            $error("RS entry #%0d did not properly match the cdb to src 2 when it should have - Current cdb idx(%0d) - RS entry src 2(%0d).", 
                            k, CDB_tags[j], rs_data[k].Source2);
                            $finish;
                        end
                end
            end
    endgenerate
endmodule

