// SystemVerilog Assertions (SVA) for use with our FIFO module
// This file is included by the testbench to separate our main module checking code
// SVA are relatively new to 470, feel free to use them in the final project if you like

`include "verilog/sys_defs.svh"

module FreddyList_sva #(
) (
    input   clock,
    input   reset,
    // ------------- FROM CDB -------------- //
    input  PHYS_REG_IDX           [`N-1:0] phys_reg_completing,    // phys reg indexes that are being completed (T_new)
    input  logic                  [`N-1:0] completing_valid,       // bit vector of N showing which phys_reg_completing is valid
    // ------------- FROM RETIRE -------------- //
    input  PHYS_REG_IDX           [`N-1:0] phys_regs_retiring,      // phy reg indexes that are being retired (T_old)
    input  logic    [`NUM_SCALAR_BITS-1:0] num_retiring_valid,     // number of retiring phys reg (T_old)
    // ------------- FROM BRANCH STACK -------------- //
    input  logic   [`PHYS_REG_SZ_R10K-1:0] free_list_restore,      // snapshot of freelist at mispredicted branch
    input  logic                           restore_flag,           // branch mispredict flag
    // ------------- FROM DISPATCH -------------- //
    input  logic   [`PHYS_REG_SZ_R10K-1:0] updated_free_list,      // freelist from dispatch
    // input  logic    [`NUM_SCALAR_BITS-1:0] num_dispatched,
    // ------------- TO DISPATCH -------------- //
    input  PHYS_REG_IDX           [`N-1:0] regs_to_use,       // physical register indices for dispatch to use
    // output logic    [`NUM_SCALAR_BITS-1:0] free_list_spots,        // how many physical registers are free
    input  logic   [`PHYS_REG_SZ_R10K-1:0] free_list,              // bitvector of the phys reg that are complete
    // ------------- TO ISSUE -------------- //
    input  logic   [`PHYS_REG_SZ_R10K-1:0] next_complete_list,           // bitvector of the phys reg that are complete
    input  logic   [`PHYS_REG_SZ_R10K-1:0] complete_list           // bitvector of the phys reg that are complete
);

    logic only_updated;
    logic   [`PHYS_REG_SZ_R10K-1:0] prev_complete_list;
    logic   [`PHYS_REG_SZ_R10K-1:0] prev_updated_free_list;

    logic   [`PHYS_REG_SZ_R10K-1:0] retiring_list;
    logic   [`PHYS_REG_SZ_R10K-1:0] prev_retiring_list;
    logic   [`PHYS_REG_SZ_R10K-1:0] prev_phys_regs_retiring;

    logic   [`PHYS_REG_SZ_R10K-1:0] FL_restore_to_check;
    logic   [`PHYS_REG_SZ_R10K-1:0] prev_FL_restore_to_check;

    logic   [`PHYS_REG_SZ_R10K-1:0] completing_list;
    logic   [`PHYS_REG_SZ_R10K-1:0] prev_completing_list;
    logic completing;

    assign completing = |completing_valid;

    assign only_updated = ~restore_flag & (num_retiring_valid == 0);

    always_comb begin 
        retiring_list = 0;
        for (int i = 0; i < num_retiring_valid; i++) begin
            retiring_list[phys_regs_retiring[i]] = 1;
        end
    end

    always_comb begin 
        FL_restore_to_check = free_list_restore;
        for (int i = 0; i < num_retiring_valid; i++) begin
            FL_restore_to_check[phys_regs_retiring[i]] = 0;
        end
    end

    always_comb begin 
        completing_list = 0;
        for (int i = 0; i < `N; i++) begin
                completing_list[phys_reg_completing[i]] = completing_valid[i];
        end
    end


    task exit_on_error;
        begin
            $display("\n\033[31m@@@ Failed at time %4d\033[0m\n", $time);
            $finish;
        end
    endtask

    always_ff @(posedge clock) begin
        prev_updated_free_list <= updated_free_list;
        prev_retiring_list <= retiring_list;
        prev_FL_restore_to_check <= FL_restore_to_check;
        prev_completing_list <= completing_list;
        prev_complete_list <= complete_list;
        prev_phys_regs_retiring <= phys_regs_retiring;
    end

    clocking FL_prop @(posedge clock);
        property no_zero_reg_retiring(int index);
            (index < num_retiring_valid) |=> (prev_phys_regs_retiring[index] != 0);
        endproperty
    
        property only_updating;
            (only_updated) |=> (prev_updated_free_list == free_list);
        endproperty

        property not_only_updating;
            (~only_updated) |=> ((prev_retiring_list & free_list) == prev_retiring_list);
        endproperty

        property not_only_updating_others;
            (~only_updated & ~restore_flag) |=> ((~prev_retiring_list & free_list) == (~prev_retiring_list & prev_updated_free_list));
        endproperty

        property FL_restore;
            (restore_flag) |=> ((prev_FL_restore_to_check & free_list) == prev_FL_restore_to_check);
        endproperty
        
    endclocking

    // TODO: update
    clocking complete_prop @(posedge clock);
        property something_completing;
            (completing) |=> ((prev_completing_list & complete_list) == prev_completing_list);
        endproperty

        property prev_complete_maintained;
            // TODO: might not want to check all the time. Choose a better condition to check
            (~reset) |=> ((~prev_complete_list & ~complete_list & ~prev_completing_list) == (~prev_complete_list & ~prev_completing_list));
        endproperty
    endclocking
    
genvar i;
generate
    for (i = 0; i < `N; ++i) begin
        always @(posedge clock) begin
            assert property (FL_prop.no_zero_reg_retiring(i))
                else begin
                    $error("Zero reg retired");
                    $finish;
                end
        end
    end
endgenerate

    
    always @(posedge clock) begin

    // Check for only_updated, free_list = updated_free_list
        assert property (FL_prop.only_updating)
            else begin
                $error("Mismatch on free_list and updated_list: expected %b, got %b", 
                    updated_free_list,     free_list);
                $finish;
            end

    // Check for num_retiring_valid and updated_free_list => free_list
        assert property (FL_prop.not_only_updating)
            else begin
                $error("Free_list didn't free a retiring register: expected %b, got %b",
                    prev_retiring_list,   prev_retiring_list & free_list);
                $finish;
            end

        assert property (FL_prop.not_only_updating_others)
            else begin
                $error("Missmatch on free_list and updated_list when retiring : expected %b, got %b",
                    (~prev_retiring_list & prev_updated_free_list),  (~prev_retiring_list & free_list));
                $finish;
            end

        // Check restore
        assert property (FL_prop.FL_restore)
            else begin
                $error("Free_list didn't restore correctly");
                $finish;
            end

        // Check completing phys reg

        assert property (complete_prop.something_completing)
            else begin
                $error("Complete_list didn't complete a completing register: expected %b, got %b",
                    prev_completing_list,   prev_completing_list & complete_list);
                $finish;
            end

        // Check non-completing phys reg after updating completing phys reg
        assert property (complete_prop.prev_complete_maintained)
            else begin
                    $error("Complete_list didn't properly maintain previous state");
                    $finish;
                end

        
    end

endmodule

