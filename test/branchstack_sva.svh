`include "verilog/sys_defs.svh"

module BranchStack_sva #(
) (
    input   logic                                      clock, 
    input   logic                                      reset,
    // ------------- TO ALL -------------- //
    input   logic                                      restore_valid,

    // ------------- TO FETCH -------------- //
    input   ADDR                                       PC_restore,

    // ------------- FROM COMPLETE -------------- //
    input   BRANCH_REG_PACKET                          branch_completing,

    // ------------- TO ROB ------------------- //
    input   logic                   [`ROB_SZ_BITS-1:0] rob_tail_restore,

    // ------------- TO FREDDY LIST ----------- //
    input   logic              [`PHYS_REG_SZ_R10K-1:0] free_list_in,
    input   logic              [`PHYS_REG_SZ_R10K-1:0] free_list_restore,

    // ------------- TO/FROM DISPATCH -------------- //
    input   BS_ENTRY_PACKET        [`B_MASK_WIDTH-1:0] branch_stack_entries,
    input   B_MASK                                     next_b_mask,
    input  PHYS_REG_IDX        [`ARCH_REG_SZ_R10K-1:0] map_table_restore,     
    input  B_MASK                                      b_mask_combinational,

    // ------------- TO RS/EXECUTE -------------- //
    input  B_MASK                                      b_mm_out,

    // ------------- TO BRANCH PREDICTOR -------------- //
    input BRANCH_PREDICTOR_PACKET                      bs_bp_packet,
    input logic                                        resolving_valid_branch,

    // ------------- TO BTB -------------- //
    input   logic                                      resolving_valid,
    input   ADDR                                       resolving_target_PC,
    input   ADDR                                       resolving_branch_PC

    // ------------- TO LSQ ------------------ //
    // output logic                                 lsq_tail_restore  //<--- STILL NEED TO UPDATE THIS
    // branch prediction repair?
`ifdef DEBUG
    , input BS_DEBUG                                   bs_debug

); 

    B_MASK  b_mm_resolve;
    B_MASK  b_mm_mispred;
    assign b_mm_mispred = branch_completing.bm_mispred;
    assign b_mm_resolve = branch_completing.bmm;

    logic [`B_MASK_WIDTH-1:0] prev_b_mm_resolve;

    BS_ENTRY_PACKET [`B_MASK_WIDTH-1:0] prev_branch_stack_entries;
    BS_ENTRY_PACKET [`B_MASK_WIDTH-1:0] prev_next_branch_stack;

    task exit_on_error;
        begin
            $display("\n\033[31m@@@ Failed at time %4d\033[0m\n", $time);
            $finish;
        end
    endtask

    always_ff @(posedge clock) begin
        prev_b_mm_resolve <= b_mm_resolve;
        prev_branch_stack_entries <= branch_stack_entries;
        prev_next_branch_stack <= bs_debug.next_branch_stack;
    end

    clocking prop_no_dispatch @(posedge clock);
        // property that checks if b_mm_resolve bit is set low (resolved) at the b_mask_combinational 
        property resolved_must_be_zero;
            ((branch_stack_entries == 0) & ~reset) |=> ((prev_b_mm_resolve & b_mask_combinational) == 0); // need to consider previous or not previous
        endproperty

        // property that checks if b_mm_resolve squashes dependent branch entries in the branch stack
        property squashed_must_be_empty(int index);
            ((branch_stack_entries[index] == 0) & b_mm_mispred & ((b_mm_resolve & bs_debug.branch_stack[index].b_m) != 0)) 
                            |=> (bs_debug.branch_stack[index] == 0);
        endproperty

    endclocking

    clocking prop_with_dispatch @(posedge clock);
        property branch_stacks_do_not_overlap;
            (branch_stack_entries[0] === 0 || branch_stack_entries[0] === 1) |=> ((prev_next_branch_stack & prev_branch_stack_entries) == 0);
        endproperty

        property dispatched_branch_update_branchstack(int index);
            (branch_stack_entries[index] != 0) |=> (prev_branch_stack_entries[index] == bs_debug.branch_stack[index]);
        endproperty

        property dispatched_branch_updates_mask(int index);
            (branch_stack_entries[index] != 0) |=> (bs_debug.b_mask_reg[index]);
        endproperty
    endclocking


genvar i;
generate
    for (i = 0; i < `B_MASK_WIDTH; ++i) begin
        always_ff @(posedge clock) begin
            
            assert property (prop_no_dispatch.squashed_must_be_empty(i))
                else begin
                    $error("Squashing without dispatch didn't work at index %d: b_mm was %b, bm was %b", 
                        i, prev_b_mm_resolve, bs_debug.branch_stack[i]);
                    $finish;
                end
            assert property (prop_with_dispatch.dispatched_branch_update_branchstack(i))
                else begin
                    $error("Branch Stack was not updated by branch_stack_entries at index %d, expected: %0b, got %0b", 
                        i, prev_branch_stack_entries[i], bs_debug.branch_stack[i]);
                    $finish;
                end

            assert property (prop_with_dispatch.dispatched_branch_updates_mask(i))
                else begin
                    $error("Branch Stack's mask was not updated at index %d", 
                        i);
                    $finish;
                end
        end
    end


endgenerate



    always @(posedge clock) begin

    // Check that resolved branch bit stays low without dispatch
        assert property (prop_no_dispatch.resolved_must_be_zero)
            else begin
                $error("Mismatch on prev_b_mm_resolve and b_mask_combinational (no dispatch)");
                $finish;
            end
        
        assert property (prop_with_dispatch.branch_stacks_do_not_overlap)
            else begin
                $error("Branch Stack and Entries Overlapped: prev_next_branch_stack %0b, prev_branch_stack_entries %0b",
                prev_next_branch_stack, prev_branch_stack_entries);
                $finish;
            end

     end


endmodule
