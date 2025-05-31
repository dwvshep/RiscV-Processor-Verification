`include "verilog/sys_defs.svh"

module freddylist #(
) (
    input   clock,
    input   reset,
    // ------------- FROM EXECUTE -------------- //
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
    output PHYS_REG_IDX           [`N-1:0] regs_to_use,       // physical register indices for dispatch to use
    // output logic    [`NUM_SCALAR_BITS-1:0] free_list_spots,        // how many physical registers are free
    output logic   [`PHYS_REG_SZ_R10K-1:0] free_list,              // bitvector of the phys reg that are complete
    // ------------- TO ISSUE -------------- //
    output logic   [`PHYS_REG_SZ_R10K-1:0] next_complete_list,           // bitvector of the phys reg that are complete
    output logic   [`PHYS_REG_SZ_R10K-1:0] complete_list,
    // ------------- FROM STORE ADDR -------------- //
    input  PHYS_REG_IDX                    store_reg_completing,
    input  logic                           store_valid
    
);

    logic [`PHYS_REG_SZ_R10K-1:0] next_free_list;

    // psel shit
    logic [`N-1:0] [`PHYS_REG_SZ_R10K-1:0] psel_output;
    logic [`PHYS_REG_SZ_R10K-1:0] gnt;
    logic empty;

    logic [`PHYS_REG_SZ_R10K-1:0] dispatched_reg;
    // logic [`PHYS_REG_NUM_ENTRIES_BITS-1:0] entries, next_entries;       // entries for free list

    assign dispatched_reg = free_list ^ updated_free_list;               // to find out which phys reg are being dispatched
    // assign next_entries = entries - num_dispatched + num_retiring_valid;
    // assign free_list_spots = (`PHYS_REG_SZ_R10K - entries) < `N ? (`PHYS_REG_SZ_R10K - entries) : `N;


    psel_gen #(
         .WIDTH(`PHYS_REG_SZ_R10K),  // The width of the request bus
         .REQS(`N)            // The number of requests that can be simultaenously granted
    ) psel_inst (
         .req(free_list),          // Input request bus
         .gnt(gnt),          // Output with all granted requests on a bus
         .gnt_bus(psel_output),  // Output bus for each request
         .empty(empty)       // Output asserted when there are no requests
    );

    genvar i;
    generate
        for(i = 0; i < `N; ++i) begin: encoderblock
            encoder #(
                .INPUT_LENGTH(`PHYS_REG_SZ_R10K),
                .OUTPUT_LENGTH(`PHYS_REG_ID_BITS)
            ) u_encoder (
                .in(psel_output[i]), 
                .out(regs_to_use[i])
            );
        end
    endgenerate

    always_comb begin // TODO: consider genvar
        next_complete_list = complete_list;
        for (int i = 0; i < `N; ++i) begin
            if (completing_valid[i]) begin
                next_complete_list[phys_reg_completing[i]] = 1'b1;
            end
            next_complete_list = ~(dispatched_reg) & next_complete_list;
        end

        if (store_valid) begin
            next_complete_list[store_reg_completing] = 1'b1;
        end
    end

    always_comb begin
        next_free_list = updated_free_list;
        for (int i = 0; i < `N; ++i) begin
            if (i < num_retiring_valid) begin
                next_free_list[phys_regs_retiring[i]] = 1'b1;
            end
        end
    end

    
    always_ff @(posedge clock) begin
        if (reset) begin
            complete_list[`PHYS_REG_SZ_R10K-1:`ARCH_REG_SZ_R10K] <= 0;
            complete_list[`ARCH_REG_SZ_R10K-1:0] <= ~0;                 // Assumption: at reset, all mappings are restored to original, ex. reg1 -> pr1
            free_list[`PHYS_REG_SZ_R10K-1:`ARCH_REG_SZ_R10K] <= ~0;
            free_list[`ARCH_REG_SZ_R10K-1:0] <= 0;
            // entries <= `0;
        end else begin
            
            // $display("free_list:     %b", free_list);
            // $display("complete_list: %b", complete_list);
            // for (int i = 0; i < `PHYS_REG_SZ_R10K; ++i) begin
            //     $display("free_list[%d]: %d", i, free_list[i]);
            //     // $display("free_list_restore[%d]: %d", i, free_list_restore[i]);
            //     // $display("next_free_list[%d]: %d", i, next_free_list[i]);
            // end
            complete_list <= next_complete_list;
            free_list <= restore_flag ? next_free_list | free_list_restore : next_free_list;
            // entries <= next_entries;
        end
    end

endmodule