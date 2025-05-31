// SystemVerilog Assertions (SVA) for use with our FIFO module
// This file is included by the testbench to separate our main module checking code
// SVA are relatively new to 470, feel free to use them in the final project if you like

`include "verilog/sys_defs.svh"

module Issue_sva #(
) (
    input logic                                clock,
    input logic                                reset,

    // ------------- FROM FREDDY -------------- //
    input logic        [`PHYS_REG_SZ_R10K-1:0] complete_list,       // The entire complete list of each register

    // ------------- TO/FROM RS -------------- //
    input RS_PACKET               [`RS_SZ-1:0] rs_data,             // full RS data exposed to issue for psel and FU packets generating
    input logic                   [`RS_SZ-1:0] rs_valid_next,
    input  wor                   [`RS_SZ-1:0] rs_data_issuing,     // set index to 1 when a rs_data is selected to be issued

    // ------------- TO/FROM REGFILE -------------- //
    
    input DATA             [`NUM_FU_ALU-1:0] issue_alu_read_data_1,
    input DATA             [`NUM_FU_ALU-1:0] issue_alu_read_data_2,
    input DATA            [`NUM_FU_MULT-1:0] issue_mult_read_data_1,
    input DATA            [`NUM_FU_MULT-1:0] issue_mult_read_data_2,
    input DATA          [`NUM_FU_BRANCH-1:0] issue_branch_read_data_1,
    input DATA          [`NUM_FU_BRANCH-1:0] issue_branch_read_data_2,

    input PHYS_REG_IDX    [`NUM_FU_ALU-1:0] issue_alu_regs_reading_1,
    input PHYS_REG_IDX    [`NUM_FU_ALU-1:0] issue_alu_regs_reading_2,
    input PHYS_REG_IDX   [`NUM_FU_MULT-1:0] issue_mult_regs_reading_1,
    input PHYS_REG_IDX   [`NUM_FU_MULT-1:0] issue_mult_regs_reading_2,
    input PHYS_REG_IDX [`NUM_FU_BRANCH-1:0] issue_branch_regs_reading_1,
    input PHYS_REG_IDX [`NUM_FU_BRANCH-1:0] issue_branch_regs_reading_2,
    
    // ------------- FROM CDB -------------- //
    input CDB_REG_PACKET              [`N-1:0] cdb_reg,

    // ------------- TO/FROM EXECUTE -------------- //
    // TODO: include the backpressure signals from each FU. 
    input                         [`NUM_FU_MULT-1:0] mult_free, // backpressure signal from the mult FU
    input                         [`NUM_FU_LDST-1:0] ldst_free, // backpressure signal from the ldst FU

    input                         [`NUM_FU_MULT-1:0] mult_cdb_req, // High if there is a valid instruction in the second to last stage of mult
    input                         [`NUM_FU_LDST-1:0] ldst_cdb_req, // High if there is a valid instruction in the second to last stage of ldst

    input logic                  [`NUM_FU_MULT-1:0] mult_cdb_gnt,
    input logic                  [`NUM_FU_LDST-1:0] ldst_cdb_gnt,
    input ALU_PACKET              [`NUM_FU_ALU-1:0] alu_packets,
    input MULT_PACKET            [`NUM_FU_MULT-1:0] mult_packets,
    input BRANCH_PACKET        [`NUM_FU_BRANCH-1:0] branch_packets,
    input LDST_PACKET            [`NUM_FU_LDST-1:0] ldst_packets,

    input logic [`N-1:0]        [`NUM_FU_TOTAL-1:0] complete_gnt_bus          // bitvector of the phys reg that are complete
);


    //temporary variables that we want to store
    

    //values we need to calculate
    

    /*
        Conditions that need to be met
        1. All instructions in the output packets should have their source registers cleared <-- DONE
        2. number of instructions issued for a FU type should be less than or equal to the number of FU free

    */


    logic mult_granted;

    assign mult_granted =| mult_cdb_gnt;

    RS_PACKET [`RS_SZ-1:0] prev_rs_data;
    



    task exit_on_error;
        begin
            $display("\n\033[31m@@@ Failed at time %4d\033[0m\n", $time);
            $finish;
        end
    endtask


    always_ff @(posedge clock) begin
       prev_rs_data = rs_data;
    end

    clocking issue_props @(posedge clock);

        //1. All instructions in the output packets should have their source registers cleared
        property valid_alu_packet (int i, int j);
            (alu_packets[j].valid && alu_packets[j].inst == prev_rs_data[i].decoded_signals.inst) 
            |=> (prev_rs_data[i].Source1_ready && prev_rs_data[i].Source2_ready);
        endproperty

        property valid_branch_packet(int i, int j);
            (branch_packets[j].valid && branch_packets[j].inst == prev_rs_data[i].decoded_signals.inst) 
            |=> (prev_rs_data[i].Source1_ready && prev_rs_data[i].Source2_ready);
        endproperty

        property valid_mult_packet(int i, int j);
            (mult_packets[j].valid && mult_packets[j].dest_reg_idx == prev_rs_data[i].T_new) 
            |=> (prev_rs_data[i].Source1_ready && prev_rs_data[i].Source2_ready);
        endproperty

        /*property mult_structural;
            for(int i = 0; i < `NUM_FU_MULT; ++i) begin
                
            end
        endproperty*/

    endclocking
    


generate
genvar i;
genvar j;
for (i = 0; i < `RS_SZ; ++i) begin
    for (j = 0; j < `NUM_FU_ALU; ++j) begin
        always_ff @(posedge clock) begin
            assert property (issue_props.valid_alu_packet(i, j))
                else begin
                    $error("Tags for instructions in ALU Packet have not been cleared");
                    $finish;
                end
        end
    end

    for(j = 0; j < `NUM_FU_BRANCH; ++j) begin
        always_ff @(posedge clock) begin
            assert property (issue_props.valid_branch_packet(i, j))
                else begin
                    $error("Tags for instructions in Branch Packet have not been cleared");
                    $finish;
                end
        end
    end

    for(j = 0; j < `NUM_FU_MULT; ++j) begin
        always_ff @(posedge clock) begin
            assert property (issue_props.valid_mult_packet(i, j))
                else begin
                    $error("Tags for instructions in Mult Packet have not been cleared");
                    $finish;
                end
        end
    end
end
endgenerate

endmodule

