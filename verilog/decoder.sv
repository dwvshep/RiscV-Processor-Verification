
// The decoder, copied from project 3

// This has a few changes, it now sets a "mult" flag for multiply instructions
// Pass these to the mult module with inst.r.funct3 as the MULT_FUNC

`include "verilog/sys_defs.svh"
`include "verilog/ISA.svh"

// Decode an instruction: generate useful datapath control signals by matching the RISC-V ISA
// This module is purely combinational
module decoder (
    //input  logic         valid, // when low, ignore inst. Output will look like a NOP
    input  FETCH_PACKET  inst_buffer_input,
    output DECODE_PACKET decoder_out,
    output logic         is_rs1_used,
    output logic         is_rs2_used,
    output ARCH_REG_IDX  source1_arch_reg,
    output ARCH_REG_IDX  source2_arch_reg,
    output ARCH_REG_IDX  dest_arch_reg
);
    //New outputs passed through into decode packet
    assign decoder_out.inst = inst_buffer_input.inst;
    assign decoder_out.valid = 1'b1;
    assign decoder_out.predict_taken = inst_buffer_input.predict_taken;
    assign decoder_out.PC = inst_buffer_input.PC;
    assign decoder_out.NPC = inst_buffer_input.PC + 4;
    // assign decoder_out.mult_func = inst_buffer_input.inst.r.funct3;
    // assign decoder_out.load_func = inst_buffer_input.inst.r.funct3;
    // assign decoder_out.store_func = inst_buffer_input.inst.r.funct3;
    // assign decoder_out.branch_func = inst_buffer_input.inst.b.funct3;
    
    assign decoder_out.bp_packet = inst_buffer_input.bp_packet;
    assign decoder_out.predicted_PC = inst_buffer_input.predicted_PC;
    assign decoder_out.is_jump = inst_buffer_input.is_jump;
    // Note: I recommend using an IDE's code folding feature on this block
    always_comb begin
        // Default control values (looks like a NOP)
        // See sys_defs.svh for the constants used here
        decoder_out.opa_select    = OPA_IS_RS1;
        decoder_out.opb_select    = OPB_IS_RS2;
        decoder_out.alu_func      = ALU_ADD;
        decoder_out.has_dest      = `FALSE;
        decoder_out.csr_op        = `FALSE;
        decoder_out.mult          = `FALSE;
        decoder_out.rd_mem        = `FALSE;
        decoder_out.wr_mem        = `FALSE;
        decoder_out.cond_branch   = `FALSE;
        decoder_out.uncond_branch = `FALSE;
        decoder_out.halt          = `FALSE;
        decoder_out.illegal       = `FALSE;

        if (1'b1) begin //replaced valid check with 1'b1 since we can decode anything we want, we already know we only dispatch valid ones
            casez (inst_buffer_input.inst)
                `RV32_LUI: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.opa_select = OPA_IS_ZERO;
                    decoder_out.opb_select = OPB_IS_U_IMM;
                end
                `RV32_AUIPC: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.opa_select = OPA_IS_PC;
                    decoder_out.opb_select = OPB_IS_U_IMM;
                end
                `RV32_JAL: begin
                    decoder_out.has_dest      = `TRUE;
                    decoder_out.opa_select    = OPA_IS_PC;
                    decoder_out.opb_select    = OPB_IS_J_IMM;
                    decoder_out.uncond_branch = `TRUE;
                end
                `RV32_JALR: begin
                    decoder_out.has_dest      = `TRUE;
                    decoder_out.opa_select    = OPA_IS_RS1;
                    decoder_out.opb_select    = OPB_IS_I_IMM;
                    decoder_out.uncond_branch = `TRUE;
                end
                `RV32_BEQ, `RV32_BNE, `RV32_BLT, `RV32_BGE,
                `RV32_BLTU, `RV32_BGEU: begin
                    decoder_out.opa_select  = OPA_IS_PC;
                    decoder_out.opb_select  = OPB_IS_B_IMM;
                    decoder_out.cond_branch = `TRUE;
                    // stage_ex uses inst.b.funct3 as the branch function
                end
                `RV32_MUL, `RV32_MULH, `RV32_MULHSU, `RV32_MULHU: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.mult       = `TRUE;
                    // stage_ex uses inst.r.funct3 as the mult function
                end
                `RV32_LB, `RV32_LH, `RV32_LW,
                `RV32_LBU, `RV32_LHU: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.opb_select = OPB_IS_I_IMM;
                    decoder_out.rd_mem     = `TRUE;
                    // stage_ex uses inst.r.funct3 as the load size and signedness
                end
                `RV32_SB, `RV32_SH, `RV32_SW: begin
                    decoder_out.opb_select = OPB_IS_S_IMM;
                    decoder_out.wr_mem     = `TRUE;
                    // stage_ex uses inst.r.funct3 as the store size
                end
                `RV32_ADDI: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.opb_select = OPB_IS_I_IMM;
                end
                `RV32_SLTI: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.opb_select = OPB_IS_I_IMM;
                    decoder_out.alu_func   = ALU_SLT;
                end
                `RV32_SLTIU: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.opb_select = OPB_IS_I_IMM;
                    decoder_out.alu_func   = ALU_SLTU;
                end
                `RV32_ANDI: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.opb_select = OPB_IS_I_IMM;
                    decoder_out.alu_func   = ALU_AND;
                end
                `RV32_ORI: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.opb_select = OPB_IS_I_IMM;
                    decoder_out.alu_func   = ALU_OR;
                end
                `RV32_XORI: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.opb_select = OPB_IS_I_IMM;
                    decoder_out.alu_func   = ALU_XOR;
                end
                `RV32_SLLI: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.opb_select = OPB_IS_I_IMM;
                    decoder_out.alu_func   = ALU_SLL;
                end
                `RV32_SRLI: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.opb_select = OPB_IS_I_IMM;
                    decoder_out.alu_func   = ALU_SRL;
                end
                `RV32_SRAI: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.opb_select = OPB_IS_I_IMM;
                    decoder_out.alu_func   = ALU_SRA;
                end
                `RV32_ADD: begin
                    decoder_out.has_dest   = `TRUE;
                end
                `RV32_SUB: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.alu_func   = ALU_SUB;
                end
                `RV32_SLT: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.alu_func   = ALU_SLT;
                end
                `RV32_SLTU: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.alu_func   = ALU_SLTU;
                end
                `RV32_AND: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.alu_func   = ALU_AND;
                end
                `RV32_OR: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.alu_func   = ALU_OR;
                end
                `RV32_XOR: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.alu_func   = ALU_XOR;
                end
                `RV32_SLL: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.alu_func   = ALU_SLL;
                end
                `RV32_SRL: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.alu_func   = ALU_SRL;
                end
                `RV32_SRA: begin
                    decoder_out.has_dest   = `TRUE;
                    decoder_out.alu_func   = ALU_SRA;
                end
                `RV32_CSRRW, `RV32_CSRRS, `RV32_CSRRC: begin
                    decoder_out.csr_op = `TRUE;
                end
                `WFI: begin
                    decoder_out.halt = `TRUE;
                end
                default: begin
                    decoder_out.illegal = `TRUE;
                end
        endcase // casez (inst)
        end // if (valid)
        decoder_out.has_dest = inst_buffer_input.inst.r.rd ? decoder_out.has_dest : 0;
    end // always

    assign is_rs1_used = decoder_out.cond_branch || (decoder_out.opa_select == OPA_IS_RS1);
    assign is_rs2_used = decoder_out.cond_branch || decoder_out.wr_mem || (decoder_out.opb_select == OPB_IS_RS2);
    assign source1_arch_reg = inst_buffer_input.inst.r.rs1;
    assign source2_arch_reg = inst_buffer_input.inst.r.rs2;
    assign dest_arch_reg = inst_buffer_input.inst.r.rd;

    assign decoder_out.FU_type = (decoder_out.cond_branch || decoder_out.uncond_branch) ? BU :
                                                                   (decoder_out.rd_mem) ? LOAD :
                                                                   (decoder_out.wr_mem) ? STORE :
                                                                     (decoder_out.mult) ? MULT :
                                                                                          ALU;
endmodule // decoder
