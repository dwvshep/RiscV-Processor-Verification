`include "verilog/sys_defs.svh"

module encoder #( // Parametize this module
    parameter INPUT_LENGTH = `PHYS_REG_SZ_R10K,
    parameter OUTPUT_LENGTH = `PHYS_REG_ID_BITS
)(
    input  wire [INPUT_LENGTH-1:0] in,                    // N-bit input
    output reg  [OUTPUT_LENGTH-1:0] out                   // Encoded output
);

    integer i;
    
    always @(*) begin
        out   = '0;
        for (i = 0; i < INPUT_LENGTH; ++i) begin
            if (in[i]) begin
                out   = i[OUTPUT_LENGTH-1:0];  // Assign the index as output
            end
        end
    end
endmodule