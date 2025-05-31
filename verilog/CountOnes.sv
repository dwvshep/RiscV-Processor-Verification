module CountOnes #(parameter int WIDTH = 32) (
    input logic [WIDTH-1:0] bit_array,
    output logic [$clog2(WIDTH+1)-1:0] count_ones
);
    generate
        if (WIDTH == 1) begin : base_case
            assign count_ones = bit_array[0];
        end else begin : recursive_case
            localparam int WIDTH_LO = WIDTH / 2;
            localparam int WIDTH_HI = WIDTH - WIDTH_LO;

            logic [$clog2(WIDTH_LO+1)-1:0] count_lo;
            logic [$clog2(WIDTH_HI+1)-1:0] count_hi;

            CountOnes #(WIDTH_LO) lo_count (
                .bit_array(bit_array[WIDTH_LO-1:0]),
                .count_ones(count_lo)
            );

            CountOnes #(WIDTH_HI) hi_count (
                .bit_array(bit_array[WIDTH-1:WIDTH_LO]),
                .count_ones(count_hi)
            );

            assign count_ones = count_lo + count_hi;
        end
        /*
        if (WIDTH == 1) begin : base_case
            assign count_ones = bit_array[0];
        end else begin : recursive_case
            logic [$clog2(WIDTH/2):0] count_lo, count_hi;

            CountOnes #(WIDTH/2) lo_count (
                .bit_array(bit_array[WIDTH/2-1:0]),
                .count_ones(count_lo)
            );

            CountOnes #(WIDTH - WIDTH/2) hi_count (
                .bit_array(bit_array[WIDTH-1:WIDTH/2]),
                .count_ones(count_hi)
            );

            assign count_ones = count_lo + count_hi;
        end
        */
    endgenerate

    
endmodule