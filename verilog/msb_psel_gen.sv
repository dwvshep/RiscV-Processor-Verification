module msb_psel_gen #(parameter WIDTH, REQS) (
    input wire [WIDTH-1:0]       req,
    output wor [WIDTH-1:0]       gnt,
    output wand [WIDTH*REQS-1:0] gnt_bus,
    output wire                  empty
);

    // Internal stuff
    wire  [WIDTH*REQS-1:0]  tmp_reqs;
    wire  [WIDTH*REQS-1:0]  tmp_gnts;

    // Calculate trivial empty case
    assign empty = ~(|req);

    genvar j, k;
    for (j=0; j<REQS; ++j)
    begin:foo
        // Zero'th request/grant trivial, just normal priority selector
        if (j == 0) begin
            assign tmp_reqs[WIDTH-1:0]  = req[WIDTH-1:0];
            assign gnt_bus[WIDTH-1:0]   = tmp_gnts[WIDTH-1:0];


        // Request/grants 2-N.  Request vector for j'th request will be same as
        //  j-2 with grant from j-2 masked out.  Will alternate between normal and
        //  reversed priority order.  For the odd lines, need to use reversed grant
        //  output so that it's consistent with order of input.
        end else begin    // mask out gnt from req[j-2]
            assign tmp_reqs[(j+1)*WIDTH-1 -: WIDTH] = tmp_reqs[(j)*WIDTH-1 -: WIDTH] &
                                                        ~tmp_gnts[(j)*WIDTH-1 -: WIDTH];


            assign gnt_bus[(j+1)*WIDTH-1 -: WIDTH] = tmp_gnts[(j+1)*WIDTH-1 -: WIDTH];

        end

        // instantiate priority selectors
        msb_wand_sel #(WIDTH) psel (.req(tmp_reqs[(j+1)*WIDTH-1 -: WIDTH]), .gnt(tmp_gnts[(j+1)*WIDTH-1 -: WIDTH]));


    end

    // assign final gnt outputs
    // gnt_bus is the full-width vector for each request line, so OR everything
    for(k=0; k<WIDTH; ++k)
    begin:final_gnt
        if(k < REQS) begin
            assign gnt = gnt_bus[(k+1)*WIDTH-1 -: WIDTH];
        end else begin
            assign gnt = 0;
        end
    end

endmodule // msb_psel_gen

module msb_wand_sel (req, gnt);
    //synopsys template
    parameter WIDTH=64;
    input wire  [WIDTH-1:0] req;
    output wand [WIDTH-1:0] gnt;

    wire  [WIDTH-1:0] req_r;
    wand  [WIDTH-1:0] gnt_r;

    //priority selector
    genvar i;
    // reverse inputs and outputs
    for (i = 0; i < WIDTH; i = i + 1)
    begin : reverse
        assign req_r[WIDTH-1-i] = req[i];
        assign gnt[WIDTH-1-i]   = gnt_r[i];
    end

    for (i = 0; i < WIDTH-1 ; i = i + 1)
    begin : foo
        assign gnt_r [WIDTH-1:i] = {{(WIDTH-1-i){~req_r[i]}},req_r[i]};
    end
    assign gnt_r[WIDTH-1] = req_r[WIDTH-1];

endmodule // msb_wand_sel