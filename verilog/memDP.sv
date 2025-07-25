///////////////////////////////////////////////////////////
// 
// Module:  memDP
// Purpose: Generic dual-ported memory
//          Optionally add multiple read ports
// 
///////////////////////////////////////////////////////////

module memDP
  #(parameter WIDTH      = 32,
    parameter DEPTH      = 32,
    parameter READ_PORTS = 1,
    parameter BYPASS_EN  = 0   // 0: Read data will update at positive edge
                               // 1: Read data will update combinationally if
                               //    write to same address
   )
   (// ------------------------------------------------------------ //
    //                      Clock and Reset                         //
    // ------------------------------------------------------------ //
    input                                            clock,
    input                                            reset,

    // ------------------------------------------------------------ //
    //                      Read interface                          //
    // ------------------------------------------------------------ //
    input        [READ_PORTS-1:0]                    re,     // Read enable
    input        [READ_PORTS-1:0][$clog2(DEPTH)-1:0] raddr,  // Read address
    output logic [READ_PORTS-1:0][WIDTH        -1:0] rdata,  // Read data

    // ------------------------------------------------------------ //
    //                      Write interface                         //
    // ------------------------------------------------------------ //
    input                                            we,     // Write enable
    input                       [$clog2(DEPTH)-1:0]  waddr,  // Write address
    input                       [WIDTH        -1:0]  wdata   // Write data
    
`ifdef DEBUG
    , output logic [DEPTH-1:0][WIDTH-1:0]  debug_mem_data
`endif
   );


logic [DEPTH-1:0][WIDTH-1:0]  memData;
genvar i;

`ifdef DEBUG
    assign debug_mem_data = memData;
`endif
///////////////////////////////////////////////////////////////////
////////////////////////// Read Logic /////////////////////////////
///////////////////////////////////////////////////////////////////

generate
    for (i = 0; i < READ_PORTS; i++) begin
        always_comb begin
            if (BYPASS_EN != 0) begin : bypass_path
                if (re[i]) begin
                    if (we && (raddr[i] == waddr))
                        rdata[i] = wdata;
                    else
                        rdata[i] = memData[raddr[i]];
                end else begin
                    rdata[i] = '0;
                end
            end else begin : non_bypass_path
                rdata[i] = re[i] ? memData[raddr[i]] : '0;
            end
        end
    end
endgenerate
 
///////////////////////////////////////////////////////////////////
////////////////////////// Write Logic ////////////////////////////
///////////////////////////////////////////////////////////////////

always_ff @(posedge clock) begin
    if (reset) begin
        memData        <= '0;
    end else if (we) begin
        memData[waddr] <= wdata;
    end
    // for(int i = 0; i < DEPTH; ++i) begin
    //     $display("MemDP[%d]: %d", i, memData[i]);
    // end
end

///////////////////////////////////////////////////////////////////
////////////////////////// Assertions /////////////////////////////
///////////////////////////////////////////////////////////////////

`ifdef GEN_ASSERT
    logic [DEPTH-1:0] valid;
    
    // Track which entries are valid
    always_ff @(posedge clock) begin
        if      (reset) valid        <= '0;
        else if (we)    valid[waddr] <= 1'b1;              
    end

    // ---------- Verify Write Interface ---------- 
    clocking cb_read @(posedge clock);
        property waddr_valid;
            we |-> waddr < DEPTH;
        endproperty
    endclocking

    validWaddr:    assert property(cb_read.waddr_valid);
    
    // ---------- Verify Read Interface ---------- 
    generate
        for (i = 0; i < READ_PORTS; i++) begin
            clocking cb_write @(posedge clock);
                property raddr_valid;
                    re[i] |-> raddr[i] < DEPTH;
                endproperty

                property read_valid_data;
                    re[i] |-> valid[raddr[i]];
                endproperty
            endclocking

            validRaddr:    assert property(cb_write.raddr_valid);
            validRdData:   assert property(cb_write.read_valid_data);
        end
    endgenerate
`endif

endmodule
