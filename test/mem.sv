/////////////////////////////////////////////////////////////////////////
//                                                                     //
//  Modulename : mem.sv                                                //
//                                                                     //
// Description : This is a clock-based latency, pipelined memory with  //
//               3 buses (address in, data in, data out) and a limit   //
//               on the number of outstanding memory operations        //
//               allowed at any time.                                  //
//                                                                     //
/////////////////////////////////////////////////////////////////////////

`include "verilog/sys_defs.svh"

module mem (
    input           clock,         // Memory clock
    input ADDR      proc2mem_addr, // address for current command
                                   // support for memory model with byte level addressing
    input MEM_BLOCK proc2mem_data, // address for current command
`ifndef CACHE_MODE
    input MEM_SIZE  proc2mem_size, // BYTE, HALF, WORD or DOUBLE
`endif
    input [1:0]     proc2mem_command, // `MEM_NONE `MEM_LOAD or `MEM_STORE

    output MEM_TAG   mem2proc_transaction_tag, // Memory tag for current transaction (0 = can't accept)
    output MEM_BLOCK mem2proc_data,            // Data for a load
    output MEM_TAG   mem2proc_data_tag         // Tag for finished transactions (0 = no value)
);

    logic [63:0] unified_memory [`MEM_64BIT_LINES-1:0];

    MEM_BLOCK   next_mem2proc_data;
    MEM_TAG     next_mem2proc_transaction_tag, next_mem2proc_data_tag;

    wire [31:3] block_addr = proc2mem_addr[31:3];
    wire [2:0] byte_addr = proc2mem_addr[2:0];

    logic [63:0] loaded_data     [`NUM_MEM_TAGS:1];
    logic [15:0] cycles_left     [`NUM_MEM_TAGS:1];
    logic        waiting_for_bus [`NUM_MEM_TAGS:1];

    logic acquire_tag, bus_filled, valid_address;

    MEM_BLOCK load_data;

`ifndef CACHE_MODE
    MEM_BLOCK block;
`endif

    // Implement the Memory function
    always @(negedge clock) begin
        next_mem2proc_transaction_tag = 4'b0;
        next_mem2proc_data            = 64'bx;
        next_mem2proc_data_tag        = 4'b0;

`ifdef CACHE_MODE
        valid_address = (proc2mem_addr[2:0] == 3'b0) && (proc2mem_addr < `MEM_SIZE_IN_BYTES);
        if (valid_address) begin
            if (proc2mem_command == MEM_LOAD) begin
                load_data = unified_memory[block_addr];
            end else if (proc2mem_command == MEM_STORE) begin
                unified_memory[block_addr] = proc2mem_data;
            end
        end
`else
        valid_address = (proc2mem_addr < `MEM_SIZE_IN_BYTES);
        if (valid_address) begin
            // filling up the block data
            block = unified_memory[block_addr];
            if (proc2mem_command == MEM_LOAD) begin
                case (proc2mem_size)
                    BYTE:   load_data = {56'b0, block.byte_level[byte_addr[2:0]]};
                    HALF:   load_data = {48'b0, block.half_level[byte_addr[2:1]]};
                    WORD:   load_data = {32'b0, block.word_level[byte_addr[2]]};
                    DOUBLE: load_data = block;
                endcase
            end else if (proc2mem_command == MEM_STORE) begin
                case (proc2mem_size)
                    BYTE:   block.byte_level[byte_addr[2:0]] = proc2mem_data[7:0];
                    HALF:   block.half_level[byte_addr[2:1]] = proc2mem_data[15:0];
                    WORD:   block.word_level[byte_addr[2]]   = proc2mem_data[31:0];
                    DOUBLE: block                            = proc2mem_data;
                endcase
                unified_memory[block_addr] = block;
            end
        end
`endif // CACHE_MODE

        bus_filled  = 1'b0;
        acquire_tag = valid_address && (proc2mem_command == MEM_LOAD ||
                                        proc2mem_command == MEM_STORE);

        for (int i = 1; i <= `NUM_MEM_TAGS; i = i+1) begin
            if (cycles_left[i] > 16'd0) begin
                cycles_left[i] = cycles_left[i] - 16'd1;

            end else if (acquire_tag && !waiting_for_bus[i]) begin
                next_mem2proc_transaction_tag = i;
                acquire_tag    = 1'b0;
                cycles_left[i] = `MEM_LATENCY_IN_CYCLES;
                // must add support for random lantencies though this could be
                // done via a non-number definition for this macro
                if (proc2mem_command == MEM_LOAD) begin
                    waiting_for_bus[i] = 1'b1;
                    loaded_data[i]     = load_data;
                end
            end

            if ((cycles_left[i] == 16'd0) && waiting_for_bus[i] && !bus_filled) begin
                bus_filled         = 1'b1;
                waiting_for_bus[i] = 1'b0;
                next_mem2proc_data_tag = i;
                next_mem2proc_data     = loaded_data[i];
            end
        end
        mem2proc_transaction_tag <= next_mem2proc_transaction_tag;
        mem2proc_data            <= next_mem2proc_data;
        mem2proc_data_tag        <= next_mem2proc_data_tag;
    end

    // Initialise the entire memory
    initial begin
        // This posedge is very important, it ensures that we don't enter a race
        // condition with the negedge driven block above.
        @(posedge clock);
        for (int i = 0; i < `MEM_64BIT_LINES; i = i+1) begin
            unified_memory[i] = 64'h0;
        end
        mem2proc_transaction_tag = 4'd0;
        mem2proc_data_tag = 4'd0;
        mem2proc_data     = 64'bx;
        for (int i = 1; i <= `NUM_MEM_TAGS; i = i+1) begin
            loaded_data[i] = 64'bx;
            cycles_left[i] = 16'd0;
            waiting_for_bus[i] = 1'b0;
        end
    end

    always_ff @(posedge clock) begin

        // $display("------------- MEM ------------");

        // $display("mem2proc_transaction_tag: %d", mem2proc_transaction_tag);
        // $display("mem2proc_command: %d", proc2mem_command);
        // $display("valid_address: %b", valid_address);
        // $display("proc2mem_addr: %d", proc2mem_addr);
        // $display("MEM_SIZE_IN_BYTES: %d", `MEM_SIZE_IN_BYTES);
        // $display("mem2proc_data_tag: %d", mem2proc_data_tag);
        // for (int i = 1; i <= `NUM_MEM_TAGS; ++i) begin
        //     $display("waiting_for_bus[%d]: %b", i, waiting_for_bus[i]);
        // end
        // for (int i = 1; i <= `NUM_MEM_TAGS; ++i) begin
        //     $display("cycles_left[%d]: %d", i, cycles_left[i]);
        // end
        // $display("acquire_tag: %b", acquire_tag);
    end

endmodule // module mem
