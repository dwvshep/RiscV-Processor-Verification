/////////////////////////////////////////////////////////////////////////
//                                                                     //
//   Modulename :  icache.sv                                           //
//                                                                     //
//  Description :  The instruction cache module that reroutes memory   //
//                 accesses to decrease misses.                        //
//                                                                     //
/////////////////////////////////////////////////////////////////////////

`include "verilog/sys_defs.svh"

/**
 * A quick overview of the cache and memory:
 *
 * We've increased the memory latency from 1 cycle to 100ns. which will be
 * multiple cycles for any reasonable processor. Thus, memory can have multiple
 * transactions pending and coordinates them via memory tags (different meaning
 * than cache tags) which represent a transaction it's working on. Memory tags
 * are 4 bits long since 15 mem accesses can be live at one time, and only one
 * access happens per cycle.
 *
 * On a request, memory responds with the tag it will use for that transaction.
 * Then, ceiling(100ns/clock period) cycles later, it will return the data with
 * the corresponding tag. The 0 tag is a sentinel value and unused. It would be
 * very difficult to push your clock period past 100ns/15=6.66ns, so 15 tags is
 * sufficient.
 *
 * This cache coordinates those memory tags to speed up fetching reused data.
 *
 * Note that this cache is blocking, and will wait on one memory request before
 * sending another (unless the input address changes, in which case it abandons
 * that request). Implementing a non-blocking cache can count towards simple
 * feature points, but will require careful management of memory tags.
 */

module icache (
    input clock,
    input reset,

    // ------------ TO/FROM FETCH ---------------//
    input ADDR                   [`N-1:0] PCs_out,
    output DATA                  [`N-1:0] cache_data, //instructions being sent to Fetch
    output logic                 [`N-1:0] cache_miss, 
 
    // ------------ TO/FROM MAIN MEMORY (MEM ARBITER) ---------------//
    input logic                             icache_mem_req_accepted,
    input MEM_TAG                           icache_mem_trxn_tag,
    input MEM_DATA_PACKET                   mem_data_packet,
    output MEM_REQ_PACKET                   icache_mem_req_packet,

    // ------------ FROM BRANCH STACK ---------------//
    input logic                             restore_valid
);
    
    // ----- mshr wires ----- // 

    ICACHE_MSHR_ENTRY [`MSHR_SZ-1:0]        mshrs, next_mshrs; 
    logic      [`MSHR_NUM_ENTRIES_BITS-1:0] mshr_spots, next_mshr_spots;
    MSHR_IDX                                mshr_head, next_mshr_head; // Next mshr to get mem data
    MSHR_IDX                                mshr_tail, next_mshr_tail; // Next mshr to get assigned a mem req
    logic              [`PREFETCH_DIST-1:0] mshr_miss;   
    
    // ---- ICACHE WIRES ---- //

    wand                               [`PREFETCH_DIST-1:0] icache_miss;  // TODO: MAKE SURE THIS WORKS! (. O .)
    DATA                      [`ICACHE_NUM_BANKS-1:0] [1:0] icache_rd_data; 
    ADDR                               [`PREFETCH_DIST-1:0] prefetch_window;
    logic                              [`PREFETCH_DIST-1:0] prefetch_miss;

    wor                                                     mem_data_returned;
    logic                              [`PREFETCH_DIST-1:0] prefetch_inst;

    assign prefetch_miss = icache_miss & mshr_miss;

    always_comb begin
        prefetch_window = '0;
        for (int i = 0; i < `PREFETCH_DIST; ++i) begin
            prefetch_window[i] = PCs_out[0] + (4 * i);
        end
    end

    lsb_psel_gen #(
        .WIDTH(`PREFETCH_DIST),
        .REQS(1) 
    ) icache_psel (
        .req(prefetch_miss),
        .gnt(prefetch_inst)
    );

    always_comb begin
        icache_mem_req_packet = '0;
        next_mshrs = mshrs;
        for (int i = 0; i < `PREFETCH_DIST; ++i) begin
            if (prefetch_inst[i]) begin
                icache_mem_req_packet.valid = 1'b1;
                icache_mem_req_packet.prior = i < `N;
                icache_mem_req_packet.addr.dw.addr = prefetch_window[i].dw.addr;
                if (icache_mem_req_accepted) begin
                    next_mshrs[mshr_tail].mem_tag = icache_mem_trxn_tag;
                    next_mshrs[mshr_tail].addr.dw.addr = prefetch_window[i].dw.addr;
                end
            end
        end
    end


    //generate the BANKS 
    generate
        genvar i;
        for (i = 0; i < `ICACHE_NUM_BANKS; ++i) begin
            logic temp_mem_data_returned;
            logic [`PREFETCH_DIST-1:0] temp_icache_miss;
            logic icache_rd_en, icache_wr_en;
            ICACHE_IDX icache_rd_idx, icache_wr_idx;
            DATA [1:0] icache_wr_data;
            ICACHE_META_DATA [`ICACHE_NUM_SETS-1:0] icache_meta_data, next_icache_meta_data;

            assign mem_data_returned = temp_mem_data_returned;
            assign icache_miss = temp_icache_miss;

            memDP #(
                .WIDTH     ($bits(MEM_BLOCK)),
                .DEPTH     (`ICACHE_LINES),
                .READ_PORTS(1),
                .BYPASS_EN (0))
            icache_mem (
                .clock(clock),
                .reset(reset),
                .re   (1'b1),
                .raddr(icache_rd_idx),
                .rdata(icache_rd_data[i]),
                .we   (icache_wr_en),
                .waddr(icache_wr_idx),
                .wdata(icache_wr_data)
            );

            // cam
            always_comb begin
                temp_icache_miss = '1;
                icache_rd_idx = '0;
                for (int j = 0; j < `PREFETCH_DIST; ++j) begin
                    if ((prefetch_window[j].icache.bank_idx == i) && (icache_meta_data[prefetch_window[j].icache.set_idx].valid) && (icache_meta_data[prefetch_window[j].icache.set_idx].addr.icache.tag == prefetch_window[j].icache.tag)) begin
                        temp_icache_miss[j] = 1'b0;
                        if (j < `N) begin
                            icache_rd_idx = prefetch_window[j].icache.set_idx;
                        end
                    end
                end
            end

            always_comb begin
                icache_wr_en = 0;
                icache_wr_data = 0;
                icache_wr_idx = 0;
                temp_mem_data_returned = 1'b0;
                next_icache_meta_data = icache_meta_data;

                if ((mshr_head != mshr_tail) && mem_data_packet.mem_tag == mshrs[mshr_head].mem_tag) begin
                    if (mshrs[mshr_head].addr.icache.bank_idx == i) begin
                        next_icache_meta_data[mshrs[mshr_head].addr.icache.set_idx].valid = 1'b1;
                        next_icache_meta_data[mshrs[mshr_head].addr.icache.set_idx].addr.icache.tag = mshrs[mshr_head].addr.icache.tag;
                        icache_wr_idx = mshrs[mshr_head].addr.icache.set_idx;
                        icache_wr_en = 1;
                        icache_wr_data = mem_data_packet.data;
                        temp_mem_data_returned = 1'b1;
                    end
                end
            end

            always_ff @(posedge clock) begin
                if (reset) begin
                    icache_meta_data <= '0;
                end else begin
                    icache_meta_data <= next_icache_meta_data;
                end

                /*$display("--------- ICACHE -----------");
                for(int i = 0; i < `ICACHE_LINES; ++i) begin
                    $display("I$[%d]: %d", i, icache_mem.memData[i]);
                end
                for(int i = 0; i < `ICACHE_LINES; ++i) begin
                    $display("I$_meta_data[%d].valid: %b", i, icache_meta_data[i].valid);
                end
                for(int i = 0; i < `ICACHE_LINES; ++i) begin
                    $display("I$_meta_data[%d].addr: %h", i, icache_meta_data[i].addr);
                end*/
            end
        end
    endgenerate

    //cam mshrs for in flight pcs
    always_comb begin
        mshr_miss = '1;
        for (int i = 0; i < `PREFETCH_DIST; ++i) begin //genvar might yell at us
            for (int j = 0; j < `MSHR_SZ; ++j) begin
                if((j < `MSHR_SZ - mshr_spots) && (prefetch_window[i].dw.addr == mshrs[(mshr_head + j) % `MSHR_SZ].addr.dw.addr)) begin
                   mshr_miss[i] = 1'b0;
                end
            end
        end
    end

    always_comb begin
        cache_miss = '1;
        cache_data = '0;
        for (int i = 0; i < `N; ++i) begin
            if (!icache_miss[i]) begin
                cache_miss[i] = 1'b0;
                cache_data[i] = icache_rd_data[PCs_out[i].icache.bank_idx][PCs_out[i].dw.w_idx];
            end
        end
    end

    // update next pointers
    always_comb begin
        // next_mshr_spots = restore_valid ? `MSHR_SZ - icache_mem_req_accepted : mshr_spots - icache_mem_req_accepted + mem_data_returned;
        next_mshr_spots = restore_valid ? `MSHR_SZ : mshr_spots - icache_mem_req_accepted + mem_data_returned;
        next_mshr_tail = (mshr_tail + icache_mem_req_accepted) % `MSHR_SZ;
        // next_mshr_head = restore_valid ? mshr_tail : (mshr_head + mem_data_returned) % `MSHR_SZ;
        next_mshr_head = restore_valid ? next_mshr_tail : (mshr_head + mem_data_returned) % `MSHR_SZ;
    end

    always_ff @(posedge clock) begin
        if (reset) begin
            mshr_head <= '0;
            mshr_tail <= '0;
            mshrs <= '0;
            mshr_spots <= `MSHR_SZ;
        end else begin
            mshr_head <= next_mshr_head;
            mshr_tail <= next_mshr_tail;
            mshrs <= next_mshrs;
            mshr_spots <= next_mshr_spots;
        end
        // $display("------- ICACHE -------- ");
        // $display("cache_miss: %b", cache_miss);
        // $display("icache_mem_trxn_tag: %d", icache_mem_trxn_tag);
        // $display("icache_mem_data_tag: %d", mem_data_packet.mem_tag);
        // $display("icache_mem_req_accepted: %d", icache_mem_req_accepted);
        // $display("mshr_head: %d", mshr_head);
        // $display("mshr_tail: %d", mshr_tail);
        // $display("mshr_spots: %d", mshr_spots);
        // $display("next_mshr_tail: %d", next_mshr_tail);
        // $display("prefetch_inst: %b", prefetch_inst);
        // $display("PC[0]: %h", PCs_out[0]);
        // for (int i = 0; i < `MSHR_SZ; ++i) begin
        //     $display("mshr[%d].mem_tag: %d", i, mshrs[i].mem_tag);
        //     $display("mshr[%d].addr: %h", i, mshrs[i].addr);
        // end
        // for (int i = 0; i < `PREFETCH_DIST; ++i) begin
        //     $display("mshr[%d].mem_tag: %d", i, mshrs[i].mem_tag);
        //     $display("mshr[%d].addr: %h", i, mshrs[i].addr);
        // end
    end
        


endmodule // icache
