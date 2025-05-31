
/////////////////////////////////////////////////////////////////////////
//                                                                     //
//   Modulename :  dcache.sv                                           //
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

module dcache (
    input logic clock,
    input logic reset,

    // ------------------- LOAD DATA STAGE --------------- //
    input logic                             load_req_valid,
    input ADDR                              load_req_addr,
    output LOAD_DATA_CACHE_PACKET           load_data_cache_packet,        

    // ------------------- LOAD BUFFER --------------- //
    output LOAD_BUFFER_CACHE_PACKET         load_buffer_cache_packet,
    
    // ------------------- STORE UNIT --------------- //
    input logic                             store_req_valid,
    input ADDR                              store_req_addr,
    input DATA                              store_req_data,
    input BYTE_MASK                           store_req_byte_mask,
    output logic                            store_req_accepted, // TODO Make sure this works. At the very least, this is how it should be thought of

    // ------------------ MAIN MEM ------------------- //
    input logic                             dcache_mem_req_accepted,
    input MEM_TAG                           dcache_mem_trxn_tag,
    input MEM_DATA_PACKET                   mem_data_packet,
    output MEM_REQ_PACKET                   dcache_mem_req_packet

`ifdef DEBUG
    , output logic [`DCACHE_LINES-1:0]             [$bits(MEM_BLOCK)-1:0] debug_mem_data_dcache,
    output logic [`VCACHE_LINES-1:0]               [$bits(MEM_BLOCK)-1:0] debug_mem_data_vcache,
    output DCACHE_META_DATA [`DCACHE_NUM_SETS-1:0] [`DCACHE_NUM_WAYS-1:0] debug_dcache_meta_data,
    output VCACHE_META_DATA                           [`VCACHE_LINES-1:0] debug_vcache_meta_data, 
    output MSHR_IDX                                                       debug_mshr_true_head,
    output logic                             [`MSHR_NUM_ENTRIES_BITS-1:0] debug_mshr_spots,
    output DCACHE_MSHR_ENTRY                               [`MSHR_SZ-1:0] debug_mshrs,
    output WB_IDX                                                         debug_wb_head,
    output logic                               [`WB_NUM_ENTRIES_BITS-1:0] debug_wb_spots,
    output WB_ENTRY                                       [`WB_LINES-1:0] debug_wb_buffer
`endif
);

    // ------- WB BUFFER WIRES -------- //
    
    WB_ENTRY         [`WB_LINES-1:0] wb_buffer, next_wb_buffer; 
    WB_IDX                           wb_head, next_wb_head;
    WB_IDX                           wb_tail, next_wb_tail; 
    logic                            load_wb_hit;
    WB_IDX                           load_wb_idx;
    logic                            store_wb_hit;
    WB_IDX                           store_wb_idx;
    logic [`WB_NUM_ENTRIES_BITS-1:0] wb_spots, next_wb_spots;
    logic                            wb_allocated;
    logic                            wb_mem_accepted;
    

    // ------- MSHR WIRES -------- //
    
    DCACHE_MSHR_ENTRY [`MSHR_SZ-1:0] mshrs, next_mshrs; 
    MSHR_IDX                         mshr_true_head, next_mshr_true_head;
    MSHR_IDX                         mshr_head, next_mshr_head; 
    MSHR_IDX                         mshr_tail, next_mshr_tail; 
    
    logic                            load_mshr_hit;
    MSHR_IDX                         load_mshr_idx;
    logic                            store_mshr_hit;
    MSHR_IDX                         store_mshr_idx;

    logic [`MSHR_NUM_ENTRIES_BITS-1:0] mshr_spots, next_mshr_spots;
    logic                              mshr_cache_accepted;
    logic                              mshr_allocated;
    logic                              mem_data_returned;

    
    // ---- DCACHE WIRES ---- //

    DCACHE_META_DATA [`DCACHE_NUM_SETS-1:0] [`DCACHE_NUM_WAYS-1:0] dcache_meta_data, next_dcache_meta_data;
    DCACHE_WAY_IDX [`DCACHE_NUM_SETS-1:0] dcache_lru_idx;
    
    logic                                load_dcache_hit;
    DCACHE_IDX                           load_dcache_idx;
    logic                                store_dcache_hit;
    DCACHE_IDX                           store_dcache_idx;

    DCACHE_IDX                           dcache_idx;
    DCACHE_IDX                           dcache_set_idx;
    DCACHE_IDX                           dcache_way_idx;
    DATA                           [1:0] dcache_data_out;
    logic                                dcache_rd_en;
    logic                                dcache_wr_en;
    DATA                           [1:0] dcache_wr_data;

    

    // ----- VCACHE WIRES ---- //
    VCACHE_META_DATA [`VCACHE_LINES-1:0] vcache_meta_data, next_vcache_meta_data;
    logic         [`VCACHE_NUM_WAYS-1:0] vcache_lru_gnt_line;
    VCACHE_IDX                           vcache_lru_idx;

    logic                                load_vcache_hit;
    VCACHE_IDX                           load_vcache_idx;
    logic                                store_vcache_hit;
    VCACHE_IDX                           store_vcache_idx;

    VCACHE_IDX                           vcache_idx;
    DATA                           [1:0] vcache_data_out;
    logic                                vcache_rd_en;
    logic                                vcache_wr_en;
    DATA                           [1:0] vcache_wr_data;

    logic  load_miss, store_miss;
    assign load_miss = load_req_valid && !load_wb_hit && !load_mshr_hit && !load_dcache_hit && !load_vcache_hit;
    assign store_miss = store_req_valid && !store_wb_hit && !store_mshr_hit && !store_dcache_hit && !store_vcache_hit; 

    logic mshr_full;
    assign mshr_full = mshr_spots == 0;

    logic  valid_dcache_lru, dirty_vcache_lru;
    assign valid_dcache_lru = dcache_meta_data[mshrs[mshr_true_head].addr.dcache.set_idx][dcache_lru_idx[mshrs[mshr_true_head].addr.dcache.set_idx]].valid;
    assign dirty_vcache_lru = vcache_meta_data[vcache_lru_idx].valid && vcache_meta_data[vcache_lru_idx].dirty;

    logic full_eviction;
    assign full_eviction = valid_dcache_lru && dirty_vcache_lru && (wb_spots == 0);

    memDP #(
        .WIDTH     ($bits(MEM_BLOCK)),
        .DEPTH     (`DCACHE_LINES),
        .READ_PORTS(1),
        .BYPASS_EN (0))
    dcache_mem (
        .clock(clock),
        .reset(reset),
        .re   (dcache_rd_en),
        .raddr(dcache_idx),
        .rdata(dcache_data_out),
        .we   (dcache_wr_en),
        .waddr(dcache_idx),
        .wdata(dcache_wr_data)
    `ifdef DEBUG
        , .debug_mem_data(debug_mem_data_dcache)
    `endif
    );

    memDP #(
        .WIDTH     ($bits(MEM_BLOCK)),
        .DEPTH     (`VCACHE_LINES), 
        .READ_PORTS(1),
        .BYPASS_EN (0))
    vcache_mem (
        .clock(clock),
        .reset(reset),
        .re   (vcache_rd_en),
        .raddr(vcache_idx),
        .rdata(vcache_data_out),
        .we   (vcache_wr_en),
        .waddr(vcache_idx),
        .wdata(vcache_wr_data)
    `ifdef DEBUG
        , .debug_mem_data(debug_mem_data_vcache)
    `endif
    );

    // ---------------------- create mem req ------------------- //

    always_comb begin 
        dcache_mem_req_packet = '0;
        wb_mem_accepted = 1'b0;

        if (mshr_allocated) begin
            dcache_mem_req_packet.valid = 1'b1;
            dcache_mem_req_packet.prior = 1'b1;
            dcache_mem_req_packet.addr.dw.addr = next_mshrs[mshr_tail].addr.dw.addr;
            dcache_mem_req_packet.data = next_mshrs[mshr_tail].data;
        end else if (wb_spots != `WB_LINES) begin
            dcache_mem_req_packet.valid = 1'b1;
            dcache_mem_req_packet.prior = 1'b0;
            dcache_mem_req_packet.addr.dw.addr = next_wb_buffer[wb_head].addr.dw.addr;
            dcache_mem_req_packet.data = next_wb_buffer[wb_head].data; 
            wb_mem_accepted = dcache_mem_req_accepted;
        end
    end 

    // ---------------------- all hit logic -------------------- //
    always_comb begin
        next_mshrs = mshrs;
        next_dcache_meta_data = dcache_meta_data;
        dcache_idx = '0;
        dcache_rd_en = 1'b0;
        dcache_wr_en = 1'b0;
        dcache_wr_data = '0;

        next_vcache_meta_data = vcache_meta_data;
        vcache_idx = '0;
        vcache_rd_en = 1'b0;
        vcache_wr_en = 1'b0;
        vcache_wr_data = '0;
        
        mshr_cache_accepted = 1'b0;
        mshr_allocated = 1'b0;
        mem_data_returned = 1'b0;

        next_wb_buffer = wb_buffer;
        wb_allocated = 1'b0;

        store_req_accepted = 1'b0;
        load_data_cache_packet = '0;
        load_buffer_cache_packet = '0; 

        if ((mshr_head != mshr_tail) && mem_data_packet.mem_tag == mshrs[mshr_head].mem_tag) begin
            mem_data_returned = 1'b1;
            for (int i = 0; i < 2; ++i) begin
                for (int j = 0; j < 4; ++j) begin
                    if (!mshrs[mshr_head].byte_mask[i][j]) begin
                        next_mshrs[mshr_head].data[i].bytes[j] = mem_data_packet.data[i].bytes[j];
                    end
                end
            end
            next_mshrs[mshr_head].byte_mask = '1;

            load_buffer_cache_packet.valid = 1'b1;
            load_buffer_cache_packet.mshr_idx = mshr_head;
            load_buffer_cache_packet.data = next_mshrs[mshr_head].data;
        end

        // include mshr hit logic

        if (load_mshr_hit) begin
            load_data_cache_packet.valid = 1'b1;
            load_data_cache_packet.mshr_idx = load_mshr_idx;
            load_data_cache_packet.byte_mask = next_mshrs[load_mshr_idx].byte_mask;
            load_data_cache_packet.data = next_mshrs[load_mshr_idx].data;
        end

        if (store_mshr_hit) begin
            store_req_accepted = 1'b1;
            for (int i = 0; i < 4; ++i) begin
                if (store_req_byte_mask[i]) begin
                    next_mshrs[store_mshr_idx].data[store_req_addr.dw.w_idx].bytes[i] = store_req_data.bytes[i];
                    next_mshrs[store_mshr_idx].byte_mask[store_req_addr.dw.w_idx][i] = 1'b1;
                end
            end
            next_mshrs[store_mshr_idx].dirty = 1'b1;
        end

        if (load_wb_hit) begin
            load_data_cache_packet.valid = 1'b1;
            load_data_cache_packet.byte_mask = 8'hFF;
            load_data_cache_packet.data = wb_buffer[load_wb_idx].data;
        end

        if (store_wb_hit) begin
            store_req_accepted = 1'b1;
            for (int i = 0; i < 4; ++i) begin
                if (store_req_byte_mask[i]) begin
                    next_wb_buffer[store_wb_idx].data[store_req_addr.dw.w_idx].bytes[i] = store_req_data.bytes[i];
                end
            end
        end

        if (load_dcache_hit) begin
            load_data_cache_packet.valid = 1'b1;
            dcache_rd_en = 1'b1;

            dcache_idx = load_dcache_idx;

            load_data_cache_packet.byte_mask = 8'hFF; //shove that shi IN 
            load_data_cache_packet.data = dcache_data_out;

        end else if (load_vcache_hit) begin
            load_data_cache_packet.valid = 1'b1;
            dcache_rd_en = 1'b1;
            dcache_wr_en = 1'b1;
            vcache_rd_en = 1'b1;
            vcache_wr_en = 1'b1;

            dcache_idx = (load_req_addr.dcache.set_idx << `DCACHE_WAY_IDX_BITS) + dcache_lru_idx[load_req_addr.dcache.set_idx];
            vcache_idx = load_vcache_idx;
            dcache_wr_data = vcache_data_out;
            vcache_wr_data = dcache_data_out;

            next_dcache_meta_data[load_req_addr.dcache.set_idx][dcache_lru_idx[load_req_addr.dcache.set_idx]].addr = vcache_meta_data[load_vcache_idx].addr;
            next_dcache_meta_data[load_req_addr.dcache.set_idx][dcache_lru_idx[load_req_addr.dcache.set_idx]].dirty = vcache_meta_data[load_vcache_idx].dirty;

            next_vcache_meta_data[load_vcache_idx].addr = dcache_meta_data[load_req_addr.dcache.set_idx][dcache_lru_idx[load_req_addr.dcache.set_idx]].addr;
            next_vcache_meta_data[load_vcache_idx].dirty = dcache_meta_data[load_req_addr.dcache.set_idx][dcache_lru_idx[load_req_addr.dcache.set_idx]].dirty;
            
            load_data_cache_packet.byte_mask = 8'hFF;
            load_data_cache_packet.data = vcache_data_out;
            
        end else if (store_dcache_hit) begin
            store_req_accepted = 1'b1;

            dcache_rd_en = 1'b1;
            dcache_wr_en = 1'b1;
            dcache_idx = store_dcache_idx;

            dcache_wr_data = dcache_data_out;
            for (int i = 0; i < 4; ++i) begin
                if (store_req_byte_mask[i]) begin
                    dcache_wr_data[store_req_addr.dw.w_idx].bytes[i] = store_req_data.bytes[i];
                end
            end

            next_dcache_meta_data[store_req_addr.dcache.set_idx][store_dcache_idx & {`DCACHE_WAY_IDX_BITS{1'b1}}].dirty = 1'b1;

        end else if (store_vcache_hit) begin
            store_req_accepted = 1'b1;

            dcache_rd_en = 1'b1;
            dcache_wr_en = 1'b1;
            vcache_rd_en = 1'b1;
            vcache_wr_en = 1'b1;

            dcache_idx = (store_req_addr.dcache.set_idx << `DCACHE_WAY_IDX_BITS) + dcache_lru_idx[store_req_addr.dcache.set_idx];
            vcache_idx = store_vcache_idx;

            dcache_wr_data = vcache_data_out; //return store to d$
            for (int i = 0; i < 4; ++i) begin
                if (store_req_byte_mask[i]) begin
                    dcache_wr_data[store_req_addr.dw.w_idx].bytes[i] = store_req_data.bytes[i];
                end
            end
        
            vcache_wr_data = dcache_data_out; //evict to v$

            next_dcache_meta_data[store_req_addr.dcache.set_idx][dcache_lru_idx[store_req_addr.dcache.set_idx]].addr = vcache_meta_data[store_vcache_idx].addr;
            next_dcache_meta_data[store_req_addr.dcache.set_idx][dcache_lru_idx[store_req_addr.dcache.set_idx]].dirty = 1'b1;

            next_vcache_meta_data[store_vcache_idx].addr = dcache_meta_data[store_req_addr.dcache.set_idx][dcache_lru_idx[store_req_addr.dcache.set_idx]].addr;
            next_vcache_meta_data[store_vcache_idx].dirty = dcache_meta_data[store_req_addr.dcache.set_idx][dcache_lru_idx[store_req_addr.dcache.set_idx]].dirty;

        end else if (((mshr_true_head != next_mshr_head) || mshr_full) && (!full_eviction || wb_mem_accepted)) begin
            // $display("MSHR CACHE WRITE");
            mshr_cache_accepted = 1'b1;
            dcache_rd_en = 1'b1;
            dcache_wr_en = 1'b1;
            dcache_wr_data = next_mshrs[mshr_true_head].data;
            dcache_idx = (mshrs[mshr_true_head].addr.dcache.set_idx << `DCACHE_WAY_IDX_BITS) + dcache_lru_idx[mshrs[mshr_true_head].addr.dcache.set_idx];
            next_dcache_meta_data[mshrs[mshr_true_head].addr.dcache.set_idx][dcache_lru_idx[mshrs[mshr_true_head].addr.dcache.set_idx]].dirty = next_mshrs[mshr_true_head].dirty;
            next_dcache_meta_data[mshrs[mshr_true_head].addr.dcache.set_idx][dcache_lru_idx[mshrs[mshr_true_head].addr.dcache.set_idx]].addr = next_mshrs[mshr_true_head].addr;
            next_dcache_meta_data[mshrs[mshr_true_head].addr.dcache.set_idx][dcache_lru_idx[mshrs[mshr_true_head].addr.dcache.set_idx]].valid = 1;

            // punt to victim cache 
            if (valid_dcache_lru) begin

                next_vcache_meta_data[vcache_lru_idx].addr = dcache_meta_data[mshrs[mshr_true_head].addr.dcache.set_idx][dcache_lru_idx[mshrs[mshr_true_head].addr.dcache.set_idx]].addr;
                next_vcache_meta_data[vcache_lru_idx].dirty = dcache_meta_data[mshrs[mshr_true_head].addr.dcache.set_idx][dcache_lru_idx[mshrs[mshr_true_head].addr.dcache.set_idx]].dirty;
                next_vcache_meta_data[vcache_lru_idx].valid = 1'b1;
                vcache_rd_en = 1'b1;
                vcache_wr_en = 1'b1;
                vcache_wr_data = dcache_data_out;
                vcache_idx = vcache_lru_idx;
                
                // punt to wb buffer
                if (dirty_vcache_lru) begin
                    next_wb_buffer[wb_tail].data = vcache_data_out;
                    next_wb_buffer[wb_tail].addr = vcache_meta_data[vcache_lru_idx].addr;
                    wb_allocated = 1'b1;
                end
            end    
        end

        if (!mshr_full) begin
            if (load_miss) begin
                next_mshrs[mshr_tail] = '0;

                load_data_cache_packet.valid = 1'b1;
                load_data_cache_packet.mshr_idx = mshr_tail;
                mshr_allocated = 1'b1;
                next_mshrs[mshr_tail].dirty = 0;
                next_mshrs[mshr_tail].addr.dw.addr = load_req_addr.dw.addr; 
                next_mshrs[mshr_tail].data = '0;
                next_mshrs[mshr_tail].byte_mask = '0;

                // Happens after the mem request is created
                next_mshrs[mshr_tail].mem_tag = dcache_mem_trxn_tag;
            end else if (store_miss) begin
                next_mshrs[mshr_tail] = '0;

                store_req_accepted = 1'b1;
                mshr_allocated = 1'b1;
                next_mshrs[mshr_tail].dirty = 1;
                next_mshrs[mshr_tail].addr.dw.addr = store_req_addr.dw.addr;
                next_mshrs[mshr_tail].data[store_req_addr.dw.w_idx] = store_req_data;
                next_mshrs[mshr_tail].byte_mask[store_req_addr.dw.w_idx] = store_req_byte_mask;

                // Happens after the mem request is created
                next_mshrs[mshr_tail].mem_tag = dcache_mem_trxn_tag;
            end
        end

        // update lru bits
        dcache_set_idx = dcache_idx >> `DCACHE_WAY_IDX_BITS;
        dcache_way_idx = dcache_idx & {`DCACHE_WAY_IDX_BITS{1'b1}};
        if (dcache_rd_en || dcache_wr_en) begin
            next_dcache_meta_data[dcache_set_idx][dcache_way_idx].lru = `DCACHE_NUM_WAYS - 1;
            for (int i = 0; i < `DCACHE_NUM_WAYS; ++i) begin
                if (dcache_meta_data[dcache_set_idx][i].valid && dcache_meta_data[dcache_set_idx][i].lru > dcache_meta_data[dcache_set_idx][dcache_way_idx].lru) begin
                    next_dcache_meta_data[dcache_set_idx][i].lru--;
                end
            end
        end

        if (vcache_rd_en || vcache_wr_en) begin
            next_vcache_meta_data[vcache_idx].lru = `VCACHE_NUM_WAYS - 1;
            for (int i = 0; i < `VCACHE_NUM_WAYS; ++i) begin
                if (vcache_meta_data[i].valid && (vcache_meta_data[i].lru > vcache_meta_data[vcache_idx].lru)) begin
                    next_vcache_meta_data[i].lru--;
                end 
            end
        end
    end

    // Find the LRU index for each set in the dcache
    generate
    genvar i;
    genvar j;

    for (i = 0; i < `DCACHE_NUM_SETS; ++i) begin
        logic [`DCACHE_NUM_WAYS-1:0] lru_gnt_line;
        logic [`DCACHE_NUM_WAYS-1:0] requests;

        for(j = 0; j < `DCACHE_NUM_WAYS; ++j) begin
            assign requests[j] = dcache_meta_data[i][j].lru == 0;
        end
        
        psel_gen #(
            .WIDTH(`DCACHE_NUM_WAYS),
            .REQS(1)
        ) lru_psel (
            .req(requests),
            .gnt(lru_gnt_line)
        );

        encoder #(`DCACHE_NUM_WAYS, `DCACHE_WAY_IDX_BITS) lru_idx_encoder (lru_gnt_line, dcache_lru_idx[i]);
    end

    endgenerate

    // Find the LRU index for the vcache

    logic [`VCACHE_NUM_WAYS-1:0] vcache_lru_requests;

    always_comb begin
        for(int jj = 0; jj < `VCACHE_NUM_WAYS; ++jj) begin
            vcache_lru_requests[jj] = vcache_meta_data[jj].lru == 0;
        end
    end
    
    psel_gen #(
        .WIDTH(`VCACHE_NUM_WAYS),
        .REQS(1)
    ) lru_psel (
        .req(vcache_lru_requests),
        .gnt(vcache_lru_gnt_line)
    );

    encoder #(`VCACHE_NUM_WAYS, `VCACHE_WAY_IDX_BITS) lru_idx_encoder (vcache_lru_gnt_line, vcache_lru_idx);

    // cam that dcache shi
    always_comb begin
        load_dcache_hit = 1'b0;
        load_dcache_idx = '0;
        store_dcache_hit = 1'b0;
        store_dcache_idx = '0;

        for (int i = 0; i < `DCACHE_NUM_WAYS; ++i) begin
            if (load_req_valid && dcache_meta_data[load_req_addr.dcache.set_idx][i].valid && dcache_meta_data[load_req_addr.dcache.set_idx][i].addr.dcache.tag == load_req_addr.dcache.tag) begin
                load_dcache_hit = 1;
                load_dcache_idx = (load_req_addr.dcache.set_idx << `DCACHE_WAY_IDX_BITS) + i;
            end
        end

        for (int i = 0; i < `DCACHE_NUM_WAYS; ++i) begin
            if (store_req_valid && dcache_meta_data[store_req_addr.dcache.set_idx][i].valid && dcache_meta_data[store_req_addr.dcache.set_idx][i].addr.dcache.tag == store_req_addr.dcache.tag) begin
                store_dcache_hit = 1;
                store_dcache_idx = (store_req_addr.dcache.set_idx << `DCACHE_WAY_IDX_BITS) + i;
            end
        end
    end

    //cam that mshr shi
    always_comb begin
        load_mshr_hit = 1'b0;
        load_mshr_idx = '0;
        store_mshr_hit = 1'b0;
        store_mshr_idx = '0;

        for (int i = 0; i < `MSHR_SZ; ++i) begin
            if (i < `MSHR_SZ - mshr_spots) begin
                if (load_req_valid && mshrs[(mshr_true_head + i) % `MSHR_SZ].addr.dw.addr == load_req_addr.dw.addr) begin
                    load_mshr_hit = 1'b1;
                    load_mshr_idx = (mshr_true_head + i) % `MSHR_SZ;
                end
                if (store_req_valid && mshrs[(mshr_true_head + i) % `MSHR_SZ].addr.dw.addr == store_req_addr.dw.addr) begin
                    store_mshr_hit = 1'b1;
                    store_mshr_idx = (mshr_true_head + i) % `MSHR_SZ;
                end
            end
        end
    end

    //cam that vcache shi
    always_comb begin
        load_vcache_hit = 1'b0;
        load_vcache_idx = '0;
        store_vcache_hit = 1'b0;
        store_vcache_idx = '0;
        for (int i = 0; i < `VCACHE_LINES; ++i) begin
            if (load_req_valid && vcache_meta_data[i].valid && vcache_meta_data[i].addr.dw.addr == load_req_addr.dw.addr) begin
                load_vcache_hit = 1'b1;
                load_vcache_idx = i;
            end 
            if (store_req_valid && vcache_meta_data[i].valid && vcache_meta_data[i].addr.dw.addr == store_req_addr.dw.addr) begin
                store_vcache_hit = 1'b1;
                store_vcache_idx = i;
            end
        end
    end

    //cam that wb buffer shi
    always_comb begin
        load_wb_hit = 1'b0;
        load_wb_idx = '0;
        store_wb_hit = 1'b0;
        store_wb_idx = '0;
        for (int i = 0; i < `WB_LINES; ++i) begin
            if (i < `WB_LINES - wb_spots) begin
                if(load_req_valid && wb_buffer[(wb_head + i) % `WB_LINES].addr.dw.addr == load_req_addr.dw.addr) begin
                    load_wb_hit = 1'b1;
                    load_wb_idx = wb_head + i;
                end
                if (store_req_valid && wb_buffer[(wb_head + i) % `WB_LINES].addr.dw.addr == store_req_addr.dw.addr) begin
                    store_wb_hit = 1'b1;
                    store_wb_idx = wb_head + i;
                end
            end
        end
    end

    // update next pointers
    always_comb begin
        next_wb_head = (wb_head + wb_mem_accepted) % `WB_LINES;
        next_wb_tail = (wb_tail + wb_allocated) % `WB_LINES;
        next_wb_spots = wb_spots + wb_mem_accepted - wb_allocated;

        next_mshr_head = (mshr_head + mem_data_returned) % `MSHR_SZ;
        next_mshr_tail = (mshr_tail + mshr_allocated) % `MSHR_SZ;
        next_mshr_true_head = (mshr_true_head + mshr_cache_accepted) % `MSHR_SZ;
        next_mshr_spots = mshr_spots + mshr_cache_accepted - mshr_allocated;
    end

    always_ff @(posedge clock) begin
        if (reset) begin
            wb_head <= '0;
            wb_tail <= '0;
            wb_spots <= `WB_LINES;
            wb_buffer <= '0;

            mshr_head <= '0;
            mshr_tail <= '0;
            mshr_true_head <= '0;
            mshr_spots <= `MSHR_SZ;
            mshrs <= '0;

            dcache_meta_data <= '0;
            vcache_meta_data <= '0;

        end else begin
            wb_head <= next_wb_head;
            wb_tail <= next_wb_tail;
            wb_spots <= next_wb_spots;
            wb_buffer <= next_wb_buffer;

            mshr_head <= next_mshr_head;
            mshr_tail <= next_mshr_tail;
            mshr_true_head <= next_mshr_true_head;
            mshr_spots <= next_mshr_spots;
            mshrs <= next_mshrs;

            dcache_meta_data <= next_dcache_meta_data;
            vcache_meta_data <= next_vcache_meta_data;
        end

        // $display("------------ DCACHE!!!!---------");
        // $display("mshr_true_head", mshr_true_head);
        // $display("mshr_head", mshr_head);
        // $display("mshr_tail", mshr_tail);
        // $display("mshr_spots", mshr_spots);
        // for (int i = 0; i < `MSHR_SZ; ++i) begin
        //     $display("mshrs[%d].valid: %b", i, mshrs[i].valid);
        // end

        // for (int i = 0; i < `MSHR_SZ; ++i) begin
        //     $display("mshrs[%d].dirty: %b", i, mshrs[i].dirty);
        // end

        // for (int i = 0; i < `MSHR_SZ; ++i) begin
        //     $display("mshrs[%d].mem_tag: %d", i, mshrs[i].mem_tag);
        // end

        // for (int i = 0; i < `MSHR_SZ; ++i) begin
        //     $display("mshrs[%d].addr: %h", i, mshrs[i].addr);
        // end

        // for (int i = 0; i < `MSHR_SZ; ++i) begin
        //     $display("mshrs[%d].data: %d", i, mshrs[i].data);
        // end

        // for (int i = 0; i < `MSHR_SZ; ++i) begin
        //     $display("mshrs[%d].byte_mask: %b", i, mshrs[i].byte_mask);
        // end

        // for (int i = 0; i < `VCACHE_LINES; ++i) begin
        //     $display("vcache_meta_data[%d].addr: %h", i, vcache_meta_data[i].addr);
        // end

        // for (int i = 0; i < `VCACHE_LINES; ++i) begin
        //     $display("vcache_mem.memData[%d]: %h", i, vcache_mem.memData[i]);
        // end

        // for (int i = 0; i < `WB_LINES; ++i) begin
        //     $display("wb_buffer[%d].addr: %h", i, wb_buffer[i].addr);
        // end

        // for (int i = 0; i < `WB_LINES; ++i) begin
        //     $display("wb_buffer[%d].data: %h", i, wb_buffer[i].data);
        // end

        // $display("wb_head: %d", wb_head);
        // $display("wb_tail: %d", wb_tail);

        // for (int i = 0; i < `DCACHE_NUM_SETS; ++i) begin
        //     for (int j = 0; j < `DCACHE_NUM_WAYS; ++j) begin
        //         $display("dcache_meta_data[%d][%d].addr: %h", i, j, dcache_meta_data[i][j].addr);
        //     end
        // end
        
        // for (int i = 0; i < `DCACHE_NUM_SETS; ++i) begin
        //     for (int j = 0; j < `DCACHE_NUM_WAYS; ++j) begin
        //         $display("dcache_meta_data[%d][%d].valid: %h", i, j, dcache_meta_data[i][j].valid);
        //     end
        // end

        // for (int i = 0; i < `DCACHE_LINES; ++i) begin
        //     $display("dcache_mem.memData[%d]: %h", i, dcache_mem.memData[i]);
        // end
    
        // $display("mshr_cache_accepted: %b", mshr_cache_accepted);
        // // if ((mshr_true_head != next_mshr_head) || mshr_full) && (!full_eviction || wb_mem_accepted) begin
        // //     $display("MSHR CACHE WRITE");
        // // end

        // $display("load_req_valid: %b", load_req_valid);
        // $display("load_req_addr: %h", load_req_addr);
        // $display("store_req_valid: %b", store_req_valid);
        // $display("store_req_addr: %h", store_req_addr);
        // $display("store_req_data: %h", store_req_data);
        // $display("store_req_byte_mask: %b", store_req_byte_mask);
        // $display("load_data_cache_packet.valid: %b", load_data_cache_packet.valid);
        // $display("load_data_cache_packet.data: %h", load_data_cache_packet.data);
        // $display("mshr_allocated: %b", mshr_allocated);
        // $display("store_miss: %b", store_miss);
        // $display("load_miss: %b", load_miss);
        // $display("store_vcache_hit: %b", store_vcache_hit);
        // $display("store_dcache_hit: %b", store_dcache_hit);
        // $display("load_vcache_hit: %b", load_vcache_hit);
        // $display("load_dcache_hit: %b", load_dcache_hit);
        // $display("load_vcache_idx: %d", load_vcache_idx);
        // $display("load_dcache_idx: %d", load_dcache_idx);
        // $display("store_mshr_hit: %b", store_mshr_hit);
        // $display("load_miss: %b", load_miss);
        // $display("mshr_full: %b", mshr_full);
        // $display("wb_spots: %d", wb_spots);
    end

`ifdef DEBUG
    assign debug_dcache_meta_data = dcache_meta_data;
    assign debug_vcache_meta_data = vcache_meta_data;
    assign debug_mshr_true_head   = mshr_true_head;
    assign debug_mshr_spots       = mshr_spots;
    assign debug_mshrs            = mshrs;
    assign debug_wb_head          = wb_head;
    assign debug_wb_spots         = wb_spots;
    assign debug_wb_buffer        = wb_buffer;
`endif

endmodule