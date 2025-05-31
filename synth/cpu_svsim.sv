`ifndef SYNTHESIS

//
// This is an automatically generated file from 
// dc_shell Version V-2023.12-SP5 -- Jul 16, 2024
//

// For simulation only. Do not modify.

module cpu_svsim (
    input clock,     input reset, 
    
    input MEM_TAG   mem2proc_transaction_tag,     input MEM_BLOCK mem2proc_data,                input MEM_TAG   mem2proc_data_tag,        
    output MEM_COMMAND proc2mem_command,     output ADDR        proc2mem_addr,        output MEM_BLOCK   proc2mem_data,          

            output COMMIT_PACKET [2-1:0] committed_insts
    
             
    , output logic [32-1:0][$bits(MEM_BLOCK)-1:0] debug_mem_data_dcache,
    output logic [4-1:0][$bits(MEM_BLOCK)-1:0] debug_mem_data_vcache,
    output DCACHE_META_DATA [32 / 16-1:0] [16-1:0] debug_dcache_meta_data,
    output VCACHE_META_DATA                           [4-1:0] debug_vcache_meta_data, 
    output MSHR_IDX                                                       debug_mshr_true_head,
    output logic                             [$clog2(16+1)-1:0] debug_mshr_spots,
    output DCACHE_MSHR_ENTRY                               [16-1:0] debug_mshrs,
    output WB_IDX                                                         debug_wb_head,
    output logic                               [$clog2(4+1)-1:0] debug_wb_spots,
    output WB_ENTRY                                       [4-1:0] debug_wb_buffer,
    output SQ_POINTER                                                     debug_sq_true_head, 
    output SQ_POINTER                                                     debug_sq_head,
    output logic                               [$clog2(8 + 1)-1:0] debug_store_buffer_entries,
    output STORE_QUEUE_PACKET                                [8-1:0] debug_store_queue


);

    
    

    

  cpu cpu( {>>{ clock }}, {>>{ reset }}, {>>{ mem2proc_transaction_tag }}, 
        {>>{ mem2proc_data }}, {>>{ mem2proc_data_tag }}, 
        {>>{ proc2mem_command }}, {>>{ proc2mem_addr }}, {>>{ proc2mem_data }}, 
        {>>{ committed_insts }}, {>>{ debug_mem_data_dcache }}, 
        {>>{ debug_mem_data_vcache }}, {>>{ debug_dcache_meta_data }}, 
        {>>{ debug_vcache_meta_data }}, {>>{ debug_mshr_true_head }}, 
        {>>{ debug_mshr_spots }}, {>>{ debug_mshrs }}, {>>{ debug_wb_head }}, 
        {>>{ debug_wb_spots }}, {>>{ debug_wb_buffer }}, 
        {>>{ debug_sq_true_head }}, {>>{ debug_sq_head }}, 
        {>>{ debug_store_buffer_entries }}, {>>{ debug_store_queue }} );
endmodule
`endif
