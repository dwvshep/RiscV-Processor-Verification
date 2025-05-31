/*
 *  pipe_print.c - Print instructions as they pass through the verisimple
 *                 pipeline.  Must compile with the '+vc' vcs flag.
 *
 *  Doug MacKay <dmackay@umich.edu> Fall 2003
 *
 *  Updated for RISC-V by C Jones, Winter 2019
 *
 *  Updated to take an arbitrary file by Ian W, Winter 2023
 *
 *  Output format improved by Ian in Winter 2024
 */

#include <stdio.h>

// NOTE: 'decode_inst()' is made available by the Makefile including it on
// the commandline. including it manually here doesn't seem to work, even
// with include guards.

static FILE* ppfile = NULL;

void open_pipeline_output_file(char* file_name)
{
    ppfile = fopen(file_name, "w");
}

void close_pipeline_output_file()
{
    fprintf(ppfile, "\n");
    fclose(ppfile);
    ppfile = NULL;
}

void print_header()
{
    fprintf(ppfile, "Cycle |     IF      |     ID      |     EX      |     MEM     |     WB      |    Reg WB    | MEM Bus");
}

void print_cycles(int clock_count)
{
    fprintf(ppfile, "\n%5d ", clock_count);
}

void print_stage(int inst, int npc, int valid_inst)
{
    if (!valid_inst)
        fprintf(ppfile, "|%4s:%-8s", "-", "-");
    else
        fprintf(ppfile, "|%4X:%-8s", npc, decode_inst(inst));
}

void print_reg(int wb_data, int wb_idx, int wb_valid)
{
    if (wb_valid && wb_idx != 0)
        fprintf(ppfile, "| r%02d=%-8X ", wb_idx, wb_data);
    else
        fprintf(ppfile, "|              ");
}

void print_membus(int proc2mem_command, int proc2mem_addr,
                  int proc2mem_data_hi, int proc2mem_data_lo)
{
    if (proc2mem_command == 1)
        fprintf(ppfile, "| LOAD  [%X]", proc2mem_addr);
    else if (proc2mem_command == 2)
        fprintf(ppfile, "| STORE [%X] = %X", proc2mem_addr, proc2mem_data_lo);
    else
        fprintf(ppfile, "|"); // this doesn't actually happen in p3 :/
}
