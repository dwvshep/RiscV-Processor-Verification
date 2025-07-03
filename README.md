# Risc-V Processor Design and UVM Verification

This repository contains the full RTL design and verification environment for an R10K-style, out-of-order, synthesizable RISC-V processor core, implemented in SystemVerilog with several components verified using the UVM (Universal Verification Methodology) framework.

---

## Project Overview

This project targets the implementation of a 32-bit RISC-V processor core (RV32I), including:

- Superscalar, out-of-order execution pipeline
- Support for base integer instructions (RV32I)
- Non-Blocking Instruction and Data Caches
- Reservation Station and Reorder Buffer (ROB) for out-of-order instruction dispatching
- AXI4-lite or simple memory interface for instruction/data memory

### Key Features

- **SystemVerilog RTL Design** — modular, synthesizable components
- **UVM Testbench** — built for scalable verification
- **Coverage-Driven Verification (CDV)** using Synopsys VCS
- **Assertion-Based Verification** for formal and dynamic checking
- **Golden Model Scoreboarding** RISC-V reference pipeline used for program level scoreboarding
- **Line, toggle, and functional coverage reports**

---

## Verification Highlights

- **Common Computational Benchmarks for Instruction-level testing**
- **Constrained random sequences for ROB and RS Verification**
- **Functional coverage models** tracking opcode groups, stalls, hazards
- **Scoreboard** that compares DUT output with ISA reference
- **Line and toggle coverage** via `-cm line+tgl` in Synopsys VCS

---

## Tools Used

- **Synopsys VCS** for simulation and coverage (`-cm line+cond+tgl+fsm+branch`)
- **UVM 1.2** (compatible with VCS)
- **Python/Verilog-Perl** (optional) for trace generation and log checking
- **VaporView** for waveform viewing (VCD)