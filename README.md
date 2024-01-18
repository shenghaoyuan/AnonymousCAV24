# End-to-end Mechanized Proof of a JIT-accelerated eBPF Virtual Machine for IoT

This repository contains the version of the verified JIT + HAVM presented in the CAV24 submission 1579.
  
## Installation
This repo relies on several existing projects
- Coq.8.13.2
- Our CompCert ARM Variant, see `compcert-arm-bin.zip`
- dx, from `https://gitlab.univ-lille.fr/samuel.hym/dx`
- ...

see INSTALL.md for how to install them.

Then to install this repo, only two commands
```shell
./configure --opamprefixdir=YOUR-OPAM-PRE-FIX --compcertdir=OUR-CompCert-Varaint-PATH
make all
```

## JIT Overview

JIT consists of:
- An analyzer to find all rBPF Alu lists from the input rBPF program `rbpf32/Analyzer.v`;
- A JIT_ALU Compiler that translates a list of rBPF Alu into ARM binary `jit/ThumbJIT.v`;
- A Combiner that calls the JIT_ALU compiler to jit all rBPF Alu lists found by the analyzer `jit/WholeCompiler.v`.

The high-level specifiation includes three modules for proof simplification, the low-level C implementation adopts a more-efficient way that combines all modules togethers (the C function `whole_compiler` in `jit/jitclight/rbpf_jit_compiler.c`): find an Alu, then jit it so that there are less intermediate results.

## HAVM Overview

HAVM consists of:
- a `jit_call` function uses ARM hardware directly to execute jited code.
- a 32-bit rBPF interpreter executes the rest rBPF Non-Alu instructions, with defensive semantics.

## Project Structure
- `compcert-arm-bin.zip`: our symbolic CompCert ARM interpreter `compcert/arm/ABinSem.v`
- `rbpf32/`: high-level specification: i.e. transition systems of rbpf32 `rbpf32/TS*.v`
- `jit/`: the JIT compiler `jit/ThumbJIT.v` + HAVM `jit/TSSemanticsB.v`
