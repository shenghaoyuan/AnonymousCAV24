# Benchmarks C code

## Tools
- `ebpf2array`: compile ebpf bytecodes into an array (for rBPF benchmarks in C level)
- `ebpf2int64`: compile ebpf bytecodes into a list (for rBPF benchmarks in Coq level)
- `BPF_COMPCERT=1`: using CompCert rBPF32 backend
- `BPF_COMPCERT=0` + `BPF_LOW=1`: using LLVM-BPF + `alu32` backend
- `BPF_COMPCERT=0` + `BPF_LOW=0`: using LLVM-BPF backend (without `alu32`)

## benchmarks

- `*_no_ctx.c`: the original C implementation which doesn't satisfy the requirement of eBPF (input should be a pointer)

- `*.c`: the corresponding C implementation which satisfies the requirement of eBPF (input should be a pointer)

