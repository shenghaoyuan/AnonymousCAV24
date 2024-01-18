include makefile.config

BPF_LOW ?= 1

LLC ?= llc
COMPCERTBPF ?= $(COMPCERTBPFDIR)
CLANG ?= clang
CLANG_DUMP ?= llvm-objdump
COMM_FLAGS = -isystem `$(CLANG) -print-file-name=include`
CLANG_FLAGS = -Os -Wall -target bpf -emit-llvm $(COMM_FLAGS) \
	        -Wno-unused-value -Wno-pointer-sign -g3\
	        -Wno-compare-distinct-pointer-types \
	        -Wno-gnu-variable-sized-type-not-at-end \
	        -Wno-address-of-packed-member -Wno-tautological-compare \
	        -Wno-unknown-warning-option \
	        
ifeq (1, $(BPF_LOW))
CLANG_FLAGS += -m32
endif

.PHONY: ebpf2int64 ebpf2array

LLC_FLAGS = -march=bpf -mcpu=v2 -filetype=obj  
      
ifeq (1, $(BPF_LOW))
LLC_FLAGS += -mattr=alu32 
endif

BPF_COMPCERT ?= 1

TEST = add_reg fletcher32

ebpf2int64:
	$gcc $@.c -o $@

ebpf2array:
	$gcc $@.c -o $@

%: %.c
ifeq (1,$(BPF_COMPCERT))
	@echo "BPF_CompCert"
	make ebpf2int64 && make ebpf2array
	$(COMPCERTBPF) -o $@ $< \
	&& $(CLANG_DUMP) -S $@ > $@_objdump.txt \
	&& ./ebpf2int64 $@ $*_compcert_int64.txt \
	&& ./ebpf2array $@ $*_compcert_array.txt && rm $@
else
	@echo "BPF_LLVM"
	make ebpf2int64 && make ebpf2array
	$(CLANG) $(CLANG_FLAGS) -c $< -o $*.bc \
	&& $(LLC) $*.bc $(LLC_FLAGS) -o $*.o && rm $*.bc \
	&& $(CLANG_DUMP) -S $*.o > $@_objdump.txt \
	&& ./ebpf2int64 $*.o $*_llvm_int64.txt \
	&& ./ebpf2array $*.o $*_llvm_array.txt && rm $*.o
endif


