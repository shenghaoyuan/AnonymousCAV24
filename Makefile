include Makefile.config

SED := sed
CAT := cat
AWK := awk
COQC := coqc
#COQDEP := coqdep
OCAMLOPT := ocamlopt
COQMAKEFILE := coq_makefile
CP := cp
MV := mv
HEADACHE := headache

CC=gcc
ARMCC=arm-none-eabi-gcc
ARMDUMP=arm-none-eabi-objdump
ARMFLAGS=-mcpu=cortex-m4 -mfpu=fpv4-sp-d16
OFLAGS=-Os
CLIGHTGEN=clightgen
CLIGHTGEN32=$(CLIGHTGEN32DIR)/clightgen

THIS_FILE := $(lastword $(MAKEFILE_LIST))

COQEXTRAFLAGS := COQEXTRAFLAGS = '-w all,-extraction,-disj-pattern-notation'

OCAMLINCS := -I extr # -I src

DIRS := comm dxcomm model dxmodel monadicmodel rbpf32 jit clightlogic

COQINCLUDES := INSTALLDEFAULTROOT = comm "\n"
COQINCLUDES += $(foreach d, $(DIRS),-R $(d) bpf.$(d) "\n")
COQINCLUDES +=-R $(COMPCERTDIR) compcert

COQDEP="$(COQBIN)coqdep" -exclude-dir aarch64 -exclude-dir x86_64 -exclude-dir riscV -exclude-dir powerpc -exclude-dir x86_32 $(COQINCLUDES)

all:
	@echo $@
	@$(MAKE) comm
	@$(MAKE) dxcomm
	@$(MAKE) monadicmodel
	@$(MAKE) clightlogic
	@$(MAKE) compcertinfo
	@$(MAKE) compile
	@$(MAKE) rbpf32
	@$(MAKE) dxjit
	@$(MAKE) jit-clight
	@$(MAKE) dxhavm
	@$(MAKE) havm-clight
	@$(MAKE) jit
	@$(MAKE) simulation
	@$(MAKE) document
   
COMM= Flag.v LemmaNat.v LemmaInt.v ListAsArray.v rBPFNat.v rBPFAST.v rBPFMemType.v rBPFValues.v MemRegion.v Regs.v BinrBPF.v \
   JITCall.v State.v Monad.v rBPFMonadOp.v
   
DXCOMM= InfComp.v GenMatchable.v \
   CoqIntegers.v DxIntegers.v DxValues.v DxListAsArray.v DxBinrBPF.v DxNat.v
   
MODEL= Syntax.v Decode.v Semantics.v SemanticsSimpl.v SemanticsJIT.v SemanticsJITSimpl.v Encode.v PrintrBPF.v

MONADIC= Opcode.v
   
   
DXMODEL= DxAST.v DxFlag.v IdentDef.v DxMemType.v DxMemRegion.v DxRegs.v \
    DxState.v DxMonad.v DxOpcode.v

CLIGHTLOGIC= clight_exec.v Clightlogic.v \
    CommonLib.v CommonLemma.v CorrectRel.v CommonLemmaNat.v

MODELTS= TSSyntax.v JITConfig.v TSPrint.v TSDecode.v TSSemantics.v \
    TSSemanticsA.v Analyzer.v TSSemanticsAproof.v \
    TSSemanticsJIT.v BState.v BSemanticsSimpl.v BStateMonadOp.v BSemanticsMonadic.v BSemanticsSimplproof.v

DXJIT= ../ListSetRefinement.v ../ThumbInsOp.v ../KeyValue2.v \
    JITState.v JITMonadOp.v JITIdDef.v DxKeyValue2.v \
    DxListSetRefinement.v DxJITMonadState.v DxThumbInsOp.v \
    ThumbJITOpcode.v DxThumbJITOpcode.v JITNat.v DxJITNat.v \
    DxMonadCommon.v DxThumbJIT.v \
    JITTests.v JITTestMain.v JITExtrMain.v

DXHAVM= HAVMState.v HAVMMonadOp.v DxHAVMInterpreter.v \
    HAVMIdDef.v DxHAVMState.v HAVMTests.v HAVMTestMain.v HAVMExtrMain.v

JIT= PrintThumb.v ABMemory.v BitfieldLemma.v \
    Arm32Reg.v ThumbDecode.v ThumbJITLtac.v ThumbJITProofLemma0.v \
    ListSetSort.v ThumbJIT.v WholeCompiler.v \
    ThumbDecodeEncodeALU.v ThumbDecodeEncodeALU0.v ThumbDecodeEncodeMEM.v \
    TSSemanticsB.v TSSemanticsBproofdef.v \
    TSSemanticsBproof6.v TSSemanticsBproofAux.v \
    TSSemanticsBproof.v \
    PrintJIT.v \
    WholeCompilerGeneric.v WholeCompiler1.v WholeCompiler2.v \
    ThumbJIT1.v ThumbJIT2.v ThumbJIT1proof.v WholeCompiler3.v WholeCompiler4.v \
    TSSemanticsBequiv.v

#TSSemanticsBproof0.v TSSemanticsBproof1.v TSSemanticsBproof2.v TSSemanticsBproof3.v TSSemanticsBproof4.v TSSemanticsBproof5.v TSSemanticsBproof6.v TSSemanticsBproof7.v TSSemanticsBproof8.v TSSemanticsBproof9.v TSSemanticsBproof10.v TSSemanticsBproof11.v TSSemanticsBproof12.v TSSemanticsBproof13.v TSSemanticsBproof14.v TSSemanticsBproof15.v TSSemanticsBproof16.v TSSemanticsBproof17.v \
#TSSemanticsBproofAux.v TSSemanticsBproof6.v \

SIMULATION= MatchStateComm.v HAVMMatchState.v InterpreterRel.v \
    correct_check_pc.v correct_upd_pc.v correct_check_pc_incr.v correct_eval_reg.v correct_upd_reg.v correct_eval_flag.v correct_upd_flag.v \
    correct_eval_mrs_num.v correct_eval_mrs_regions.v correct_load_mem.v correct_store_mem.v \
    correct_eval_ins.v correct_cmp_ptr32_nullM.v correct_get_dst.v correct_get_src.v correct_get_mem_region.v \
    correct__bpf_get_call.v correct_exec_function.v  \
    correct_get_offset.v #correct_get_immediate.v correct_get_src32.v \
    #correct_get_opcode_ins.v correct_get_opcode_alu32.v correct_get_opcode_branch.v \
    #correct_get_opcode_mem_ld_reg.v correct_get_opcode_mem_st_imm.v correct_get_opcode_mem_st_reg.v correct_get_opcode_nat.v \
    #correct_get_add.v correct_get_sub.v correct_get_addr_ofs.v correct_get_start_addr.v correct_get_block_size.v correct_get_block_perm.v \
    #correct_check_mem_aux2.v correct_check_mem_aux.v correct_check_mem.v \
    #correct_step_opcode_alu32.v correct_step_opcode_branch.v \
    #correct_step_opcode_mem_ld_reg.v correct_step_opcode_mem_st_reg.v correct_step_opcode_mem_st_imm.v \
    #correct_step.v correct_bpf_interpreter_aux.v correct_bpf_interpreter.v

# correct_jit_call.v
COQCOMM = $(addprefix comm/, $(COMM))
COQDXCOMM = $(addprefix dxcomm/, $(DXCOMM))
COQMODEL =  $(addprefix model/, $(MODEL))
COQDXMODEL =  $(addprefix dxmodel/, $(DXMODEL))
COQEMONADIC =  $(addprefix monadicmodel/, $(MONADIC))
COQMODELTS =  $(addprefix rbpf32/, $(MODELTS))
COQDXJIT = $(addprefix jit/jitcompiler/, $(DXJIT))
COQDXHAVM = $(addprefix jit/havm/, $(DXHAVM))
COQJIT = $(addprefix jit/, $(JIT))
CLIGHTLOGICDIR =  $(addprefix clightlogic/, $(CLIGHTLOGIC))
COQSIMULATION = $(addprefix jit/simulation/, $(SIMULATION))

FILES= $(COQCOMM) $(COQDXCOMM) $(COQMODEL) $(COQJIT) $(COQDXMODEL) $(COQEMONADIC) $(CLIGHTLOGICDIR)

depend: $(FILES)
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend

comm:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQCOMM) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

dxcomm:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQDXCOMM) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

model:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQMODEL) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

monadicmodel:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQEMONADIC) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

compcertinfo:
	@echo $@
	$(COMPCERTSRCDIR)/tools/modorder $(COMPCERTSRCDIR)/.depend.extr cfrontend/PrintCsyntax.cmx | \
	    $(AWK) '{ delete paths ;                                                                 \
	              for(i = 1; i <= NF; i++) {                                                     \
	                 x = $$i ;                                                                   \
	                 sub("/[^/]*$$", "", x) ;                                                    \
	                 paths[x] = 1 ;                                                              \
	              }                                                                              \
	              for(p in paths) {                                                              \
	                 print "-I" ;                                                                \
	                 print "$(COMPCERTSRCDIR)/" p ;                                              \
	              }                                                                              \
	            }' > compcertsrc-I	
	$(COMPCERTSRCDIR)/tools/modorder $(COMPCERTSRCDIR)/.depend.extr cfrontend/PrintCsyntax.cmx | \
	    $(AWK) 'BEGIN { RS=" " } /cmx/ { gsub(".*/","") ; print }' > compcertcprinter-cmx-args
	$(OCAMLOPT) -args compcertsrc-I -a -args compcertcprinter-cmx-args -o compcertcprinter.cmxa
	$(OCAMLOPT) -args compcertsrc-I -a -args compcertcprinter-cmx-args -o compcertcprinter.a

compile:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQDXMODEL) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile
	
clightlogic:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(CLIGHTLOGICDIR) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile
	
rbpf32:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQMODELTS) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile
	
dxjit:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQDXJIT) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile
	$(CP) JITTestMain.ml jit/jitcompiler
	$(CP) JITTestMain.mli jit/jitcompiler
	$(OCAMLOPT) -args $(DXDIR)/cprinter-inc-args -I jit/jitcompiler jit/jitcompiler/JITTestMain.mli	
	$(OCAMLOPT) -args $(DXDIR)/cprinter-inc-args -I jit/jitcompiler -c jit/jitcompiler/JITTestMain.ml
	$(OCAMLOPT) -args compcertsrc-I str.cmxa unix.cmxa compcertcprinter.cmxa $(DXDIR)/ResultMonad.cmx $(DXDIR)/DXModule.cmx $(DXDIR)/DumpAsC.cmx jit/jitcompiler/JITTestMain.cmx -o jit/jitcompiler/main
	ln -sf $(COMPCERTSRCDIR)/compcert.ini jit/jitcompiler/compcert.ini
	cd jit/jitcompiler && ./main
	$(MV) jit/jitcompiler/jit_generated.c jit/jitcompiler/repatch
	cd jit/jitcompiler/repatch \
	&& $(CC) -o repatch1 ../../../repatch/repatch1.c && ./repatch1 jit_generated.c generated_repatch1.c && rm jit_generated.c repatch1 \
	&& $(CC) -o repatch2 repatch2.c && ./repatch2 generated_repatch1.c generated_repatch2.c && rm generated_repatch1.c repatch2 \
	&& $(CC) -o repatch3 ../../../repatch/repatch3.c && ./repatch3 generated_repatch2.c generated_repatch3.c && rm generated_repatch2.c repatch3 \
	&& $(CC) -o repatch4 ../../../repatch/repatch4.c && ./repatch4 rbpf_jit_compiler_pre.c generated_repatch3.c rbpf_jit_compiler.c && rm generated_repatch3.c repatch4
	$(MV) jit/jitcompiler/repatch/rbpf_jit_compiler.c jit/jitclight

jit-clight:
	@echo $@
	#cd jit/clight \
	#&& $(ARMCC) -o $@ $(OFLAGS) $(ARMFLAGS) fletcher32_ibpf_test.c ibpf_interpreter.c && ./$@ \
	cd jit/jitclight && $(CLIGHTGEN32) rbpf_jit_compiler.c
	$(COQMAKEFILE) -f _CoqProject jit/jitclight/rbpf_jit_compiler.v $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile
	
dxhavm:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQDXHAVM) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile
	$(CP) HAVMTestMain.ml jit/havm
	$(CP) HAVMTestMain.mli jit/havm
	$(OCAMLOPT) -args $(DXDIR)/cprinter-inc-args -I jit/havm jit/havm/HAVMTestMain.mli	
	$(OCAMLOPT) -args $(DXDIR)/cprinter-inc-args -I jit/havm -c jit/havm/HAVMTestMain.ml
	$(OCAMLOPT) -args compcertsrc-I str.cmxa unix.cmxa compcertcprinter.cmxa $(DXDIR)/ResultMonad.cmx $(DXDIR)/DXModule.cmx $(DXDIR)/DumpAsC.cmx jit/havm/HAVMTestMain.cmx -o jit/havm/main
	ln -sf $(COMPCERTSRCDIR)/compcert.ini jit/havm/compcert.ini
	cd jit/havm && ./main
	$(MV) jit/havm/havm_generated.c jit/havm/repatch
	cd jit/havm/repatch \
	&& $(CC) -o repatch1 ../../../repatch/repatch1.c && ./repatch1 havm_generated.c generated_repatch1.c && rm havm_generated.c repatch1 \
	&& $(CC) -o repatch2 repatch2.c && ./repatch2 generated_repatch1.c generated_repatch2.c && rm generated_repatch1.c repatch2 \
	&& $(CC) -o repatch3 ../../../repatch/repatch3.c && ./repatch3 generated_repatch2.c generated_repatch3.c && rm generated_repatch2.c repatch3 \
	&& $(CC) -o repatch4 ../../../repatch/repatch4.c && ./repatch4 havm_interpreter_pre.c generated_repatch3.c havm_interpreter_ef.c && ./repatch4 havm_interpreter_pre_builtin.c generated_repatch3.c havm_interpreter.c && rm generated_repatch3.c repatch4
	$(MV) jit/havm/repatch/havm_interpreter.c jit/jitclight && $(MV) jit/havm/repatch/havm_interpreter_ef.c jit/jitclight

havm-clight:
	@echo $@
	#cd jit/clight \
	#&& $(ARMCC) -o $@ $(OFLAGS) $(ARMFLAGS) fletcher32_ibpf_test.c ibpf_interpreter.c && ./$@ \
	cd jit/jitclight && $(CLIGHTGEN32) havm_interpreter.c
	$(COQMAKEFILE) -f _CoqProject jit/jitclight/havm_interpreter.v $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile
	
jit:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQJIT) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

simulation:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQSIMULATION) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

DOCFLAG := -external https://compcert.org/doc/html compcert -base bpf -short-names 
document:
	@echo $@
	mkdir -p html
	mkdir -p html/glob
	cp comm/*.glob html/glob
	#cp model/*.glob html/glob
	cp rbpf32/*.glob html/glob
	cp jit/*.glob html/glob
	coq2html $(DOCFLAG) -d html html/glob/*.glob comm/*.v
	#coq2html $(DOCFLAG) -d html html/glob/*.glob model/*.v
	coq2html $(DOCFLAG) -d html html/glob/*.glob rbpf32/*.v
	coq2html $(DOCFLAG) -d html html/glob/*.glob jit/*.v

CoqProject:
	@echo $(COQINCLUDES) > _CoqProject

addheadache:
	@echo $@
	$(HEADACHE) -c head_config -h head \
	rbpf32/*.v jit/*.v

clean :
	@echo $@
	make -f CoqMakefile clean
	find . -name "*\.vo" -exec rm {} \;
	find . -name "*\.vok" -exec rm {} \;
	find . -name "*\.vos" -exec rm {} \;
	find . -name "*\.glob" -exec rm {} \;
	find . -name "*\.aux" -exec rm {} \;
	find . -name "*\.cmi" -exec rm {} \;
	find . -name "*\.cmx" -exec rm {} \;
	find . -name "*\.crashcoqide" -exec rm {} \;

.SECONDARY:

.PHONY: all comm dxcomm model monadicmodel compcertinfo compile rbpf32 dxjit jit-clight dxhavm havm-clight jit clightlogic simulation document CoqProject addheadache clean
