# Coq extraction debug

```shell
make target # where target.ml is extracted
```

# print.ml
It defines some useful printing functions

# fletcher32InterpreterSimulator.ml
This extracted file is used to simulate the fletcher32 algorithm (using **LLVM BPF-backend** to translate into BPF binary) executed by the CertrBPF interpreter.
1. It is extracted by `fletcher32InterpreterSimulator.v`
2. It removes some errored extracted code
3. It adds several printing functions from `print.ml`

# fletcher32InterpreterSimulatorCompCert.ml
This extracted file is used to simulate the fletcher32 algorithm (using **CompCert BPF-backend** to translate into **32** -BPF binary) executed by the CertrBPF interpreter.
1. It is extracted by `fletcher32InterpreterSimulatorCompCert.v`
2. It removes some errored extracted code
3. It adds several printing functions from `print.ml`
