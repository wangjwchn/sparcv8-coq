# sparc-coq
Formalizing SPARCv8 instruction set architecture in coq


## Installation
#### Coq8.6
Install Coq8.6 from [here](https://coq.inria.fr/news/134.html). 

## Description

| File name | Description |
| ------------- |:-------------:||Asm.v | Formalizing SPARCv8 ISA || Property.v |Properties and the proof || WinOverflow.v |Verification of the window overflow trap handler || Integers.v |Integer library (from CompCert) || Maps.v | Map libaray (from CompCert) || Coqlib.v |Coq basic library (from CompCert)| LibTactics.v |Some tactics in Coq (from Software Foundations)| IntAuto.v | Some tactics for integer library (From CertiC/OS-II verification project) || MathSol.v |Some tactics for integer library (From CertiC/OS-II verification project)| Makefile | - |