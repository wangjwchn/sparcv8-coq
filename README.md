# sparc-coq
Formalizing SPARCv8 instruction set architecture in coq


### Requirements
 - [Coq8.6.1](https://coq.inria.fr/coq-86)
 - [coq2smt](https://github.com/wangjwchn/coq2smt)


### Installation
```bash
git clone https://github.com/wangjwchn/sparcv8-coq.git
cd sparcv8-coq
make
```

### Description

| File name | Description |
| ------------- |:-------------:|
|Asm.v | The Formal Model of SPARCv8 ISA |
| Property.v | Properties |
| WinOverflow.v | Verifying the window overflow trap handler |
| WinUnderflow.v | Verifying the window underflow trap handler |
| Maps.v | Map library (From CompCert) |
| LibTactics.v |Some tactics (From Software Foundations) |
| IntAuto.v | Some tactics for integer library (From CertiC/OS-II verification project) |
| MathSol.v |Some tactics for integer library (From CertiC/OS-II verification project)
| Makefile | - |
