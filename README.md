# Intermediate Memory Model (IMM) and compilation correctness proofs for it

This repository contains Coq code supplementing the paper *Bridging the Gap Between Programming Languages and Hardware Weak Memory Models*
([arXiv](https://arxiv.org/abs/1807.07892)) by Anton Podkopaev, Ori Lahav, and Viktor Vafeiadis.

## Building the Project

### Requirements
* [Coq 8.8](https://coq.inria.fr)
* [Hahn library](https://github.com/vafeiadis/hahn)(`coq-hahn`)
* [The Coq development of A Promising Semantics for Relaxed-Memory Concurrency](https://github.com/anlun/promising-coq/tree/opam_red)(`coq-promising`)

### Building Manually

To build the project, one needs to install some libraries (`sflib`, `paco`, `promising-coq`, and `hahn`), which the project
depends on. This might be done by running `./configure`.
The command installs `Coq` as well. After that, one needs to run `make` (or `make -j4` for a faster build).

### Installation via OPAM
The project may be built and installed via OPAM:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam remote add coq-weakmemory-local -k git https://github.com/weakmemory/local-coq-opam-archive
opam install coq-imm
```

### Building in virtual machine
Download a [VirtualBox image](http://podkopaev.net/popl19-imm-artifact).
The login is `popl19` and the password is `popl`.

### Building in a Docker container
First, one needs to build a Docker image with the project and its dependencies
```bash
sudo docker build -t weakmemory/imm .
```
or to pull it from Docker Hub
```bash
docker pull weakmemory/imm
```
After that, one has to connect to the container

```bash
docker run -it weakmemory/imm /bin/bash
```
run
```bash
eval `opam config env`
```
to update container's environment variables and run
```bash
cd imm
make clean; make -j4
```
to build the project.

## File description
`src/basic`. Definitions and statements about programs and execution graphs.
- *Prog.v*—a definition of the program language.
- *Events.v*—definitions related to events.
- *Execution.v*, *Execution\_eco.v*—execution graphs.
- *ProgToExecution.v*—construction of execution graphs from sequential programs.
- *ProgToExecutionProperties.v*—properties of the construction.

`src/imm`. Definitions and statements about IMM
and IMMs, a version of IMM with RC11-style definition of happens-before (HB).
- *CombRelations.v*, *CombRelationsMore.v*—definitions of relation VF and linked relations and their properties.
- *imm\_common\_more.v*, *imm\_common.v*—common definitions for both models.
- *imm\_hb.v*—a definition of HB for IMM.
- *imm\_s\_hb.v*—the RC11-style definition of HB for IMMs.
- *imm.v*—a definition of IMM.
- *imm\_s.v*—a definition of IMMs.
- *imm\_sToimm.v*—a proof that IMMs is weaker than IMM.

`src/hardware`. Definitions of hardware models and proofs about them.
- *Power\_fences.v*,
  *Power\_ppo.v*,
  *Power.v*—a definition of POWER (Alglave-al:TOPLAS14).
- *Rel\_opt.v*—a correctness proof for release write transformation.
- *immToPower.v*—a compilation correctness proof from IMM to POWER.
- *Arm.v*—a definition of ARMv8.3 (Pulte-al:POPL18).
- *immToARM.v*—a compilation correctness proof from IMM to ARMv8.3.
- *TSO.v*—a definition of TSO (Alglave-al:TOPLAS14, Owens-al:TPHOLs09).
- *immToTSO.v*—a compilation correctness proof from IMM to TSO.

`src/c11`. Definition of C11 model w/o SC and NA accesses and a compilation correctness proof from it to IMM.
- *C11.v*—a definition of C11 (Batty-al:POPL11).
- *C11Toimm\_s.v*—a compilation correctness proof from C11 to IMMs.

`src/rc11`. Definition of RC11 model w/o SC and NA accesses and a compilation correctness proof from it to IMM.
- *RC11.v*—a definition of RC11 (Lahav-al:PLDI17).
- *RC11Toimm\_s.v*—a compilation correctness proof from RC11 to IMMs.

`src/promiseToImm`. The compilation correctness from Promise to IMM.
- *Promise.v*—a definition of a Promise outcome.
- *SimTraversal.v*—traversal of IMM-consistent execution graphs.
- *TraversalConfig.v*, *Traversal.v*—a small traversal step of IMM-consistent execution graphs
    used to prove properties of the traversal.
- *SimTraversalProperties.v*—properties of the normal traversal.
- *SimulationRel.v*—a simulation relation.
- *SimulationPlainStep.v*— a proof of simulation step.
- *PlainStepBasic.v*,
    *WritePlainStep.v*,
    *FencePlainStep.v*,
    *RMWPlainStep.v*,
    *ReadPlainStep.v*,
    *ReadPlainStepHelper.v*—auxiliary lemmas for the simulation step proof.
- *SubExecution.v*,
    *CertCOhelper.v*,
    *CertExecution1.v*,
    *CertExecution2.v*,
    *Receptiveness.v*, *CertExecutionMain.v*—construction of the certification graph and proofs of its properties.
- *PromiseFuture.v*— a proof that it is enough to show certification
    only for a restricted set of future memories.
- *PromiseToIMM.v*—a proof of the compilation correctness from Promise to IMM.

Auxiliary files:
- *AuxRel.v*,
*MaxValue.v*,
*Monotone.v*,
*Event\_imm\_promise.v*,
*SimStateHelper.v*,
*SimulationPlainStepAux.v*,
*SimulationRelAux.v*,
*TraversalConfigAlt.v*,
*TraversalCounting.v*,
*ViewRelHelpers.v*,
*ViewRel.v*,
*MemoryAux.v*.
