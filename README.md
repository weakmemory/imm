# Supplementary material for ``Bridging the Gap Between Programming Languages and Hardware Weak Memory Models'' paper

## Authors

Anton Podkopaev, Ori Lahav, Viktor Vafeiadis

## Paper draft on Arxiv

https://arxiv.org/abs/1807.07892


The repository contains Coq code, which describes a definition of Intermediate Memory Model (IMM) and
compilation correctness proofs stated in the paper.

## How to build the project
*Requirements*: OPAM 1.2, Make.

To build the project, one needs to install some libraries (`sflib`, `paco`, `promising-coq`, and `hahn`), which the project
depends on. This might be done by running `./configure`. After that, one needs to run `make`.

Alternatively, the project may be built and installed via OPAM:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam remote add coq-weakmemory-local -k git https://github.com/weakmemory/local-coq-opam-archive
opam install coq-imm
```

## File description
`src/basic`. Definitions and statements about programs and execution graphs.
- *Prog.v*---a definition of the program language.
- *Events.v*---definitions related to events.
- *Execution.v*, *Execution\_eco.v*---execution graphs.
- *ProgToExecution.v*---construction of execution graphs from sequential programs.
- *ProgToExecutionProperties.v*---properties of the construction.

`src/imm`. Definitions and statements about IMM (in the development, it is called *ph*)
and IMMs, a version of IMM with RC11-style definition of happens-before (HB), (in the development, it is called *ph\_s*).
- *CombRelations.v*, *CombRelationsMore.v*---definitions of relation VF and linked relations and their properties.
- *ph\_common\_more.v*, *ph\_common.v*---common definitions for both models.
- *ph\_hb.v*---a definition of HB for IMM.
- *ph\_s\_hb.v*---the RC11-style definition of HB for IMMs.
- *ph.v*---a definition of IMM.
- *ph\_s.v*---a definition of IMMs.
- *ph\_sToph.v*---a proof that IMMs is weaker than IMM.

`src/hardware`. Definitions of hardware models and proofs about them.
- *Power\_fences.v*,
  *Power\_ppo.v*,
  *Power.v*---a definition of POWER (Alglave-al:TOPLAS14).
- *Rel\_opt.v*---a correctness proof for release write transformation.
- *phToPower.v*---a compilation correctness proof from IMM to POWER.
- *Arm.v*---a definition of ARMv8.3 (Pulte-al:POPL18).
- *phToARM.v*---a compilation correctness proof from IMM to ARMv8.3.
- *TSO.v*---a definition of TSO (Alglave-al:TOPLAS14, Owens-al:TPHOLs09).
- *phToTSO.v*---a compilation correctness proof from IMM to TSO.

`src/rc11`. Definitions of hardware models and proofs about them.
- *RC11.v*---a definition of RC11 (Lahav-al:PLDI17).
- *RC11Toph\_s.v*---a compilation correctness proof from RC11 to IMMs.

`src/promiseToImm`. The compilation correctness from Promise to IMM.
- *Promise.v*---a definition of a Promise outcome.
- *SimTraversal.v*---traversal of IMM-consistent execution graphs.
- *TraversalConfig.v*, *Traversal.v*---a small traversal step of IMM-consistent execution graphs
    used to prove properties of the traversal.
- *SimTraversalProperties.v*---properties of the normal traversal.
- *SimulationRel.v*---a simulation relation.
- *SimulationPlainStep.v*--- a proof of simulation step.
- *PlainStepBasic.v*,
    *WritePlainStep.v*,
    *FencePlainStep.v*,
    *RMWPlainStep.v*,
    *ReadPlainStep.v*,
    *ReadPlainStepHelper.v*---auxiliary lemmas for the simulation step proof.
- *SubExecution.v*,
    *CertCOhelper.v*,
    *CertExecution1.v*,
    *CertExecution2.v*,
    *Receptiveness.v*, *CertExecutionMain.v*---construction of the certification graph and proofs of its properties.
- *PromiseFuture.v*--- a proof that it is enough to show certification
    only for a restricted set of future memories.
- *PromiseToPH.v*---a proof of the compilation correctness from Promise to IMM.

Auxiliary files:
- *AuxRel.v*,
*MaxValue.v*,
*Monotone.v*,
*Event\_ph\_promise.v*,
*SimStateHelper.v*,
*SimulationPlainStepAux.v*,
*SimulationRelAux.v*,
*TraversalConfigAlt.v*,
*TraversalCounting.v*,
*ViewRelHelpers.v*,
*ViewRel.v*,
*MemoryAux.v*.
