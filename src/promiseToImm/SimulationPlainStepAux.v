Require Import Classical Peano_dec.
From hahn Require Import Hahn.
From promising Require Import Basic DenseOrder
     TView View Time Event Cell Thread Language Memory Configuration.

Require Import Events Execution.
Require Import PArith.
Require Import AuxRel.
Require Import Setoid.
Require Import MaxValue ViewRel.
Require Import SimulationRel.
Require Import Promise.

Lemma rtc_lang_tau_step_rtc_thread_tau_step
      thread st1 st2 lc sc mem
      (STEP: rtc (Language.step (thread_lts thread) ProgramEvent.silent) st1 st2):
  rtc (@Thread.tau_step (thread_lts thread))
      (Thread.mk (thread_lts thread) st1 lc sc mem)
      (Thread.mk (thread_lts thread) st2 lc sc mem).
Proof.
  induction STEP.
  { econs 1. }
  econs 2; eauto. econs.
  { econs. econs 2. econs; [|econs 1]; eauto. }
  simpls.
Qed.

Lemma sim_state_other_thread_step G
      (C C' : actid -> Prop) smode thread (state : Language.state (thread_lts thread))
      (CINCL : C ⊆₁ C')
      (COVSTEP : forall a, tid a = thread -> C' a -> C a)
      (SIMSTATE: sim_state G smode C state) :
  sim_state G smode C' state.
Proof.
  cdes SIMSTATE.
  red. splits; eauto.
  ins. split; ins.
  { apply PCOV. apply COVSTEP; eauto. }
  apply CINCL. by apply PCOV.
Qed.