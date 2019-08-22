From hahn Require Import Hahn.
Require Import PromisingLib.

Require Import Events Execution.
Require Import ProgToExecution.
Require Import ProgToExecutionProperties.
Require Import PromiseLTS.

Set Implicit Arguments.

Inductive sim_mode := sim_normal | sim_certification.
  
Definition sim_state_helper G smode thread
           (state state' : Language.state (thread_lts thread)) : Prop :=
  ⟪ STEPS : (step thread)＊ state state' ⟫ /\
  ⟪ TERMINAL : smode = sim_normal -> is_terminal state' ⟫ /\
  ⟪ TEH  : thread_restricted_execution G thread state'.(ProgToExecution.G) ⟫.

Definition sim_state G smode (C : actid -> Prop) thread
           (state : Language.state (thread_lts thread)) : Prop :=
  ⟪ PCOV : forall index , C (ThreadEvent thread index) <-> index < state.(eindex)⟫ /\
  exists state', sim_state_helper G smode state state'.

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

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Lemma sim_state_set_tid_eq G mode thread s s' state
      (EQ : s ∩₁ Tid_ thread ≡₁ s' ∩₁ Tid_ thread):
  @sim_state G mode s thread state <->
  @sim_state G mode s' thread state.
Proof.
  split; intros AA. 
  all: red; splits; [|by apply AA].
  all: ins; split; intros BB.
  1,3: by apply AA; apply EQ.
  all: by apply EQ; split; auto; apply AA.
Qed.

Lemma sim_state_set_eq G mode thread s s' state
      (EQ : s ≡₁ s'):
  @sim_state G mode s thread state <->
  @sim_state G mode s' thread state.
Proof. apply sim_state_set_tid_eq. by rewrite EQ. Qed.
