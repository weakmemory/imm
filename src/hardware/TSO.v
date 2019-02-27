(******************************************************************************)
(** * Definition of the x86-TSO memory model *)
(******************************************************************************)
From hahn Require Import Hahn.
Require Import AuxRel.
Require Import Events Execution Execution_eco.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section TSO.

Variable G : execution.

Notation "'E'" := G.(acts_set).
Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'deps'" := G.(deps).
Notation "'fre'" := G.(fre).
Notation "'rfe'" := G.(rfe).
Notation "'coe'" := G.(coe).
Notation "'rfi'" := G.(rfi).
Notation "'fri'" := G.(fri).
Notation "'fr'" := G.(fr).
Notation "'eco'" := G.(eco).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'MFENCE'" := (F ∩₁ (fun a => is_true (is_sc lab a))).

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

Definition ppo := (⦗RW⦘ ⨾ sb ⨾ ⦗RW⦘) \ (fun x y => W x /\ R y).

Definition fence := ⦗RW⦘ ⨾ sb ⨾ ⦗MFENCE⦘ ⨾ sb ⨾ ⦗RW⦘.

Definition implied_fence := ⦗W⦘ ⨾ sb ⨾ ⦗dom_rel rmw⦘ ∪ ⦗codom_rel rmw⦘ ⨾ sb ⨾ ⦗R⦘.

Definition hb := ppo ∪ fence ∪ implied_fence ∪ rfe ∪ co ∪ fr.

(******************************************************************************)
(** ** Consistency *)
(******************************************************************************)

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.
Implicit Type ATOM : rmw_atomicity G.
Implicit Type SC_PER_LOC : sc_per_loc G.

Definition TSOConsistent :=
  ⟪ WF : Wf G ⟫ /\
  ⟪ COMP : complete G ⟫ /\
  ⟪ SC_PER_LOC: sc_per_loc G ⟫ /\
  ⟪ ATOMICITY : rmw_atomicity G ⟫ /\
  ⟪ GHB : acyclic hb ⟫.

Implicit Type CON : TSOConsistent.

Lemma CON_WF CON : Wf G.
Proof. apply CON. Qed.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_ppoE WF: ppo ≡ ⦗E⦘ ⨾ ppo ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold ppo.
rewrite (@wf_sbE G) at 1.
basic_solver 42.
Qed.

Lemma wf_fenceE WF: fence ≡ ⦗E⦘ ⨾ fence ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold fence.
rewrite (@wf_sbE G) at 1 2.
basic_solver 42.
Qed.

Lemma wf_implied_fenceE WF: implied_fence ≡ ⦗E⦘ ⨾ implied_fence ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold implied_fence.
rewrite (@wf_sbE G) at 1 2.
basic_solver 42.
Qed.

(******************************************************************************)
(** ** Domains and codomains *)
(******************************************************************************)

Lemma wf_hbD WF : hb ≡ ⦗RW⦘ ⨾ hb ⨾ ⦗RW⦘.
Proof.
split; [|basic_solver].
apply dom_helper_3.
unfold hb.
unfold ppo, fence, implied_fence.
rewrite (wf_rmwD WF) at 1 2.
rewrite (wf_rfeD WF) at 1.
rewrite (wf_coD WF) at 1.
rewrite (wf_frD WF) at 1.
generalize (R_ex_in_R lab).
basic_solver 42.
Qed.


Lemma wf_ct_hbD WF : hb^+ ≡ ⦗RW⦘ ⨾ hb^+ ⨾ ⦗RW⦘.
Proof.
split; [|basic_solver].
apply dom_helper_3.
rewrite (wf_hbD WF).
rewrite inclusion_ct_seq_eqv_l.
rewrite inclusion_ct_seq_eqv_r.
basic_solver.
Qed.

(******************************************************************************)
(** ** Properties  *)
(******************************************************************************)

Lemma ppo_alt : ppo ≡ 
  ⦗R⦘ ⨾ sb ⨾ ⦗RW⦘ ∪ ⦗W⦘ ⨾ sb ⨾ ⦗W⦘.
Proof.
unfold ppo.
split.
by apply inclusion_minus_l; basic_solver 12.
by unfolder; ins; desf; splits; eauto 10; intro; type_solver.
Qed.

Lemma ppo_in_sb : ppo ⊆ sb. 
Proof.
unfold ppo; basic_solver.
Qed.

End TSO.
