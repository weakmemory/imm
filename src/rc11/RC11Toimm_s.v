(******************************************************************************)
(** * RC11 is weaker than IMM_S   *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxRel.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_common.
Require Import imm_s_hb.
Require Import imm_s.
Require Import RC11.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section RC11_TO_IMM_S.

Variable G : execution.

Notation "'E'" := G.(acts_set).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'rmw_dep'" := G.(rmw_dep).

Notation "'fr'" := G.(fr).
Notation "'eco'" := G.(eco).
Notation "'coe'" := G.(coe).
Notation "'coi'" := G.(coi).
Notation "'deps'" := G.(deps).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).

Notation "'detour'" := G.(detour).

Notation "'rs'" := G.(rs).
Notation "'release'" := G.(release).
Notation "'sw'" := G.(sw).
Notation "'hb'" := G.(hb).

Notation "'ar_int'" := G.(ar_int).
Notation "'ppo'" := G.(ppo).
Notation "'bob'" := G.(bob).

Notation "'ar'" := G.(ar).

Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

(******************************************************************************)
(** relations are contained in the corresponding ones **  *)
(******************************************************************************)

Lemma s_imm_consistentimplies_rc11_consistent (WF: Wf G) 
      (COND: ⦗R \₁ Acq⦘ ⨾ sb ⨾ ⦗W \₁ Rel⦘ ⊆ sb ⨾ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb ∪ ⦗R⦘ ⨾ deps ⨾ ⦗W⦘ ∪ rmw) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  rc11_consistent G.
Proof.
  cdes IPC. cdes IC.
  red. splits; auto.
  rewrite rfi_union_rfe with (G:=G). 
  unfold Execution.rfi; rewrite inclusion_inter_l2, <- unionA, unionK.
  eapply acyclic_ud with (adom := W) (bdom := R); eauto using sb_acyclic.
  1-2: by destruct WF; unfold Execution.rfe; rewrite wf_rfD; eauto using minus_doma, minus_domb with hahn. 
  assert (T:= @sb_trans G); relsf; clear T.
  eapply irreflexive_inclusion, Cext; apply inclusion_t_t2. 
  unfold imm_s.ar, imm_common.ar_int; unionL; eauto with hahn.
  arewrite (R ≡₁ (R ∩₁ Acq) ∪₁ (R \₁ Acq)).
    by unfolder; split; ins; desf; destruct (is_acq lab x); auto. 
  rewrite id_union; relsf; unionL.
    by rewrite inclusion_seq_eqv_r at 1; unfold imm_common.bob; auto 10 with hahn.
  arewrite (W ≡₁ (W ∩₁ Rel) ∪₁ (W \₁ Rel)) at 1.
    by unfolder; split; ins; desf; destruct (is_rel lab x); auto. 
  rewrite id_union; relsf; unionL.
    by rewrite inclusion_seq_eqv_l at 1; unfold imm_common.bob, imm_common.fwbob; auto 10 with hahn.
  rewrite COND.
  sin_rewrite rmw_in_ppo; auto.
  arewrite (⦗R⦘ ⨾ deps ⨾ ⦗W⦘ ⊆ ppo).
  { rewrite <- deps_rfi_in_ppo.
    sin_rewrite (ct_step deps).
    rewrite unionC, ct_unionE.
    basic_solver. }
  unionL.
  { rewrite <- seq_eqvK, seqA, <- seqA. 
    apply inclusion_step2_ct; unfold imm_common.bob, imm_common.fwbob; auto 10 with hahn. }
  all: etransitivity; [|by apply ct_step].
  all: basic_solver 20.
Qed.

End RC11_TO_IMM_S.
