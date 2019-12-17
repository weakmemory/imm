Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import AuxDef.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_s_hb.
Require Import imm_s.
Require Import imm_bob imm_s_ppo.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section ImmRFRMW.

  Variable G : execution.
  Variable WF : Wf G.
  Variable COM : complete G.
  Variable sc : relation actid.
  Variable IMMCON : imm_consistent G sc.

  Notation "'acts'" := G.(acts).
  Notation "'sb'" := G.(sb).
  Notation "'rmw'" := G.(rmw).
  Notation "'data'" := G.(data).
  Notation "'addr'" := G.(addr).
  Notation "'ctrl'" := G.(ctrl).
  Notation "'rf'" := G.(rf).
  Notation "'co'" := G.(co).
  Notation "'coe'" := G.(coe).
  Notation "'fr'" := G.(fr).

  Notation "'eco'" := G.(eco).

  Notation "'bob'" := G.(bob).
  Notation "'fwbob'" := G.(fwbob).
  Notation "'ppo'" := G.(ppo).
  Notation "'fre'" := G.(fre).
  Notation "'rfi'" := G.(rfi).
  Notation "'rfe'" := G.(rfe).
  Notation "'deps'" := G.(deps).
  Notation "'detour'" := G.(detour).
  Notation "'release'" := G.(release).
  Notation "'sw'" := G.(sw).
  Notation "'hb'" := G.(hb).

  Notation "'ar'" := (ar G sc).

Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (Events.mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'E'" := G.(acts_set).
Notation "'R'" := (fun x => is_true (is_r lab x)).
Notation "'W'" := (fun x => is_true (is_w lab x)).
Notation "'F'" := (fun x => is_true (is_f lab x)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Init'" := (fun a => is_true (is_init a)).
Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).

Notation "'Pln'" := (fun x => is_true (is_only_pln lab x)).
Notation "'Rlx'" := (fun x => is_true (is_rlx lab x)).
Notation "'Rel'" := (fun x => is_true (is_rel lab x)).
Notation "'Acq'" := (fun x => is_true (is_acq lab x)).
Notation "'Acqrel'" := (fun x => is_true (is_acqrel lab x)).
Notation "'Sc'" := (fun x => is_true (is_sc lab x)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).

Lemma ar_rfrmw_in_ar_ct : ar ;; rf ;; rmw ⊆ ar⁺.
Proof.
  assert (sb ;; sb ⊆ sb) as AA.
  { apply transitiveI. apply sb_trans. }
  
  assert (rfi ;; rmw ⊆ sb) as BB.
  { arewrite (rfi ⊆ sb). by rewrite rmw_in_sb. }

  rewrite rfi_union_rfe.
  rewrite seq_union_l, seq_union_r.
  unionL.
  2: { rewrite rfe_rmw_in_ar_ct; auto.
       rewrite ct_step with (r:=ar) at 1.
       apply ct_ct. }
  unfold imm_s.ar at 1.
  rewrite !seq_union_l.
  unionL.
  { rewrite wf_scD with (sc:=sc) at 1; [|by apply IMMCON].
    rewrite (dom_l WF.(wf_rfiD)).
    type_solver. }
  { rewrite (dom_l WF.(wf_rfiD)).
    rewrite (dom_r WF.(wf_rfeD)).
    type_solver. }
  unfold ar_int.
  rewrite !seq_union_l.
  unionL.
  5: by rewrite (dom_l (wf_rfiD WF)); type_solver.
  3: { rewrite WF.(wf_detourD).
       rewrite WF.(wf_rfiD). type_solver. }
  { unfold imm_bob.bob.
    rewrite !seq_union_l, !seqA.
    unionL.
    2: { rewrite BB, AA.
         arewrite (⦗R ∩₁ Acq⦘ ⨾ sb ⊆ bob).
         rewrite bob_in_ar. apply ct_step. }
    rewrite fwbob_rfi_rmw_in_fwbob; auto.
    rewrite fwbob_in_bob. by rewrite bob_in_ar. }
  { rewrite WF.(rmw_in_ppo), ppo_rfi_ppo. rewrite <- ct_step.
    rewrite ppo_in_ar_int. 
    apply ar_int_in_ar. }
  arewrite_id ⦗W⦘. rewrite seq_id_l.
  rewrite (dom_r WF.(wf_rmwD)).
  sin_rewrite BB. sin_rewrite AA.
  rewrite <- ct_step.
  rewrite w_ex_acq_sb_w_in_ar_int.
  apply ar_int_in_ar.
Qed.

Lemma ar_ct_rfrmw_in_ar_ct : ar⁺ ;; rf ;; rmw ⊆ ar⁺.
Proof.
  rewrite ct_end at 1. rewrite !seqA.
  rewrite ar_rfrmw_in_ar_ct.
  apply rt_ct.
Qed.

Lemma ar_rfrmw_acyclic : acyclic (ar ∪ rf ;; rmw).
Proof.
  rewrite ct_step with (r:=ar).
  rewrite unionC.
  apply acyclic_absorb.
  { right. apply ar_ct_rfrmw_in_ar_ct. }
  split.
  2: { red. rewrite ct_of_ct. apply IMMCON. }
  rewrite rf_rmw_in_co; eauto.
  { by apply co_acyclic. }
  apply coherence_sc_per_loc. by apply IMMCON.
Qed.

Lemma ar_ct_rfrmw_ct_in_ar_ct : ar⁺ ⨾ (rf ⨾ rmw)⁺ ⊆ ar⁺.
Proof.
  intros x y [z [AA BB]].
  apply clos_trans_t1n in BB.
  induction BB.
  2: apply IHBB.
  all: apply ar_ct_rfrmw_in_ar_ct; auto.
  all: basic_solver.
Qed.

Lemma ar_rfrmw_ct_in_ar_ct : ar ⨾ (rf ⨾ rmw)⁺ ⊆ ar⁺.
Proof.
  rewrite ct_step with (r:=ar) at 1. by apply ar_ct_rfrmw_ct_in_ar_ct.
Qed.

Lemma wf_ar_rfrmw_ct : well_founded (ar ∪ rf ;; rmw)⁺.
Proof.
  eapply wf_finite; auto.
  { red. rewrite ct_of_ct. apply ar_rfrmw_acyclic; auto. }
  rewrite wf_ar_rfrmw_ctE; auto.
  apply doma_eqv.
Qed.

End ImmRFRMW.
