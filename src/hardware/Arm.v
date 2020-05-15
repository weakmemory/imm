(******************************************************************************)
(** * Definition of the ARMv8.3 memory model                                  *)
(* a fragment of the full model                                                *)
(* (omitting dmb.st, LDAR, and isb that are not used in compiled programs)    *)
(******************************************************************************)
From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Arm.

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
Notation "'coi'" := G.(coi).
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
Notation "'W_ex'" := (W_ex G).

Notation "'L'" := (W ∩₁ (fun a => is_true (is_rel lab a))).
Notation "'Q'" := (R ∩₁ (fun a => is_true (is_acq lab a))).
Notation "'A'" := (R ∩₁ (fun a => is_true (is_sc  lab a))).

Notation "'F^ld'" := (F ∩₁ (fun a => is_true (is_acq lab a))).
Notation "'F^sy'" := (F ∩₁ (fun a => is_true (is_rel lab a))).

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

(* Observed-by *)
Definition obs := rfe ∪ coe ∪ fre.

(* Dependency-ordered-before *)
Definition dob :=
   (addr ∪ data) ⨾ rfi^?
 ∪ (ctrl ∪ data) ⨾ ⦗W⦘ ⨾ coi^?
 ∪ addr ⨾ sb ⨾ ⦗W⦘.

(* Atomic-ordered-before *)
Definition aob :=
  rmw ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗Q⦘.

(* Barrier-ordered-before *)
Definition bob :=
    sb ⨾ ⦗F^sy⦘ ⨾ sb
  ∪ ⦗R⦘ ⨾ sb ⨾ ⦗F^ld⦘ ⨾ sb
  ∪ ⦗Q⦘ ⨾ sb
  ∪ sb ⨾ ⦗L⦘ ⨾ coi^?
  ∪ ⦗L⦘ ⨾ sb ⨾ ⦗A⦘.

(******************************************************************************)
(** ** Consistency *)
(******************************************************************************)

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.
Implicit Type ATOM : rmw_atomicity G.
Implicit Type SC_PER_LOC : sc_per_loc G.

Definition ArmConsistent :=
  ⟪ WF : Wf G ⟫ /\
  ⟪ COMP : complete G ⟫ /\
  ⟪ SC_PER_LOC: sc_per_loc G ⟫ /\
  ⟪ POWER_ATOMICITY : rmw_atomicity G ⟫ /\
  ⟪ ACYC : acyclic (obs ∪ dob ∪ aob ∪ bob) ⟫.

Implicit Type CON : ArmConsistent.


(******************************************************************************)
(** ** Additional derived relations to simlify our proofs *)
(******************************************************************************)

Definition obs' := rfe ∪ co ∪ fr.

Definition bob' :=
    bob ∪ ⦗R⦘ ⨾ sb ⨾ ⦗F^ld⦘ 
        ∪ sb ⨾ ⦗F^sy⦘ 
        ∪ ⦗F^ld ∪₁ F^sy⦘ ⨾ sb.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_obsE WF: obs ≡ ⦗E⦘ ⨾ obs ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold obs.
rewrite (wf_rfeE WF) at 1.
rewrite (wf_coeE WF) at 1.
rewrite (wf_freE WF) at 1.
basic_solver 42.
Qed.

Lemma wf_dobE WF: dob ≡ ⦗E⦘ ⨾ dob ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold dob.
rewrite (wf_addrE WF) at 1 2 3.
rewrite (wf_dataE WF) at 1 2.
rewrite (wf_rfiE WF) at 1.
rewrite (wf_ctrlE WF) at 1 2.
rewrite (wf_coiE WF) at 1.
rewrite wf_sbE at 1 2 3.
basic_solver 42.
Qed.

Lemma wf_aobE WF: aob ≡ ⦗E⦘ ⨾ aob ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold aob.
rewrite (wf_rmwE WF) at 1.
rewrite (wf_rfiE WF) at 1.
basic_solver 42.
Qed.

Lemma wf_bobE WF: bob ≡ ⦗E⦘ ⨾ bob ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold bob.
rewrite wf_sbE at 1 2 3 4 5 6 7.
rewrite (wf_coiE WF) at 1.
basic_solver 42.
Qed.

Lemma wf_obs'E WF: obs' ≡ ⦗E⦘ ⨾ obs' ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold obs'.
rewrite (wf_rfeE WF) at 1.
rewrite (wf_coE WF) at 1.
rewrite (wf_frE WF) at 1.
basic_solver 42.
Qed.

Lemma wf_bob'E WF: bob' ≡ ⦗E⦘ ⨾ bob' ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold bob'.
rewrite (wf_bobE WF) at 1.
rewrite wf_sbE at 1 2 3.
basic_solver 42.
Qed.

(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

Lemma wf_obsD WF: obs ≡ ⦗RW⦘ ⨾ obs ⨾ ⦗RW⦘.
Proof using.
split; [|basic_solver].
unfold obs.
rewrite (wf_rfeD WF) at 1.
rewrite (wf_coeD WF) at 1.
rewrite (wf_freD WF) at 1.
basic_solver 42.
Qed.

Lemma wf_obs'D WF: obs' ≡ ⦗RW⦘ ⨾ obs' ⨾ ⦗RW⦘.
Proof using.
split; [|basic_solver].
unfold obs'.
rewrite (wf_rfeD WF) at 1.
rewrite (wf_coD WF) at 1.
rewrite (wf_frD WF) at 1.
basic_solver 42.
Qed.

Lemma wf_dobD WF: dob ≡ dob ⨾ ⦗RW⦘.
Proof using.
split; [|basic_solver].
unfold dob.
rewrite (dom_r (wf_addrD WF)) at 1.
rewrite (dom_r (wf_dataD WF)) at 1.
rewrite (dom_r (wf_rfiD WF)) at 1.
rewrite (dom_r (wf_coiD WF)) at 1.
basic_solver 42.
Qed.

Lemma wf_aobD WF: aob ≡ aob ⨾ ⦗RW⦘.
Proof using.
split; [|basic_solver].
unfold aob.
rewrite (dom_r (wf_rmwD WF)) at 1.
basic_solver 42.
Qed.

(******************************************************************************)
(** ** Properties of consistent executions  *)
(******************************************************************************)

Lemma dob_alt WF :
 dob ≡
   addr
 ∪ (addr ∪ data) ⨾ rfi
 ∪ (ctrl ∪ data) ⨾ ⦗W⦘ ⨾ coi^?
 ∪ addr ⨾ sb ⨾ ⦗W⦘.
Proof using.
unfold dob.
rewrite (dom_r (wf_dataD WF)) at 1 3.
basic_solver 42.
Qed.

Lemma deps_in_ctrl_or_dob WF:
    deps ⊆ ctrl ∪ dob.
Proof using.
    rewrite (dob_alt WF).
unfold Execution.deps;
rewrite (dom_r (wf_dataD WF)) at 1.
basic_solver 12.
Qed.

Lemma dob_in_sb WF: dob ⊆ sb.
Proof using.
unfold dob.
rewrite (addr_in_sb WF).
rewrite (data_in_sb WF).
rewrite (ctrl_in_sb WF).
arewrite (coi ⊆ sb).
arewrite (rfi ⊆ sb).
generalize (@sb_trans G).
basic_solver 21.
Qed.

Lemma aob_in_sb WF: aob ⊆ sb.
Proof using.
unfold aob.
rewrite (rmw_in_sb WF).
arewrite (rfi ⊆ sb).
basic_solver 21.
Qed.

Lemma bob_in_sb WF: bob ⊆ sb.
Proof using.
unfold bob.
arewrite (coi ⊆ sb).
generalize (@sb_trans G).
basic_solver 21.
Qed.

Lemma bob'_in_sb WF: bob' ⊆ sb.
Proof using.
unfold bob'.
rewrite (bob_in_sb WF).
basic_solver 21.
Qed.

Lemma external_alt_coi CON (RMW_COI : rmw ⨾ coi ⊆ obs ∪ dob ∪ aob ∪ bob) :
    acyclic (coi ∪ obs ∪ dob ∪ aob ∪ bob).
Proof using.
  cdes CON.
  rewrite !(unionA coi). 
  apply acyclic_absorb; ins.
  2: { arewrite (coi ⊆ co). split; auto.
       apply (co_acyclic WF). }
  right; relsf; hahn_rel.
  { unfold obs.
    relsf; unionL.
    { arewrite (rfe ⊆ rf) at 1.
      arewrite (coi ⊆ co) at 1.
      rewrite (rf_co WF). basic_solver. }
    all: ie_unfolder.
    { generalize (coe_coi WF SC_PER_LOC). basic_solver 42. }
    generalize (fre_coi WF SC_PER_LOC). basic_solver 42. }
  { unionR left -> left -> right; rewrite dob_alt; ins.
    generalize (addr ∪ data), (ctrl ∪ data), (ctrl ∪ addr ⨾ sb). ins. relsf.
    unionL; rewrite ?seqA.
    { rewrite (dom_r (wf_coiD WF)) at 1.
      ie_unfolder. basic_solver 12. }
    { arewrite (rfi ⊆ rf) at 1.
      arewrite (coi ⊆ co) at 1.
      rewrite (rf_co WF). basic_solver. }
    { rewrite crE; relsf.
      generalize (@sb_trans G).
      generalize (co_trans WF).
      ie_unfolder. basic_solver 13. }
    rewrite (dom_r (wf_coiD WF)) at 1.
    generalize (@sb_trans G).
    ie_unfolder. basic_solver 42. }
  { unfold aob at 1; relsf; unionL.
    { apply RMW_COI. }
    rewrite (dom_l (wf_coiD WF)) at 1.
    type_solver 42. }
  assert (transitive coi).
  apply transitiveI; generalize (@sb_trans G) (co_trans WF); ie_unfolder; basic_solver 12.
  unionR right; unfold bob; relsf; rewrite ?seqA.
  arewrite (coi ⊆ sb) at 1.
  arewrite (coi ⊆ sb) at 1.
  arewrite (coi ⊆ sb) at 1.
  rewrite (@sb_sb G).
  arewrite_false (⦗A⦘ ⨾ coi).
  { rewrite WF.(wf_coiD). type_solver. }
  basic_solver 21.
Qed.

Lemma external_alt WF CON (RMW_COI : rmw ⨾ coi ⊆ obs ∪ dob ∪ aob ∪ bob) :
  acyclic (obs' ∪ dob ∪ aob ∪ bob).
Proof using.
  forward eapply external_alt_coi as AA; ins.
  unfold obs'.
  unfold acyclic in *; rewrite <- ct_of_union_ct_r in *.
  unfold obs in AA.
  rewrite !unionA, (unionAC (rfe)), <- !unionA in AA.
  rewrite <- coi_union_coe in AA.
  rewrite fri_union_fre.
  rewrite !unionA, (unionAC rfe), !(unionAC _ fri), <- !unionA.
  rewrite !(unionA fri).
  apply acyclic_absorb; ins; cycle 1.
  { arewrite (fri ⊆ fr).
    rewrite (wf_frD WF).
    split; auto.
    apply trans_irr_acyclic; [type_solver 12|apply transitiveI; type_solver 12]. }
  right; relsf; hahn_rel.
  { arewrite (fri ⊆ fr); rewrite (co_fr WF). basic_solver. }
  { arewrite (fri ⊆ fr); arewrite (rfe ⊆ rf); rewrite (rf_fr WF). basic_solver 12. }
  { arewrite (fri ⊆ fr); arewrite (fre ⊆ fr); rewrite (fr_fr WF). basic_solver 12. }
  { unionR left -> left -> right; rewrite dob_alt; ins.
    set (ad := addr ∪ data); set (cd := ctrl ∪ data); set (ca := ctrl ∪ addr ⨾ sb).
    ins; relsf.
    unionL; rewrite ?seqA.
    + rewrite (dom_r (wf_friD WF)) at 1.
      arewrite (fri ⊆ sb); basic_solver 12.
    + ie_unfolder.
      rewrite (seq_ii (rf_fr WF)).
      unfold ad at 1; relsf; unionL.
      -- rewrite (dom_r (wf_coD WF)) at 1.
         basic_solver 21.
      -- rewrite (dom_l (wf_coD WF)) at 1.
         unfold cd.
         basic_solver 21.
    + rewrite (dom_r (wf_coiD WF)) at 1.
      rewrite (dom_l (wf_friD WF)) at 1.
      type_solver.
    + rewrite (dom_l (wf_friD WF)) at 1.
      type_solver. }
  { transitivity (aob ∪ co); eauto 8 with hahn.
    unfold aob; relsf; rewrite ?seqA; unionL.
    + rewrite (dom_l (wf_friD WF)) at 1.
      rewrite (dom_r (wf_rmwD WF)) at 1.
      type_solver.
    + arewrite_id ⦗W_ex⦘; arewrite_id ⦗Q⦘; rels.
      ie_unfolder.
      rewrite (seq_ii (rf_fr WF)).
      basic_solver 42. }
  transitivity bob⁺; eauto with hahn.
  rewrite ct_end, seqA; unfold bob at 2; relsf.
  ie_unfolder.
  rewrite inclusion_inter_l1 at 4.
  rewrite inclusion_inter_l2 with (r:=fr), ?seqA.
  rewrite (@sb_sb G).
  arewrite_false (⦗L⦘ ⨾ (co ∩ sb)^? ⨾ fr).
  rewrite (dom_r (wf_coD WF)) at 1.
  rewrite (dom_l (wf_frD WF)) at 1.
  type_solver.
  arewrite (⦗A⦘ ⊆ ⦗A⦘ ⨾ ⦗A⦘) by basic_solver.
  arewrite (⦗L⦘ ⨾ sb ⨾ ⦗A⦘ ⊆ bob).
  arewrite (A ⊆₁ Q) by mode_solver.
  arewrite (⦗Q⦘ ⨾ sb ⊆ bob).
  rels; unionL; try solve [rewrite ct_end; hahn_frame_l; eauto with hahn].
  apply ct_unit.
Qed.

Lemma external_alt2 WF CON (RMW_COI : rmw ⨾ coi ⊆ obs ∪ dob ∪ aob ∪ bob) :
  acyclic (obs' ∪ dob ∪ aob ∪ bob').
Proof using.
  forward eapply external_alt as AA; ins.
  unfold bob'; rewrite <- !unionA in *.
  assert (APO: acyclic sb).
    by apply trans_irr_acyclic; eauto using sb_trans, sb_irr.
  assert (X: acyclic (obs' ∪ dob ∪ aob ∪ bob ∪ (⦗R⦘ ⨾ sb ⨾ ⦗F^ld⦘ ∪ sb ⨾ ⦗F^sy⦘))).
  { apply acyclic_absorb; eauto.
    left; relsf; rewrite !seqA. 
    transitivity (⦗R⦘ ⨾ sb ⨾ ⦗F^ld⦘⨾ sb ∪ sb ⨾ ⦗F^sy⦘ ⨾ sb).
    2: by transitivity bob; eauto with hahn; unionL; eauto with hahn.
    rewrite (dob_in_sb WF), (aob_in_sb WF), (bob_in_sb WF).
    unionL; eauto with hahn.
    1-2: rewrite (dom_l (wf_obs'D WF)); type_solver.
    split; auto.
    apply inclusion_acyclic with (r':=sb); basic_solver. }
  rewrite <- unionA in X.
  rewrite unionC; apply acyclic_absorb; eauto.
  right; transitivity bob; relsf; rewrite ?seqA; unionL.
  rewrite (dom_r (wf_obs'D WF)); type_solver.
  rewrite (wf_dobD WF); type_solver.
  rewrite (wf_aobD WF); type_solver.
  2-4: arewrite_id ⦗F^ld ∪₁ F^sy⦘; rels; eauto 6 with hahn.
  unfold bob; relsf; rewrite ?seqA.
  arewrite_false (⦗L⦘ ⨾ coi^? ⨾ ⦗F^ld ∪₁ F^sy⦘).
  rewrite (dom_r (wf_coiD WF)); type_solver.
  arewrite_false (⦗A⦘ ⨾ ⦗F^ld ∪₁ F^sy⦘).
  { type_solver. }
  arewrite_id ⦗F^ld ∪₁ F^sy⦘.
  rels.
  rewrite (@sb_sb G).
  basic_solver 21.
Qed.

Lemma external_alt3 WF CON : acyclic (obs ∪ dob ∪ aob ∪ bob').
Proof using.
  unfold bob'; rewrite <- !unionA in *.
  assert (APO: acyclic sb).
  { apply trans_irr_acyclic; eauto using sb_trans, sb_irr. }
  assert (X: acyclic (obs ∪ dob ∪ aob ∪ bob ∪ (⦗R⦘ ⨾ sb ⨾ ⦗F^ld⦘ ∪ sb ⨾ ⦗F^sy⦘))).
  { apply acyclic_absorb; eauto.
    left; relsf; rewrite !seqA. 
    transitivity (⦗R⦘ ⨾ sb ⨾ ⦗F^ld⦘⨾ sb ∪ sb ⨾ ⦗F^sy⦘ ⨾ sb).
    2: by transitivity bob; eauto with hahn; unionL; eauto with hahn.
    rewrite (dob_in_sb WF), (aob_in_sb WF), (bob_in_sb WF).
    unionL; eauto with hahn.
    1-2: rewrite (dom_l (wf_obsD WF)); type_solver.
    split; auto.
    { apply CON. }
    apply inclusion_acyclic with (r':=sb); basic_solver. }
  rewrite <- unionA in X.
  rewrite unionC; apply acyclic_absorb; eauto.
  right; transitivity bob; relsf; rewrite ?seqA; unionL.
  rewrite (dom_r (wf_obsD WF)); type_solver.
  rewrite (wf_dobD WF); type_solver.
  rewrite (wf_aobD WF); type_solver.
  2-4: arewrite_id ⦗F^ld ∪₁ F^sy⦘; rels; eauto 6 with hahn.
  unfold bob; relsf; rewrite ?seqA.
  arewrite_false (⦗L⦘ ⨾ coi^? ⨾ ⦗F^ld ∪₁ F^sy⦘).
  rewrite (dom_r (wf_coiD WF)); type_solver.
  arewrite_false (⦗A⦘ ⨾ ⦗F^ld ∪₁ F^sy⦘).
  { type_solver. }
  arewrite_id ⦗F^ld ∪₁ F^sy⦘.
  rels.
  rewrite (@sb_sb G).
  basic_solver 21.
Qed.

End Arm.
