(******************************************************************************)
(** * Weaker IMM model for Promise->IMM    *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_s_hb.
Require Import imm_bob.
Require Import imm_s_ppo.
Require Import imm_s_hb_hb.
Require Import imm.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section IMM.

Variable G : execution.
Variable sc : relation actid.

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
Notation "'hb'" := G.(imm_s_hb.hb).
Notation "'sw'" := G.(imm_s_hb.sw).

Notation "'bob'" := G.(bob).
Notation "'ppo'" := G.(imm_s_ppo.ppo).
Notation "'ar_int'" := G.(imm_s_ppo.ar_int).

Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).




(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

(* Definition psc := ⦗F∩₁Sc⦘ ⨾  hb ⨾ eco ⨾ hb ⨾ ⦗F∩₁Sc⦘. *)

Definition scb := sb ∪ (sb \ same_loc) ⨾ hb ⨾ (sb \ same_loc) ∪
                     (hb ∩ same_loc) ∪ co ∪ fr.
Definition psc_base := ⦗ Sc ⦘ ⨾ (⦗ F ⦘ ⨾ hb)^? ⨾ scb ⨾ (hb ⨾ ⦗ F ⦘)^? ⨾ ⦗ Sc ⦘.
Definition psc_f    := ⦗F∩₁Sc⦘ ⨾  hb ⨾ (eco ⨾ hb)^? ⨾ ⦗F∩₁Sc⦘.

Definition ar := sc ∪ rfe ∪ ar_int.

(******************************************************************************)
(** ** Consistency  *)
(******************************************************************************)

Record wf_sc :=
  { wf_scE : sc ≡ ⦗E⦘ ⨾ sc ⨾ ⦗E⦘ ;
    wf_scD : sc ≡ ⦗F∩₁Sc⦘ ⨾ sc ⨾ ⦗F∩₁Sc⦘ ;
    sc_trans : transitive sc ;
    wf_sc_total : is_total (E ∩₁ F ∩₁ Sc) sc ;
    sc_irr : irreflexive sc ;
  }.

Definition acyc_ext := acyclic ar.

Definition coh_sc := irreflexive (sc ⨾ hb ⨾ (eco ⨾ hb)^?).

Definition imm_consistent := 
  ⟪ Wf_sc : wf_sc ⟫ /\
  ⟪ Csc   : coh_sc ⟫ /\
  ⟪ Comp  : complete G ⟫ /\
  ⟪ Cint  : coherence G ⟫ /\
  ⟪ Cext  : acyc_ext ⟫ /\
  ⟪ Cat   : rmw_atomicity G ⟫.

Definition imm_psc_consistent :=
  ⟪ IC   : imm_consistent ⟫ /\
  ⟪ Cpsc : acyclic (psc_f ∪ psc_base) ⟫.

Implicit Type WF : Wf G.
Implicit Type WF_SC : wf_sc.
Implicit Type IMMCON : imm_consistent.
Implicit Type CSC : coh_sc.
Implicit Type COMP : complete G.
Implicit Type COH : coherence G.
Implicit Type ACYC_EXT : acyc_ext.
Implicit Type AT : rmw_atomicity G.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

(* Lemma wf_pscE WF : psc ≡ ⦗E⦘ ⨾ psc ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold psc; rewrite (wf_hbE WF) at 1 2.
basic_solver 42.
Qed. *)

Lemma wf_arE WF WF_SC : ar ≡ ⦗E⦘ ⨾ ar ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
unfold ar.
rewrite (wf_scE WF_SC), (wf_ar_intE WF), (wf_rfeE WF) at 1.
basic_solver 42.
Qed.


(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

(* Lemma wf_pscD : psc ≡ ⦗F∩₁Sc⦘ ⨾ psc ⨾ ⦗F∩₁Sc⦘.
Proof.
split; [|basic_solver].
unfold psc; basic_solver 42.
Qed. *)

(******************************************************************************)
(** ** init *)
(******************************************************************************)

(* Lemma no_psc_to_init WF : psc ≡ psc ⨾  ⦗fun x => ~ is_init x⦘.
Proof.
split; [|basic_solver].
rewrite wf_pscD at 1.
generalize (read_or_fence_is_not_init WF).
basic_solver 42.
Qed. *)

Lemma no_sc_to_init WF WF_SC :
 sc ≡ sc ⨾  ⦗fun x => ~ is_init x⦘.
Proof.
split; [|basic_solver].
rewrite wf_scD at 1; try done.
generalize (read_or_fence_is_not_init WF).
basic_solver 42.
Qed.

(******************************************************************************)
(** ** more properties  *)
(******************************************************************************)

Lemma F_sc_ar_F_sc WF WF_SC ACYC_EXT:
  ⦗F ∩₁ Sc⦘ ⨾ ar⁺ ⨾ ⦗F ∩₁ Sc⦘ ⊆ sc.
Proof.
rewrite wf_arE; try done.
rewrite inclusion_ct_seq_eqv_l, inclusion_ct_seq_eqv_r.
unfold ar.
destruct WF_SC.
unfolder; ins; desf.
eapply tot_ex; eauto; try basic_solver.
intro; eapply ACYC_EXT.
eapply t_trans; unfold ar; [basic_solver| apply t_step; basic_solver].
intro; eapply ACYC_EXT; unfold ar; basic_solver.
Qed.

Lemma sw_in_ar1 WF :
  sw ⊆ (<|F ∩₁ Rel|> ;; sb ∪ <|W ∩₁ Rel|> ;; (sb ∩ same_loc⨾ ⦗W⦘)^?) ⨾ 
  (rfe ∪ ar_int)⁺ ⨾ sb^? ∪ sb.
Proof.
remember (rfe ∪ ar_int) as ax.
  assert (rmw ⨾ (sb ∩ same_loc)^?⨾ ⦗W⦘ ⊆ ax) as CC.
  { rewrite crE; relsf; unionL.
    - rewrite (rmw_in_ppo WF).
      desf; unfold imm_s_ppo.ar_int. basic_solver 12.
    - desf; unfold imm_s_ppo.ar_int, imm_s_ppo.ppo.
    rewrite <- ct_step at 1. rewrite WF.(wf_rmwD) at 1. rewrite R_ex_in_R.
    basic_solver 21. }

  assert (fwbob G ⊆ ar) as EE.
  { unfold ar. unfold imm_s_ppo.ar_int.
    rewrite fwbob_in_bob. basic_solver 10. }

  assert (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⊆ sb^? ⨾ ⦗W⦘ ⨾ ar^?) as DD.
  { rewrite crE. rewrite !seq_union_l, !seq_union_r, seq_id_l.
    unionL.
    2: generalize (@sb_trans G); basic_solver 10.
    rewrite crE, seq_union_l, seq_id_l. unionR left.
    arewrite (⦗Rel⦘ ⨾ ⦗W⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⊆ ⦗W⦘ ⨾ fwbob G).
    { unfold fwbob. basic_solver 10. }
    rewrite EE. basic_solver. }
  
  assert (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ sb^? ⨾ ⦗W⦘ ⨾ ar^?) as FF.
  { rewrite crE with (r:=sb ∩ same_loc). rewrite !seq_union_l, !seq_union_r, seq_id_l.
    rewrite DD. unionL; [|done].
    basic_solver 10. }

  assert (⦗W⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc)^? ⊆ ⦗W⦘ ⨾ sb ∩ same_loc) as UU.
  { unfold Events.same_loc.
    unfolder. ins. desf; eexists; splits; eauto.
    { eapply sb_trans; eauto. }
    etransitivity; eauto. }

  assert (ar^? ⨾ ar ⨾ ar^? ⊆ ar⁺) as WW.
  { arewrite (ar ⊆ ar⁺) at 2. by rewrite ct_cr, cr_ct. }

  unfold imm_s_hb.sw, imm_s_hb.release, imm_s_hb.rs.
  rewrite (s_sw_in_ar_helper WF).

  rewrite (dom_l (wf_rfeD WF)).
  rewrite !seqA. 
  arewrite (rfe ⊆ ax) by desf.
  arewrite ((sb ∩ same_loc ⨾ ⦗W⦘)^?
             ∪ (sb ∩ same_loc)^? ⨾ (⦗W⦘ ⨾ ax ⨾ rmw ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘)⁺ ⊆
             (sb ∩ same_loc ⨾ ⦗W⦘)^? ⨾ (⦗W⦘ ⨾ ax ⨾ rmw ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘)^*).
  { rewrite rtE, seq_union_r, seq_id_r. apply union_mori; [done|].
    arewrite (⦗W⦘ ⊆ ⦗W⦘ ;; ⦗W⦘) at 1 by basic_solver.
    rewrite inclusion_ct_seq_eqv_l at 1.
    assert ((sb ∩ same_loc)^? ⨾ ⦗W⦘ ⊆ (sb ∩ same_loc ⨾ ⦗W⦘)^?) as AA by basic_solver.
    rewrite <- seqA. by rewrite AA at 1. }
  rewrite CC.
  arewrite ((⦗W⦘ ⨾ ax ⨾ ax)＊ ⊆ ax＊).
  { arewrite_id ⦗W⦘. rewrite seq_id_l.
    arewrite (ax ⨾ ax ⊆ ax⁺).
    2: { by rewrite rt_of_ct. }
    arewrite (ax ⊆ ax^*) at 1.
    apply ct_end. }
  arewrite (ax＊ ⨾ rf ⊆ ax⁺ ⨾ sb^? ∪ sb).
  { rewrite rfi_union_rfe.
    arewrite (rfe ⊆ ax) by desf.
    arewrite (rfi ⊆ sb).
    rewrite seq_union_r. rewrite <- ct_end.
    basic_solver 10. }
  rewrite !seq_union_l, !seq_union_r. 
  apply union_mori.
  2: { generalize (@sb_trans G). basic_solver 20. }
  rewrite seqA.
  arewrite (sb^? ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘ ⊆ sb^?).
  { generalize (@sb_trans G). basic_solver. }
  rewrite crE at 1.
  rewrite unionC, !seq_union_l, !seq_union_r, seq_id_l.
  apply union_mori.
  { generalize (@sb_trans G). basic_solver 20. }
  generalize (@sb_same_loc_trans G). basic_solver 20.
Qed.

Lemma f_sc_hb_f_sc_in_rfe_ar_int WF :
  ⦗F ∩₁ Sc⦘ ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⊆ (rfe ∪ ar_int)⁺.
Proof.
  unfold imm_s_hb.hb.
  rewrite (dom_l (wf_swD WF)).
  rewrite (sw_in_ar1 WF).
  remember (rfe ∪ ar_int) as ax.
  rewrite seq_union_r.
  arewrite (⦗FW ∩₁ Rel⦘ ⨾ sb ⊆ sb).

  rewrite unionC.
  rewrite unionA.
  arewrite (sb ∪ sb ⊆ sb).
  rewrite unionC.
  rewrite path_union.

  rewrite seq_union_l, seq_union_r. unionL.
  { rewrite ct_of_trans; [|by apply sb_trans].
    desf. rewrite <- ct_step; unfold imm_s_ppo.ar_int, imm_bob.bob, imm_bob.fwbob.
    mode_solver 21. }
  rewrite rt_of_trans; [|by apply sb_trans].
  rewrite ct_seq_swap.
  rewrite !seqA.
  arewrite (sb^? ⨾ sb^? ⊆ sb^?).
  { generalize (@sb_trans G). basic_solver. }
  rewrite ct_rotl, !seqA.

  assert (sb^? ⨾ ⦗FW ∩₁ Rel⦘ ⊆ ax^?) as BB.
  { desf.
    rewrite <- bob_in_ar_int, <- fwbob_in_bob.
    unfold imm_bob.fwbob.
    mode_solver 12. }

  sin_rewrite !BB.

  arewrite (sb^? ⨾ ⦗F ∩₁ Sc⦘ ⊆ ax^?).
  { desf.
    rewrite <- bob_in_ar_int, <- fwbob_in_bob.
    unfold imm_bob.fwbob.
    mode_solver 12. }
  rels.
  arewrite ((⦗F ∩₁ Rel⦘ ⨾ sb ∪ ⦗W ∩₁ Rel⦘ ⨾ (sb ∩ same_loc ⨾ ⦗W⦘)^?) ⊆ ax^?).
  { unionL.
    2: { rewrite crE. rewrite seq_union_r. unionL.
         { basic_solver. }
         rewrite sb_from_w_rel_in_bob. subst. unfold imm_s_ppo.ar_int. basic_solver 10. }
    arewrite (Rel ⊆₁ Acq/Rel) by mode_solver.
    rewrite sb_from_f_in_fwbob. rewrite fwbob_in_bob.
    subst. unfold imm_s_ppo.ar_int. basic_solver 10. }
  rels.
  basic_solver.
Qed.

Lemma f_sc_hb_f_sc_in_ar WF : 
  ⦗F ∩₁ Sc⦘ ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⊆ ar⁺.
Proof.
  rewrite WF.(f_sc_hb_f_sc_in_rfe_ar_int).
  unfold ar. apply clos_trans_mori. eauto with hahn.
Qed.

Lemma f_sc_hb_f_sc_in_sc WF WF_SC ACYC_EXT: 
  ⦗F ∩₁ Sc⦘ ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ⊆ sc.
Proof.
arewrite (⦗F ∩₁ Sc⦘ ⊆ ⦗F ∩₁ Sc⦘ ⨾ ⦗F ∩₁ Sc⦘) by basic_solver.
sin_rewrite (f_sc_hb_f_sc_in_ar WF).
apply F_sc_ar_F_sc; done.
Qed.

Lemma wf_ar WF IMMCON : well_founded ar.
Proof.
  eapply wf_finite; auto.
  { cdes IMMCON. apply Cext. }
  rewrite wf_arE; auto.
  2: by apply IMMCON.
  apply doma_eqv.
Qed.

Lemma wf_ar_tc WF IMMCON : well_founded (ar⁺).
Proof.
  eapply wf_finite; auto.
  { cdes IMMCON. unfold acyclic. rewrite ct_of_ct.
    apply Cext. }
  rewrite wf_arE; auto.
  2: by apply IMMCON.
  apply ct_doma. apply doma_eqv.
Qed.

Lemma ar_int_in_ar : ar_int ⊆ ar.
Proof. unfold ar. basic_solver. Qed.

Lemma ppo_in_ar : ppo ⊆ ar.
Proof.
  etransitivity; [|by apply ar_int_in_ar].
  apply ppo_in_ar_int.
Qed.

Lemma bob_in_ar : bob ⊆ ar.
Proof.
  etransitivity; [|by apply ar_int_in_ar].
  apply bob_in_ar_int.
Qed.

Lemma detour_in_ar : detour ⊆ ar.
Proof.
  etransitivity; [|by apply ar_int_in_ar].
  apply detour_in_ar_int.
Qed.

Lemma rfe_in_ar : rfe ⊆ ar.
Proof. unfold ar. basic_solver. Qed.

Lemma sc_in_ar : sc ⊆ ar.
Proof. unfold ar. basic_solver. Qed.

Lemma w_ex_acq_sb_w_in_ar : ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ar.
Proof.
  etransitivity; [|by apply ar_int_in_ar].
  apply w_ex_acq_sb_w_in_ar_int.
Qed.

Lemma coh_sc_alt WF WF_SC CSC COH : ⦗F∩₁Sc⦘ ⨾  hb ⨾ eco ⨾ hb ⨾ ⦗F∩₁Sc⦘ ⊆ sc.
Proof.
rewrite (dom_l (wf_hbE WF)) at 1.
rewrite (dom_r (wf_hbE WF)) at 2.
unfolder; ins; desf.
eapply tot_ex.
apply WF_SC.
basic_solver.
basic_solver.
intro; eapply CSC; basic_solver 10.
intro; subst.
eapply COH.
eexists; splits; [ | eby right].
eapply hb_trans; eauto.
Qed.

Proposition coh_helper_alt :
  irreflexive (hb ⨾ sc^? ∪ hb ⨾ (sc ⨾ hb)^? ⨾ rfe ∪ 
  hb ⨾ (sc ⨾ hb)^? ⨾ co ∪ hb ⨾ (sc ⨾ hb)^? ⨾ co ⨾ rfe ∪ 
  hb ⨾ (sc ⨾ hb)^? ⨾ fr ∪ hb ⨾ (sc ⨾ hb)^? ⨾ fr ⨾ rfe) -> 
  irreflexive (hb ⨾ (sc ⨾ hb)^? ⨾ eco^?).
Proof.
unfold Execution_eco.eco; relsf.
rewrite rfi_union_rfe; relsf.
arewrite (rfi ⊆ sb); rewrite sb_in_hb; rewrite !crE; relsf.
ins; unionL.
all: try rotate 1.
all: generalize (@hb_trans G); ins; relsf.
all: try (unfolder in *; basic_solver 12).
all: try (unfolder in *; basic_solver 16).
Qed.

Lemma init_co_w WF IMMCON
      e e' (INIT : is_init e) (NINIT : ~ is_init e')
      (EE : E e') (WW : W e') (SL : same_loc e e') :
  co e e'.
Proof.
  destruct (is_w_loc lab e' WW) as [l LOC].
  red in SL. rewrite LOC in SL.
  unfold is_init in INIT. unfold Events.loc in SL.
  destruct e; [|done].
  rewrite WF.(wf_init_lab) in SL. inv SL.
  assert (E (InitEvent l)) as EL.
  { apply WF.(wf_init). eexists. eauto. }
  edestruct WF.(wf_co_total) as [CO|CO]; eauto; desf.
  { split; [split|]; auto. by apply init_w.
    unfold Events.loc at 1. by rewrite WF.(wf_init_lab). }
  { intros H. subst. desf. }
  exfalso. cdes IMMCON.
  eapply Cint. eexists. split.
  { apply sb_in_hb. by apply init_ninit_sb with (y:=e'); eauto. }
  apply r_step. apply Execution_eco.co_in_eco; eauto.
Qed.

Lemma wf_rfrmw_irr WF IMMCON : irreflexive (rf ⨾ rmw).
Proof.
  arewrite (rmw ⊆ sb).
  { rewrite WF.(wf_rmwi). basic_solver. }
  rewrite Execution_eco.rf_in_eco.
  rewrite sb_in_hb. cdes IMMCON.
  red in Cint. generalize Cint. basic_solver 10.
Qed.

Lemma rfrmw_in_im_co WF IMMCON :
  rf ⨾ rmw ⊆ immediate co.
Proof. 
  cdes IMMCON.
  apply rf_rmw_in_coimm; auto using coherence_sc_per_loc.
Qed.

Lemma rfe_rmw_in_ar_ct WF : rfe ;; rmw ⊆ ar⁺.
Proof.
  rewrite <- ct_ct.
  rewrite rfe_in_ar, WF.(rmw_in_ppo), ppo_in_ar.
  eby rewrite <- ct_step.
Qed.

Lemma rfe_ppo_in_ar_ct : rfe ;; ppo ⊆ ar⁺.
Proof.
  rewrite <- ct_ct.
  rewrite rfe_in_ar, ppo_in_ar.
  eby rewrite <- ct_step.
Qed.

(*
Lemma rfe_Rex_sb_in_ar_ct : rfe ;; <|R_ex|> ;; sb ;; <|W|> ⊆ ar⁺.
Proof.
  arewrite (⦗R_ex⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ppo).
  2: by apply rfe_ppo_in_ar_ct.
  unfold imm_s_ppo.ppo. rewrite <- ct_step, !seq_union_l, !seq_union_r, !seqA.
  unionR left -> right.
  type_solver.
Qed.
*)

(*
Lemma rfe_rmw_sb_in_ar_ct WF : rfe ;; rmw ;; sb ;; <|W|> ⊆ ar⁺.
Proof.
  rewrite (dom_l WF.(wf_rmwD)), WF.(rmw_in_sb), !seqA.
  (* TODO: introduce a lemma *)
  arewrite (sb ;; sb ⊆ sb).
  { apply transitiveI. apply sb_trans. }
  apply rfe_Rex_sb_in_ar_ct.
Qed.
*)

Lemma sb_release_rmw_in_fwbob WF
      (SPL  : Execution_eco.sc_per_loc G)
      (COMP : complete G) :
  sb^? ∩ release G ⨾ sb ∩ Events.same_loc lab ⨾ rmw ⊆ fwbob G.
Proof.
  rewrite (dom_r WF.(wf_rmwD)).
  rewrite WF.(rmw_in_sb_loc).
  sin_rewrite rewrite_trans.
  2: by apply sb_same_loc_trans.
  rewrite (dom_l WF.(wf_releaseD)).
  arewrite (sb^? ∩ (⦗(F ∪₁ W) ∩₁ Rel⦘ ⨾ release G) ⊆
            ⦗(F ∪₁ W) ∩₁ Rel⦘ ⨾ (sb^? ∩ release G)).
  { basic_solver. }
  rewrite set_inter_union_l.
  rewrite id_union, seq_union_l.
  unionL.
  { unfold fwbob.
    unionR right. 
    arewrite (sb^? ∩ release G ⨾ sb ∩ Events.same_loc lab ⊆ sb).
    { generalize (@sb_trans G). basic_solver. }
    mode_solver. }
  unfold release.
  arewrite (⦗W ∩₁ Rel⦘ ⨾ sb^? ∩ (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ rs G) ⊆
            ⦗W ∩₁ Rel⦘ ⨾ sb^? ∩ (⦗Rel⦘ ⨾ rs G)).
  { type_solver 10. }
  rewrite rs_in_co; auto.
  rewrite WF.(wf_col).
  arewrite (sb^? ∩ (⦗Rel⦘ ⨾ ⦗W⦘ ⨾ (Events.same_loc lab)^?) ⊆
               (sb ∩ Events.same_loc lab)^?).
  { basic_solver. }
  sin_rewrite rewrite_trans_seq_cr_l.
  2: by apply sb_same_loc_trans.
  unfold fwbob. eauto with hahn.
Qed.

Lemma no_ar_to_init WF IMMCON : ar ;; <|is_init|> ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfold ar.
  rewrite WF.(ar_int_in_sb). rewrite no_sb_to_init.
  rewrite wf_scD; [|by apply IMMCON].
  rewrite WF.(wf_rfeD).
  rewrite seq_union_l. unionL; [|basic_solver].
  rewrite WF.(init_w). type_solver 10.
Qed.

Lemma no_ar_rfrmw_to_init WF IMMCON : (ar ∪ rf ⨾ rmw) ;; <|is_init|> ≡ ∅₂.
Proof.
  split; [|basic_solver].
  rewrite seq_union_l, seqA, no_ar_to_init; auto.
  rewrite WF.(rmw_in_sb). rewrite no_sb_to_init.
  basic_solver.
Qed.

Lemma wf_ar_rfrmwE WF IMMCON :
  ar ∪ rf ;; rmw ≡ <|E|> ;; (ar ∪ rf ;; rmw) ;; <|E|>.
Proof.
  rewrite wf_arE at 1; auto.
  2: by apply IMMCON.
  rewrite (dom_l WF.(wf_rfE)) at 1.
  rewrite (dom_r WF.(wf_rmwE)) at 1.
  basic_solver 10.
Qed.

Lemma wf_ar_rfrmw_ctE WF IMMCON :
  (ar ∪ rf ;; rmw)⁺ ≡ <|E|> ;; (ar ∪ rf ;; rmw)⁺ ;; <|E|>.
Proof.
  split; [|basic_solver].
  rewrite wf_ar_rfrmwE at 1; auto.
  rewrite inclusion_ct_seq_eqv_l.
    by rewrite inclusion_ct_seq_eqv_r.
Qed.

Lemma ar_ar_in_ar_ct : ar ;; ar ⊆ ar⁺.
Proof.
  rewrite ct_step with (r:=ar) at 1 2. apply ct_ct.
Qed.

Lemma rfe_n_same_tid WF IMMCON : rfe ∩ same_tid ⊆ ∅₂.
Proof.
  arewrite (rfe ∩ same_tid ⊆ rfe ∩ (<|E|> ;; same_tid ;; <|E|>)).
  { rewrite WF.(wf_rfeE) at 1. basic_solver. }
  arewrite (⦗E⦘ ⨾ same_tid ⨾ ⦗E⦘ ⊆ same_tid ∩ (⦗E⦘ ⨾ same_tid ⨾ ⦗E⦘)) by basic_solver.
  rewrite tid_sb.
  rewrite !inter_union_r.
  unionL.
  3: { rewrite WF.(wf_rfeD). rewrite init_w; eauto. type_solver. }
  2: { unfolder. ins. desf.
       cdes IMMCON.
       eapply Cint. eexists. split.
       { eby apply sb_in_hb. }
       right. apply rf_in_eco.
       match goal with
       | H : rfe _ _ |- _ => apply H
       end. }
  unfolder. ins. desf.
  { eapply eco_irr; eauto. apply rf_in_eco.
    match goal with
    | H : rfe _ _ |- _ => apply H
    end. }
  cdes IMMCON.
  eapply (thread_rfe_sb WF (coherence_sc_per_loc Cint)).
  basic_solver 10.
Qed.

Lemma ar_W_in_ar_int WF IMMCON : ar ;; <|W|> ⊆ ar_int.
Proof.
  unfold ar. erewrite wf_scD; [|by apply IMMCON].
  rewrite WF.(wf_rfeD). type_solver.
Qed.

End IMM.
