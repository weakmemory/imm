Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import Lia.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob.
Require Import imm_s.
Require Import imm_s_ppo.
Require Import imm_s_rfppo.
Require Import AuxDef.
Require Import SetSize.
Require Import FairExecution.
Require Import ImmFair.
Require Import AuxRel2.
Require Import CountabilityHelpers.
Import ListNotations.

Set Implicit Arguments.

Inductive trav_action :=
| ta_cover
| ta_issue
| ta_propagate (tid : thread_id)
| ta_reserve
.

Definition is_ta_propagate ta :=
  match ta with 
  | ta_propagate _ => true
  | _              => false
  end.

Definition ta_propagate_tid ta :=
  match ta with 
  | ta_propagate t => t
  | _              => tid_init
  end.

Definition trav_label : Set := trav_action * actid.
Definition action : trav_label -> trav_action := fst.
Definition event  : trav_label -> actid       := snd.
Definition mkTL ta e : trav_label := (ta, e).

Lemma trav_label_countable: countable (@set_full trav_label).
Proof using.
  apply countable_prod.
  2: now apply actid_countable. 
  apply countable_subset with
    (s':=eq ta_cover ∪₁ eq ta_issue ∪₁ eq ta_reserve ∪₁ (fun ta => exists tid, ta = ta_propagate tid)).
  2: { unfolder. ins. destruct x; eauto. }
  apply countable_union.
  { apply finite_countable. exists [ta_cover; ta_issue; ta_reserve].
    clear; basic_solver. }
  pose pos_countable as AA. destruct AA as [AA|AA].
  { exfalso. apply AA. repeat constructor. }
  desf. right. exists (fun n => ta_propagate (nu n)).
  destruct AA; desf.
  { left. splits; ins.
    { now exists (nu i). }
    { inv EQ. now apply INJ. }
    desf; eauto.
    destruct (SUR tid) as [y].
    { clear; basic_solver. }
    now exists y; subst. }
  right. exists n. splits; ins.
  { now exists (nu i). }
  { inv EQ. now apply INJ. }
  desf; eauto.
  destruct (SUR tid) as [y [HH DD]].
  { clear; basic_solver. }
  exists y. now splits; auto; subst. 
Qed.

Lemma event_surj y : exists x, y = event x.
Proof using.
  ins. exists (mkTL ta_cover y); ins.
Qed.

Lemma event_cover_finite_inj y :
  set_finite (fun x => y = event x /\ (action ↓₁ eq ta_cover) x).
Proof using.
  ins. exists [mkTL ta_cover y]. 
  ins. desf. red in IN0. destruct x as [[]]; ins; auto.
Qed.

Lemma event_issue_finite_inj y :
  set_finite (fun x => y = event x /\ (action ↓₁ eq ta_issue) x).
Proof using.
  ins. exists [mkTL ta_issue y]. 
  ins. desf. red in IN0. destruct x as [[]]; ins; auto.
Qed.

Definition graph_threads (G: execution): thread_id -> Prop :=
  tid ↑₁ (acts_set G \₁ is_init). 

Definition is_ta_propagate_to_G (G: execution): trav_action -> Prop := 
  ⋃₁ t ∈ graph_threads G, eq (ta_propagate t). 

Definition SB (G: execution) (sc: relation actid) :=
  ⦗action ↓₁ (eq ta_cover)⦘
      ⨾ (event ↓ (sb G ∪ sc)⁺)
      ⨾ ⦗action ↓₁ (eq ta_cover)⦘.

Definition RF (G: execution):=
  ⦗action ↓₁ (eq ta_issue)⦘
    ⨾ (event ↓ (⦗is_w (lab G)⦘ ⨾ (rf G)^?))
    ⨾ ⦗action ↓₁ (eq ta_cover)⦘.

Definition FWBOB (G: execution):=
  ⦗action ↓₁ (eq ta_cover)⦘
    ⨾ (event ↓ (fwbob G⨾ ⦗is_w (lab G)⦘))
    ⨾ ⦗action ↓₁ (eq ta_issue)⦘.

Definition AR (G: execution) (sc: relation actid) :=
  ⦗action ↓₁ (eq ta_issue)⦘
    ⨾ (event ↓ (⦗is_w (lab G)⦘ ⨾ (ar G sc ∪ rf G ⨾ ppo G ∩ same_loc (lab G))⁺ ⨾ ⦗is_w (lab G)⦘))
    ⨾ ⦗action ↓₁ (eq ta_issue)⦘.

Definition IPROP (G: execution) :=
  ⦗action ↓₁ (eq ta_issue)⦘
    ⨾ (event ↓ (eq ⨾ ⦗is_w (lab G)⦘))
    ⨾ ⦗action ↓₁ is_ta_propagate_to_G G⦘.

Definition PROP (G: execution) (sc: relation actid): relation trav_label :=
  ⦗action ↓₁ (eq ta_cover)⦘ ⨾
  ((event ↓ ((sb G)^? ⨾ (ar G sc ∪ rf G ⨾ ppo G ∩ same_loc (lab G))^* ⨾
             (sb G)^? ⨾ (co G)^? ⨾ ⦗is_w (lab G)⦘))
       ∩ (fun ta1 ta2 =>
            tid (event ta1) = ta_propagate_tid (action ta2))) ⨾
  ⦗action ↓₁ is_ta_propagate_to_G G⦘.

(* Essentially, it is an alternative representation of a part of tc_coherent *)
Definition iord (G: execution) (sc: relation actid): relation trav_label :=
  restr_rel (event ↓₁ (acts_set G \₁ is_init))
            (SB G sc ∪ RF G ∪ FWBOB G ∪ AR G sc ∪ IPROP G ∪ PROP G sc).

Global Ltac iord_parts_unfolder := 
  unfold iord, SB, RF, FWBOB, AR, PROP, IPROP. 

Global Ltac iord_dom_unfolder :=
  iord_parts_unfolder;
  unfold is_ta_propagate_to_G in *;
  (* clear; *)
  unfolder; intros [?a ?b] [?c ?d]; ins; desc;
  (try match goal with
       | z : trav_label |- _ => destruct z; desf; ins; desf
       end);
  desf.

Global Ltac iord_dom_solver := by iord_dom_unfolder. 
  
Section TravLabel. 
  Context (G : execution) (sc : relation actid).
  Implicit Types (WF : Wf G) (COMP : complete G)
           (WFSC : wf_sc G sc) (CONS : imm_consistent G sc)
           (MF : mem_fair G).

  Notation "'sb'" := (sb G).
  Notation "'rmw'" := (rmw G).
  Notation "'data'" := (data G).
  Notation "'addr'" := (addr G).
  Notation "'ctrl'" := (ctrl G).
  Notation "'rf'" := (rf G).
  Notation "'co'" := (co G).
  Notation "'coe'" := (coe G).
  Notation "'fr'" := (fr G).

  Notation "'fwbob'" := (fwbob G).
  Notation "'ppo'" := (ppo G).
  Notation "'ar'" := (ar G sc).
  Notation "'fre'" := (fre G).
  Notation "'rfi'" := (rfi G).
  Notation "'rfe'" := (rfe G).
  Notation "'deps'" := (deps G).
  Notation "'detour'" := (detour G).

  Notation "'lab'" := (lab G).
  Notation "'loc'" := (loc lab).
  Notation "'val'" := (val lab).
  Notation "'mod'" := (Events.mod lab).
  Notation "'same_loc'" := (same_loc lab).
  
  Notation "'E'" := (acts_set G).
  Notation "'R'" := (fun x => is_true (is_r lab x)).
  Notation "'W'" := (fun x => is_true (is_w lab x)).
  Notation "'F'" := (fun x => is_true (is_f lab x)).
  Notation "'Sc'" := (fun x => is_true (is_sc lab x)).
  Notation "'RW'" := (R ∪₁ W).
  Notation "'FR'" := (F ∪₁ R).
  Notation "'FW'" := (F ∪₁ W).
  Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
  Notation "'W_ex'" := (W_ex G).
  Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

  (* iord *)
  Notation "'SB'" := (SB G sc). 
  Notation "'RF'" := (RF G). 
  Notation "'FWBOB'" := (FWBOB G). 
  Notation "'AR'" := (AR G sc). 
  Notation "'IPROP'" := (IPROP G). 
  Notation "'PROP'" := (PROP G sc).
  Notation "'iord'" := (iord G sc).

  Lemma iord_irreflexive WF COMP WFSC CONS : irreflexive iord.
  Proof using.
    iord_dom_unfolder.
    { eapply sb_sc_acyclic; eauto. apply CONS. }
    eapply ar_rf_ppo_loc_acyclic; eauto. 
  Qed. 
  
  Lemma AR_trans : transitive AR.
  Proof using.
    unfold "AR".
    rewrite <- restr_relE.
    apply transitive_restr.
    apply transitiveI. rewrite map_rel_seq.
    apply map_rel_mori; auto.
    hahn_frame.
    arewrite_id ⦗W⦘.
    now rewrite !seq_id_l, ct_ct.
  Qed.

  Lemma AR_irr WF COMP CONS : irreflexive AR.
  Proof using.
    unfold "AR".
    rewrite <- restr_relE.
    apply irreflexive_restr.
    apply map_rel_irr.
    arewrite_id ⦗W⦘. rewrite !seq_id_l, seq_id_r.
    apply ar_rf_ppo_loc_acyclic; auto.
  Qed.
  
  Local Hint Resolve AR_trans AR_irr : lbase.

  Lemma AR_acyc WF COMP CONS : acyclic AR.
  Proof using.
    apply trans_irr_acyclic; auto with lbase.
  Qed.

  Local Hint Resolve AR_acyc : lbase.
  
  Lemma SBRF : SB ⨾ RF ⊆ ∅₂.
  Proof using. iord_dom_solver. Qed.
  
  Lemma SBAR : SB ⨾ AR ⊆ ∅₂.
  Proof using. iord_dom_solver. Qed.

  Lemma RFAR : RF ⨾ AR ⊆ ∅₂.
  Proof using. iord_dom_solver. Qed.

  Lemma RFRF : RF ⨾ RF ⊆ ∅₂.
  Proof using. iord_dom_solver. Qed.
  
  Lemma RF_trans : transitive RF.
  Proof using. iord_dom_solver. Qed.

  Lemma RF_irr : irreflexive RF.
  Proof using. iord_dom_solver. Qed.

  Local Hint Resolve SBRF SBAR RFAR RFRF RF_trans RF_irr : lbase.

  Lemma eSB_in_sb_sc_ct : event ↑ SB ⊆ (sb ∪ sc)⁺.
  Proof using. unfold "SB". clear. basic_solver 10. Qed.

  Lemma SB_acyclic WF WFSC CONS : acyclic SB.
  Proof using.
    eapply collect_rel_acyclic with (f:=event).
    rewrite eSB_in_sb_sc_ct.
    red. rewrite ct_of_ct.
    apply sb_sc_acyclic; auto.
    apply CONS.
  Qed.
  
  Lemma SB_trans : transitive SB.
  Proof using.
    unfold "SB".
    rewrite <- restr_relE.
    apply transitive_restr.
    apply transitiveI.
    rewrite map_rel_seq.
    now rewrite ct_ct.
  Qed.
  
  Lemma SB_irr WF WFSC CONS : irreflexive SB.
  Proof using.
    arewrite (SB ⊆ SB⁺).
    now apply SB_acyclic.
  Qed.

  Lemma FWBOBFWBOB : FWBOB ⨾ FWBOB ⊆ ∅₂.
  Proof using. iord_dom_solver. Qed.

  Local Hint Resolve SB_acyclic SB_trans SB_irr FWBOBFWBOB : lbase.

  Lemma FWBOB_trans : transitive FWBOB.
  Proof using.
    apply transitiveI. rewrite FWBOBFWBOB. clear; basic_solver 1.
  Qed.

  Lemma FWBOB_irr : irreflexive FWBOB.
  Proof using. iord_dom_solver. Qed.

  Local Hint Resolve FWBOB_trans FWBOB_irr : lbase.

  Lemma IPROP_trans : transitive IPROP.
  Proof using. apply transitiveI. iord_dom_solver. Qed.
  
  Lemma IPROP_irr : irreflexive IPROP.
  Proof using. iord_dom_solver. Qed.

  Local Hint Resolve IPROP_trans IPROP_irr : lbase.

  Lemma PROP_trans : transitive PROP.
  Proof using. apply transitiveI. iord_dom_solver. Qed.

  Lemma PROP_irr : irreflexive PROP.
  Proof using. iord_dom_solver. Qed.

  Local Hint Resolve PROP_trans PROP_irr : lbase.

  Lemma SBRF_acyc WF WFSC CONS : acyclic (SB ∪ RF).
  Proof using.
    apply acyclic_utt; splits; auto with lbase.
    rewrite SBRF. 
    apply false_acyclic.
  Qed.

  Local Hint Resolve SBRF_acyc : lbase.

  Lemma RFSB_trans : transitive (RF ⨾ SB).
  Proof using.
    apply transitiveI. rewrite !seqA.
    sin_rewrite SBRF. clear. basic_solver 1.
  Qed.

  Lemma FWBOBSB : FWBOB ⨾ SB ⊆ ∅₂.
  Proof using. iord_dom_solver. Qed.

  Local Hint Resolve RFSB_trans FWBOBSB event_surj
        event_cover_finite_inj
        event_issue_finite_inj : lbase.

  Lemma ERF : event ↑ RF ⊆ rf^?.
  Proof using. unfold "RF". clear. basic_solver 10. Qed.
  Lemma EFWBOB : event ↑ FWBOB ⊆ fwbob.
  Proof using. unfold "FWBOB". clear. basic_solver 10. Qed.
  Lemma EAR : event ↑ AR ⊆ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺.
  Proof using. unfold "AR". clear. basic_solver 10. Qed.

  Lemma RFSBFWBOBINAR WF WFSC CONS : RF ⨾ SB^? ⨾ FWBOB ⊆ AR.
  Proof using.
    iord_parts_unfolder. 
    rewrite !seqA.
    hahn_frame.
    arewrite_id ⦗action ↓₁ eq ta_cover⦘. rewrite !seq_id_l, !seq_id_r.
    rewrite <- !map_rel_seq2; auto with lbase.
    rewrite !seqA.
    hahn_frame.
    rewrite map_rel_cr, !map_rel_seq.
    apply map_rel_mori; auto.
    rewrite cr_of_ct. rewrite sb_sc_rt; auto; try apply CONS.
    rewrite !seqA.
    rewrite rf_sb_sc_sb_fwbob_in_ar; auto.
    apply clos_trans_mori. eauto with hahn.
  Qed.

  Lemma RFSBFINAR WF WFSC CONS : event ↑ (RF^? ⨾ SB^? ⨾ FWBOB) ⊆ ar⁺.
  Proof using.
    rewrite !collect_rel_seq, !collect_rel_cr.
    rewrite ERF, eSB_in_sb_sc_ct, EFWBOB. rewrite cr_of_cr.
    rewrite cr_of_ct. apply rf_sb_sc_rt_sb_fwbob_in_ar; auto.
    apply CONS.
  Qed.

  Lemma FWBOB_SBRF_acyc WF WFSC COMP CONS : acyclic (FWBOB ⨾ (SB ∪ RF)⁺).
  Proof using.
    rewrite acyclic_seqC.
    rewrite path_ut2; auto with lbase.
    rewrite ct_of_trans; auto with lbase.
    repeat (rewrite rt_of_trans; auto with lbase).
    arewrite (SB^? ⨾ (RF ⨾ SB)^? ⨾ RF ⊆ RF).
    { rewrite !crE, !seq_union_l, !seqA.
      rewrite !seq_union_r, !seq_id_l.
      rewrite SBRF.
      clear; basic_solver 1. }
    rewrite acyclic_seqC.
    rewrite !seq_union_r.
    rewrite FWBOBSB, union_false_l.
    rewrite acyclic_seqC, !seqA.
    rewrite RFSBFWBOBINAR; auto.
    apply AR_acyc; auto.
  Qed.

  Local Hint Resolve RFSBFWBOBINAR FWBOB_SBRF_acyc : lbase.

  Lemma SBRFFWBOB_acyc WF WFSC COMP CONS : acyclic (SB ∪ RF ∪ FWBOB).
  Proof using.
    apply acyclic_ut; splits; auto with lbase.
  Qed.

  Local Hint Resolve SBRFFWBOB_acyc : lbase.
  
  Lemma iord_acyclic WF WFSC COMP CONS : acyclic iord.
  Proof using.
    assert (transitive sb) as SBTRANS.
    { apply sb_trans. }

    red. unfold "iord".
    apply acyclic_restr.
    apply acyclic_ut; splits; auto with lbase.
    2: { rewrite ct_begin.
         arewrite (PROP ⨾ (SB ∪ RF ∪ FWBOB ∪ AR ∪ IPROP) ⊆ ∅₂).
         { iord_dom_solver. }
         rewrite seq_false_l.
         apply false_acyclic. }
    apply acyclic_ut; splits; auto with lbase.
    2: { rewrite ct_begin.
         arewrite (IPROP ⨾ (SB ∪ RF ∪ FWBOB ∪ AR) ⊆ ∅₂).
         { iord_dom_solver. }
         rewrite seq_false_l.
         apply false_acyclic. }

    apply acyclic_ut; splits; auto with lbase.
    rewrite acyclic_seqC.
    rewrite unionA, unionC.
    arewrite (FWBOB ⊆ SB^? ⨾ FWBOB).
    { clear. basic_solver 10. }

    rewrite path_absorb.
    2: { left. rewrite seq_union_r.
         rewrite SBRF, union_false_l.
         unionR right.
         hahn_frame_r.
         rewrite rewrite_trans_seq_cr_r; eauto with hahn lbase. }
    arewrite (SB⁺ ⊆ SB).
    { apply ct_of_trans; auto with lbase. }
    rewrite !seq_union_l, !seqA. rewrite !SBAR.
    rewrite seq_false_r, !union_false_r.
    rewrite path_union, !seq_union_l.
    arewrite (RF⁺ ⊆ RF).
    { apply ct_of_trans; auto with lbase. }
    rewrite RFAR, !union_false_l.
    rewrite rt_of_trans; auto with lbase.
    arewrite (RF^? ⨾ AR ⊆ AR).
    { rewrite crE, !seq_union_l, !seq_id_l. rewrite RFAR.
      clear; basic_solver 1. }

    eapply collect_rel_acyclic with (f:=event).
    rewrite collect_rel_seq, collect_rel_ct.
    rewrite RFSBFINAR; auto. rewrite ct_of_ct.
    rewrite EAR.
    arewrite (ar ⊆ ar ∪ rf ⨾ ppo ∩ same_loc) at 1.
    rewrite ct_ct. red. rewrite ct_of_ct.
    apply ar_rf_ppo_loc_acyclic; auto.
  Qed.
  
  Lemma SB_fsupp WF WFSC CONS
        (FSUPPSC : fsupp sc)
    : fsupp (restr_rel (event ↓₁ (E \₁ is_init)) SB).
  Proof using.
    assert (FSUPPSB : fsupp (<|set_compl is_init|> ⨾ sb)).
    { now apply fsupp_sb. }
    unfold "SB". rewrite inclusion_t_rt.
    rewrite sb_sc_rt; auto; try apply CONS.
    rewrite restr_seq_eqv_l.
    arewrite_id ⦗action ↓₁ eq ta_cover⦘ at 2.
    rewrite seq_id_r.
    rewrite <- map_rel_restr.
    apply fsupp_seq_l_map_rel; auto with lbase.
    rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l, !seq_id_r.
    rewrite restr_relE.
    arewrite_id ⦗E \₁ is_init⦘ at 2.
    rewrite !seq_id_r.
    arewrite (E \₁ is_init ⊆₁ set_compl is_init).
    { clear; basic_solver. }
    rewrite rewrite_trans; eauto using sb_trans.
    arewrite (sc ⨾ sb ⊆ sc ⨾ ⦗set_compl is_init⦘ ⨾ sb).
    { rewrite (dom_r (wf_scD WFSC)) at 1.
      arewrite (F ∩₁ Sc ⊆₁ set_compl is_init); [|easy].
      rewrite (init_w WF). clear. mode_solver. }
    rewrite !seq_union_r, !seq_id_r.
    assert (fsupp ⦗set_compl is_init⦘) as AA.
    { now apply fsupp_eqv. }
    assert (fsupp (⦗set_compl is_init⦘ ⨾ sc)) as BB.
    { apply fsupp_seq; auto. }

    repeat apply fsupp_union; auto.
    { rewrite <- !seqA. rewrite seqA.
      apply fsupp_seq; auto. }
    { rewrite <- !seqA. apply fsupp_seq; auto. }
    rewrite <- !seqA. rewrite seqA.
    repeat (apply fsupp_seq; auto).
  Qed.

  Lemma RF_fsupp (FSUPPRF : fsupp rf) :
    fsupp RF.
  Proof using.
    unfold "RF".
    arewrite_id ⦗action ↓₁ eq ta_cover⦘. rewrite seq_id_r.
    apply fsupp_seq_l_map_rel; auto with lbase.
    arewrite_id ⦗W⦘. rewrite !seq_id_l.
    now apply fsupp_cr.
  Qed.
  
  Lemma AR_fsupp WF WFSC MF CONS COMP
        (IMM_FAIR: imm_s_fair G sc):
    fsupp (⦗event ↓₁ (set_compl is_init)⦘ ⨾ AR).
  Proof using.
    unfold "AR". seq_rewrite seq_eqvC. rewrite seqA. 
    rewrite <- seqA with (r2 := event ↓ _).
    rewrite map_rel_eqv with (f := event), map_rel_seq.  
    arewrite_id ⦗action ↓₁ eq ta_issue⦘ at 2. rewrite seq_id_r.
    apply fsupp_seq_l_map_rel; auto with lbase.
    eapply fsupp_mori.
    2: { eapply fsupp_ar_implies_fsupp_ar_rf_ppo_loc; eauto. }
    red. basic_solver 10. 
  Qed.
  
  Lemma FWBOB_fsupp WF : fsupp (restr_rel (event ↓₁ (E \₁ is_init)) FWBOB).
  Proof using.
    assert (FSUPPSB : fsupp (<|set_compl is_init|> ⨾ sb)).
    { now apply fsupp_sb. }
    unfold "FWBOB".
    arewrite_id ⦗action ↓₁ eq ta_issue⦘.
    arewrite_id ⦗W⦘.
    rewrite !seq_id_r.
    rewrite restr_seq_eqv_l.
    rewrite restr_relE, <- !seqA.
    apply fsupp_seq; auto using fsupp_eqv.
    rewrite map_rel_eqv with (f:=event).
    rewrite !seqA. rewrite map_rel_seq.
    apply fsupp_seq_l_map_rel; auto with lbase.
    rewrite fwbob_in_sb.
    arewrite (E \₁ is_init ⊆₁ set_compl is_init); auto.
    clear; basic_solver.
  Qed.
  
  Lemma IPROP_fsupp : fsupp IPROP.
  Proof using.
    unfold "IPROP". 
    rewrite <- seqA.
    apply fsupp_seq; auto using fsupp_eqv.
    apply fsupp_seq_l_map_rel; auto with lbase.
    repeat (apply fsupp_seq); auto using fsupp_eqv.
    red; ins. exists [y]; ins; eauto.
  Qed.

  Lemma PROP_fsupp WF MF CONS COMP (IMM_FAIR: imm_s_fair G sc)
    : fsupp (⦗event ↓₁ (set_compl is_init)⦘ ⨾ PROP).
  Proof using.
    assert (FSUPPSBCR : fsupp (⦗set_compl is_init⦘ ⨾ sb^?)).
    { rewrite crE, seq_union_r.
      apply fsupp_union; auto using fsupp_seq, fsupp_eqv, fsupp_sb. }

    assert (fsupp (⦗set_compl is_init⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)＊)) as FSUPPAR.
    { rewrite rtE, seq_union_r. apply fsupp_union; auto using fsupp_seq, fsupp_eqv.
      eapply fsupp_ar_implies_fsupp_ar_rf_ppo_loc; eauto. }

    unfold "PROP".
    rewrite inclusion_inter_l1.
    arewrite_id ⦗W⦘.
    arewrite_id ⦗action ↓₁ is_ta_propagate_to_G G⦘.
    rewrite !seq_id_r.
    rewrite <- !seqA.
    rewrite seq_eqvC, !seqA.
    rewrite map_rel_eqv with (f := event), map_rel_seq.  
    apply fsupp_seq_l_map_rel; auto with lbase.
    rewrite <- !seqA. apply fsupp_seq.
    2: { apply fsupp_cr. apply MF. }
    sin_rewrite no_sb_cr_to_init.
    rewrite !seqA, <- seqA. apply fsupp_seq; auto.
    sin_rewrite no_ar_rfppo_rt_to_init; auto.
    rewrite !seqA, <- seqA. apply fsupp_seq; auto.
  Qed.

  Local Hint Resolve SB_fsupp RF_fsupp FWBOB_fsupp AR_fsupp IPROP_fsupp PROP_fsupp : lbase.

  Lemma iord_fsupp WF WFSC MF CONS COMP
        (IMM_FAIR: imm_s_fair G sc):
    fsupp (⦗event ↓₁ (set_compl is_init)⦘ ⨾ iord).
  Proof using.
    assert (FSUPPRF : fsupp rf).
    { now apply fsupp_rf. }
    assert (FSUPPSC : fsupp sc).
    { eapply imm_s_fair_fsupp_sc; eauto. }
    unfold "iord". rewrite !restr_union, !seq_union_r. 
    repeat (apply fsupp_union).
    6: { eapply fsupp_mori; [| apply PROP_fsupp]; auto. red. basic_solver. }
    4: { eapply fsupp_mori; [| apply AR_fsupp]; auto. red. basic_solver. }
    all: apply fsupp_seq; [by apply fsupp_eqv| ].
    1, 3: by auto using SB_fsupp, FWBOB_fsupp. 
    all: apply fsupp_restr; auto using RF_fsupp, IPROP_fsupp.
  Qed.

  Lemma no_RF_to_init_weak WF:
    ⦗event ↓₁ set_compl is_init⦘ ⨾ RF ≡ ⦗event ↓₁ set_compl is_init⦘ ⨾ RF ⨾ ⦗event ↓₁ set_compl is_init⦘. 
  Proof using.
    split; [| basic_solver]. rewrite <- seqA. apply domb_helper. 
    unfold "RF". rewrite crE. repeat case_union _ _.
    rewrite map_rel_union. repeat case_union _ _.
    apply union_domb.
    { unfolder. ins. desc. congruence. }
    rewrite no_rf_to_init; auto. basic_solver.
  Qed. 

  Lemma no_AR_to_init WF CONS:
    AR ≡ AR ⨾ ⦗event ↓₁ set_compl is_init⦘. 
  Proof using.
    split; [| basic_solver]. apply domb_helper. 
    forward eapply no_ar_rf_ppo_loc_to_init as AR'_NI; eauto.
    apply seq_eqv_compl in AR'_NI. unfold "AR". rewrite AR'_NI.
    rewrite ct_end. basic_solver.
  Qed. 

  Lemma no_PROP_to_init WF CONS :
     ⦗event ↓₁ set_compl is_init⦘ ⨾ PROP ≡
     ⦗event ↓₁ set_compl is_init⦘ ⨾ PROP ⨾ ⦗event ↓₁ set_compl is_init⦘. 
  Proof using.
    split; [| basic_solver].
    rewrite <- !seqA.
    apply domb_helper.
    unfold "PROP".
    rewrite inclusion_inter_l1.
    arewrite_id ⦗action ↓₁ eq ta_cover⦘.
    arewrite_id ⦗action ↓₁ is_ta_propagate_to_G G⦘.
    arewrite_id ⦗W⦘.
    rewrite !seq_id_l, !seq_id_r.
    rewrite map_rel_eqv, map_rel_seq.
    sin_rewrite no_sb_cr_to_init. rewrite !seqA.
    sin_rewrite no_ar_rfppo_rt_to_init; auto. rewrite !seqA.
    arewrite_id ⦗set_compl (fun a : actid => is_init a)⦘ at 1.
    sin_rewrite no_sb_cr_to_init. rewrite !seqA.

    assert (SPL : Execution_eco.sc_per_loc G).
    { apply imm_s_hb.coherence_sc_per_loc. apply CONS. }
    sin_rewrite no_co_cr_to_init; auto.
    rewrite <- !map_rel_seq2; auto using event_surj.
    repeat apply seq_domb.
    iord_dom_solver.
  Qed.

  Lemma seq_eqv_l_trans {A: Type} (r: relation A) (s: A -> Prop)
        (TRANS: transitive r):
    transitive (⦗s⦘ ⨾ r).
  Proof using.
    red. intros ? ? ? ?%seq_eqv_l ?%seq_eqv_l. desc.
    apply seq_eqv_l. split; auto. eapply TRANS; eauto.
  Qed.

  Lemma iord_ct_fsupp WF WFSC COMP MF CONS
        (FAIR: mem_fair G)
        (IMM_FAIR: imm_s_fair G sc):
    fsupp (⦗event ↓₁ (set_compl is_init)⦘ ⨾ iord⁺).
  Proof using.
    forward eapply fsupp_ar_implies_fsupp_ar_rf_ppo_loc as FS_AR_RFPPOL; eauto.
    assert (transitive sb) as SBTRANS.
    { apply sb_trans. }
    assert (FSUPPSB : fsupp (<|set_compl is_init|> ⨾ sb)).
    { now apply fsupp_sb. }
    assert (FSUPPRF : fsupp rf).
    { now apply fsupp_rf. }
    assert (FSUPPSC : fsupp sc).
    { eapply imm_s_fair_fsupp_sc; eauto. }

    unfold "iord".
    rewrite !restr_union.
    remember
      (restr_rel (event ↓₁ (E \₁ (fun a : actid => is_init a)))
                 SB) as rSB.
    remember
      (restr_rel (event ↓₁ (E \₁ (fun a : actid => is_init a)))
                 FWBOB) as rFWBOB.
    rewrite !inclusion_restr.

    assert (transitive rFWBOB) as TRFWBOB.
    { subst rFWBOB. apply transitive_restr.
      auto with lbase. }

    assert (rSB ∪ RF ⊆ RF^? ⨾ rSB^?) as SBRFT.
    { rewrite crE. clear; basic_solver 10. }

    assert (fsupp rSB) as FSUPPRSB.
    { subst rSB; auto with lbase. }
    assert (fsupp rSB^?) as FSUPPRSBCR.
    { now apply fsupp_cr. }

    assert (fsupp rFWBOB) as FSUPPRFWBOB.
    { subst rFWBOB; auto with lbase. }

    assert (transitive rSB) as TRSB.
    { subst rSB. apply transitive_restr. auto with lbase. }
    
    assert (rSB ⨾ RF ⊆ ∅₂) as RSBRF.
    { arewrite (rSB ⊆ SB); auto with lbase.
      subst rSB. apply inclusion_restr. }

    assert (fsupp (rSB ∪ RF)＊) as SRA.
    { rewrite SBRFT. rewrite rt_of_trans; auto.
      { apply fsupp_cr. apply fsupp_seq; auto.
        all: apply fsupp_cr; auto with lbase. }
      apply transitiveI. rewrite !seqA.
      rewrite !crE, !seq_union_l, !seq_union_r.
      rewrite !seq_id_l,  !seq_id_r.
      sin_rewrite !RFRF.
      sin_rewrite !rewrite_trans; auto with lbase.
      sin_rewrite !RSBRF.
      unionL; eauto with hahn.
      all: clear; basic_solver 1. }

    assert (rFWBOB ⨾ rSB ⊆ ∅₂) as RFWBOBSB.
    { subst rFWBOB rSB. rewrite !inclusion_restr. auto with lbase. }

    assert (transitive (RF ⨾ rSB)) as TRFRSB.
    { apply transitiveI. rewrite !seqA. sin_rewrite RSBRF.
      clear; basic_solver 1. }

    assert (rSB^? ⨾ RF ⊆ RF) as RSBCRRF.
    { rewrite crE, !seq_union_l, seq_id_l.
      rewrite RSBRF. now rewrite union_false_r. }

    assert (transitive (RF^? ⨾ rSB^?)) as TRFSBCR.
    { apply transitiveI. rewrite !seqA.
      rewrite crE, !seq_union_l, !seq_union_r, !seq_id_l.
      arewrite (rSB^? ⨾ rSB^? ⊆ rSB^?).
      { apply transitiveI. now apply transitive_cr. }
      sin_rewrite !RSBCRRF.
      sin_rewrite !RFRF.
      unionL; eauto with hahn. clear; basic_solver 1. }

    assert (rFWBOB ⨾ (rSB ∪ RF)⁺ ⊆ rFWBOB ⨾ RF ⨾ rSB^?) as FWBOBSBRF.
    { rewrite ct_begin. rewrite path_ut; auto with lbase.
      arewrite (rFWBOB ⨾ (rSB ∪ RF) ⊆ rFWBOB ⨾ RF).
      { rewrite seq_union_r.
        rewrite RFWBOBSB.
        unionL; eauto with hahn.
        clear; basic_solver 1. }
      rewrite ct_of_trans; auto with lbase.
      rewrite !rt_of_trans; auto with lbase.
      rewrite !crE, !seq_union_r, !seq_union_l, !seq_union_r, !seq_id_r, !seq_id_l.
      sin_rewrite !RSBRF.
      sin_rewrite !RFRF.
      rewrite !seq_false_l, !seq_false_r.
      rewrite !union_false_l, !union_false_r.
      rewrite !seqA.
      sin_rewrite !RFRF.
      rewrite !seq_false_l, !seq_false_r.
      sin_rewrite !RSBRF.
      rewrite !seq_false_l, !seq_false_r.
      now rewrite !union_false_r. }

    assert (fsupp (⦗event ↓₁ set_compl is_init⦘ ⨾ AR^?)) as FARCR.
    { rewrite crE, seq_union_r.
      apply fsupp_union; [rewrite <- id_inter; by apply fsupp_eqv| ].
      auto with lbase. }

    assert (rSB ⊆ SB) as RSBIN.
    { subst rSB. apply inclusion_restr. }
    assert (rFWBOB ⊆ FWBOB) as RFWBOBIN.
    { subst rFWBOB. apply inclusion_restr. }

    assert (rFWBOB ⊆ rFWBOB ⨾ ⦗event ↓₁ set_compl is_init⦘) as FWB_NI.
    { subst rFWBOB. basic_solver. }

    assert (fsupp (⦗event ↓₁ set_compl is_init⦘ ⨾ (rSB ∪ RF ∪ rFWBOB))⁺) as FSRFW.
    { rewrite !seq_union_r.
      rewrite inclusion_seq_eqv_l with (r := RF), inclusion_seq_eqv_l with (r := rFWBOB).
      apply fsupp_rt_ct.      
      rewrite path_ut; auto.
      repeat apply fsupp_seq.
      3: now apply fsupp_cr.
      { eapply fsupp_mori; [| by apply SRA]. red.
        apply clos_refl_trans_mori. basic_solver. }
      rewrite inclusion_seq_eqv_l. 
      
      rewrite FWBOBSBRF.
      apply fsupp_ct_rt.
      rewrite ct_rotl, !seqA.
      rewrite rtE. repeat case_union _ _. apply fsupp_union.
      { repeat (apply fsupp_seq; auto with lbase). apply fsupp_eqv. } 
      rewrite FWB_NI, seqA at 1. rewrite <- seqA with (r1 := ⦗_⦘).
      rewrite clos_trans_domb_l; [| rewrite FWB_NI; basic_solver].
      repeat (apply fsupp_seq; auto with lbase).
      rewrite RSBIN, RFWBOBIN.
      rewrite RFSBFWBOBINAR; auto.
      eapply fsupp_mori; [| by apply FARCR].
      red. rewrite ct_of_trans; [basic_solver| ].
      rewrite <- restr_relE. apply transitive_restr, AR_trans. }
    
    assert (RF ⨾ rSB^? ⨾ rFWBOB ⊆ AR) as RRFSBFWBOBINAR.
    { rewrite RSBIN, RFWBOBIN; auto with lbase. }

    assert (PROP ⨾ (rSB ∪ RF ∪ rFWBOB ∪ AR ∪ IPROP) ⊆ ∅₂) as PROPIORDSTEP.
    { subst. clear. iord_dom_solver. }
    assert (PROP ⨾ (rSB ∪ RF ∪ rFWBOB ∪ AR ∪ IPROP)⁺ ⊆ ∅₂) as PROPIORD.
    { rewrite ct_begin. sin_rewrite PROPIORDSTEP. clear; basic_solver 1. }

    rewrite clos_trans_domb_l_strong. 
    2: { subst rSB rFWBOB. unfold "IPROP". rewrite !seq_union_r.
         repeat apply union_domb; try (clear; basic_solver). 
         { rewrite no_RF_to_init_weak; auto. basic_solver. }
         { rewrite no_AR_to_init; auto. basic_solver. }  
         { iord_dom_solver. }
         rewrite no_PROP_to_init; auto. clear. basic_solver. }

    apply fsupp_rt_ct. 
    rewrite <- seqA. rewrite inclusion_seq_eqv_r. repeat case_union _ _ .
                  
    rewrite path_ut; auto with lbase.
    2: { apply seq_eqv_l_trans; auto with lbase. }
    rewrite <- !seq_union_r. 
    repeat apply fsupp_seq.
    3: now auto using fsupp_cr with lbase.
    2: { rewrite inclusion_eqv_rel_true, !seq_id_l.
         rewrite PROPIORD. rewrite empty_rt. auto using fsupp_eqv. }

    assert (IPROP ⨾ (rSB ∪ RF ∪ rFWBOB ∪ AR) ⊆ ∅₂) as IPROPIORDSTEP.
    { subst. clear. iord_dom_solver. }
    assert (IPROP ⨾ (rSB ∪ RF ∪ rFWBOB ∪ AR)⁺ ⊆ ∅₂) as IPROPIORD.
    { rewrite ct_begin. sin_rewrite IPROPIORDSTEP. clear; basic_solver 1. }
    
    rewrite seq_union_r.
    rewrite path_ut; auto with lbase.
    2: { apply seq_eqv_l_trans; auto with lbase. }
    rewrite <- !seqA. apply fsupp_seq.
    2: now auto using fsupp_cr, fsupp_seq, fsupp_eqv with lbase.
    apply fsupp_seq.
    2: { rewrite inclusion_eqv_rel_true, !seq_id_l.
         rewrite IPROPIORD. rewrite empty_rt. auto using fsupp_eqv. }

    rewrite rtE, seq_union_r.
    apply fsupp_union; eauto using fsupp_seq, fsupp_eqv.

    apply fsupp_rt_ct.
    rewrite path_ut; auto with lbase.
    2: { apply seq_eqv_l_trans; auto with lbase. }
    repeat apply fsupp_seq.
    3: now apply fsupp_cr; auto with lbase.
    { now apply fsupp_ct_rt. }
    apply fsupp_ct_rt.
    rewrite ct_rotl.
    repeat (apply fsupp_seq; auto with lbase).
    rewrite ct_end, !seqA.
    rewrite inclusion_seq_eqv_l with (r := AR). 
    arewrite ((rSB ∪ RF ∪ rFWBOB) ⨾ AR ⊆ rFWBOB ⨾ AR).
    { rewrite !seq_union_l.
      rewrite RSBIN, SBAR, RFAR.
      now rewrite !union_false_l. }
    repeat case_union _ _. remember (event ↓₁ set_compl is_init) as ENI.

    rewrite path_ut; auto.
    2: { apply seq_eqv_l_trans; auto with lbase. }
    rewrite !seqA.
    rewrite <- seqA with (r3 := AR). sin_rewrite rewrite_trans_seq_cr_l; auto.
    2: { apply seq_eqv_l_trans; auto with lbase. }
    rewrite inclusion_seq_eqv_l with (r := rSB) at 2. 
    rewrite inclusion_seq_eqv_l with (r := RF) at 2.
    rewrite <- seqA with (r2 := rFWBOB). 
    rewrite !inclusion_seq_eqv_l with (r := rFWBOB). 
    rewrite FWBOBSBRF.
    arewrite ((rFWBOB ⨾ RF ⨾ rSB^?)＊ ⨾ rFWBOB ⨾ AR ⊆ rFWBOB ⨾ AR).
    { rewrite rtE with (r:=rFWBOB ⨾ RF ⨾ rSB^?).
      rewrite seq_union_l, seq_id_l. unionL; eauto with hahn.
      rewrite ct_rotl, !seqA.
      sin_rewrite !RRFSBFWBOBINAR.
      hahn_frame_l. seq_rewrite <- ct_end.
      rewrite ct_unit. apply ct_of_trans; auto with lbase. }

    eapply fsupp_mori.
    { red. apply clos_refl_trans_mori. apply doma_rewrite with (d := ENI).
      rewrite rtE. repeat case_union _ _. apply union_doma.
      { subst rFWBOB. basic_solver. }
      rewrite ct_begin. basic_solver. }
    rewrite (@inclusion_seq_eqv_l _ rSB). rewrite (@inclusion_seq_eqv_l _ RF).

    arewrite ((rSB ∪ RF)＊ ⨾ rFWBOB ⊆ RF^? ⨾ rSB^? ⨾ rFWBOB).
    { rewrite SBRFT. rewrite rt_of_trans; auto.
      rewrite cr_seq, !seqA.
      unionL; eauto with hahn.
      clear. basic_solver 10. }

    rewrite crE, !seq_union_l, seq_id_l.
    sin_rewrite RRFSBFWBOBINAR.
    rewrite rewrite_trans; auto with lbase.
    rewrite rt_of_trans.
    { case_union _ _. subst ENI. 
      apply fsupp_cr, fsupp_union; auto with lbase.
      rewrite FWB_NI. rewrite seqA. rewrite <- seqA with (r2 := rSB^?). 
      repeat (apply fsupp_seq; auto with lbase). apply fsupp_eqv. }

    apply seq_eqv_l_trans. 

    assert (AR ⨾ rFWBOB ⊆ ∅₂) as ARFWBOB.
    { subst. unfold "AR", "FWBOB". iord_dom_solver. }
    assert (AR ⨾ rSB ⊆ ∅₂) as ARSB.
    { subst. unfold "AR", "SB".  iord_dom_solver. }

    assert (AR ⨾ rSB^? ⨾ rFWBOB ⊆ ∅₂) as ARSBFW.
    { rewrite crE, !seq_union_l, !seq_union_r, !seq_id_l.
      rewrite ARFWBOB. sin_rewrite ARSB.
      clear; basic_solver 1. }
    apply transitiveI.
    rewrite !seq_union_r, !seq_union_l, !seqA.
    unionL.
    { sin_rewrite ARSBFW. clear; basic_solver 1. }
    { sin_rewrite ARSBFW. clear; basic_solver 1. }
    all: rewrite rewrite_trans; eauto with hahn lbase.
  Qed.
        
End TravLabel.

(* Global Ltac iord_dom_solver := *)
(*   unfold SB, RF, FWBOB, AR, PROP, IPROP; *)
(*   unfold is_ta_propagate_to_G in *; *)
(*   clear; unfolder; intros [a b] [c d]; ins; desc; *)
(*   (try match goal with *)
(*        | z : trav_label |- _ => destruct z; desf; ins; desf *)
(*        end); *)
(*   desf. *)

Global Add Parametric Morphism : SB with signature
       eq ==> same_relation ==> same_relation as SB_more.
Proof using.
  intros G r r' EQ.
  unfold SB. rewrite EQ; eauto.
Qed.

(* TODO: move to ... *)
Global Add Parametric Morphism : ar with signature
       eq ==> same_relation ==> same_relation as ar_more.
Proof using.
  intros G r r' EQ.
  now unfold ar; rewrite EQ.
Qed.

Global Add Parametric Morphism : AR with signature
       eq ==> same_relation ==> same_relation as AR_more.
Proof using.
  intros G r r' EQ.
  unfold AR. now rewrite EQ.
Qed.

Global Add Parametric Morphism : PROP with signature
       eq ==> same_relation ==> same_relation as PROP_more.
Proof using.
  intros G r r' EQ.
  unfold PROP. now rewrite EQ.
Qed.

Global Add Parametric Morphism : iord with signature
       eq ==> same_relation ==> same_relation as iord_more.
Proof using.
  intros G r r' EQ.
  unfold iord.
  apply restr_rel_more; eauto.
  now rewrite EQ.
Qed.

  
(* TODO: move to lib *)
Lemma set_pair_alt {A B: Type} (Sa: A -> Prop) (Sb: B -> Prop ):
  Sa <*> Sb ≡₁ (fst ↓₁ Sa) ∩₁ (snd ↓₁ Sb). 
Proof using. unfold set_pair. basic_solver. Qed.

(* TODO: move to lib *)
Global Add Parametric Morphism {A B: Type}: (@set_pair A B) with signature
       @set_equiv A ==> @set_equiv B ==> @set_equiv (A * B) as set_pair_more.
Proof using.
  ins. rewrite !set_pair_alt. rewrite H, H0. basic_solver. 
Qed.

(* TODO: move to lib *)
Global Add Parametric Morphism {A B: Type}: (@set_pair A B) with signature
       @set_subset A ==> @set_subset B ==> @set_subset (A * B) as set_pair_mori.
Proof using.
  ins. rewrite !set_pair_alt. rewrite H, H0. basic_solver. 
Qed.

(* TODO: move to lib *)
Lemma eqv_rel_alt {A: Type} (S: A -> Prop):
  ⦗S⦘ ≡ S × S ∩ eq.
Proof using. basic_solver. Qed.

(* TODO: move to lib *)
Lemma doma_alt {A: Type} (r: relation A) (d: A -> Prop):
  doma r d <-> dom_rel r ⊆₁ d. 
Proof using. unfolder. split; ins; basic_solver. Qed. 

(* TODO: move to lib *)  
Lemma map_rel_seq_insert_exact {A B: Type} (r1 r2: relation B)
      (f: A -> B) (d: A -> Prop)
      (SUR_D: forall b, exists a, f a = b /\ d a):
  f ↓ (r1 ⨾ r2) ⊆ f ↓ r1 ⨾ ⦗d⦘ ⨾ f ↓ r2. 
Proof using.
  unfolder. ins. desc.
  specialize (SUR_D z). desc. eexists. splits; eauto; congruence. 
Qed. 


(* TODO: move to lib *)  
Lemma rel_map_bunionC {A B C: Type} (f: A -> B)
      (cdom: C -> Prop) (ss: C -> relation B):
  f ↓ (⋃ c ∈ cdom, ss c) ≡ (⋃ c ∈ cdom, f ↓ (ss c)).
Proof using. basic_solver. Qed. 

(* TODO: move to lib *)  
Lemma dom_rel_bunion {B C: Type}
      (cdom: C -> Prop) (ss: C -> relation B):
  dom_rel (⋃ c ∈ cdom, ss c) ≡₁ (⋃₁ c ∈ cdom, dom_rel (ss c)).
Proof using. basic_solver. Qed.

(* TODO: move to lib *)  
Lemma restr_rel_seq_same {A: Type} (r1 r2: relation A) (d: A -> Prop)
      (DOMB1: domb (⦗d⦘ ⨾ r1) d):
  restr_rel d (r1 ⨾ r2) ≡ restr_rel d r1 ⨾ restr_rel d r2. 
Proof using.
  split; [| apply restr_seq].
  unfolder. unfolder in DOMB1. ins. desc.
  eexists. splits; eauto.
Qed. 

(* TODO: move to lib *)
Global Add Parametric Morphism
       {A: Type} (r: relation (A -> Prop)):
  r with signature
       @set_equiv A ==> @set_equiv A ==> iff as set_equiv_rel_more. 
Proof using. ins. apply set_extensionality in H, H0. by subst. Qed.

(* TODO: move to lib? *)
Lemma set_subset_inter_exact {A: Type} (s s': A -> Prop):
  s ⊆₁ s' <-> s ⊆₁ s ∩₁ s'. 
Proof using.
  split; [basic_solver| ]. ins.
  red. ins. by apply H. 
Qed.  

(* TODO: move to lib *)
Lemma set_collect_map_ext [A B : Type] [f : A -> B] [d : B -> Prop]
      (SUR: forall b, exists a, f a = b):
  f ↑₁ (f ↓₁ d) ≡₁ d. 
Proof.
  ins. split; [apply set_collect_map| ]. 
  unfolder. ins.
  specialize (SUR x) as [a Fa]. exists a. split; congruence. 
Qed.
 
(* TODO: move *)
Lemma restr_rel_cross_inter {A: Type} (d1 d2 d: A -> Prop):
  (d1 ∩₁ d) × (d2 ∩₁ d) ≡ restr_rel d (d1 × d2).
Proof using. basic_solver. Qed. 

