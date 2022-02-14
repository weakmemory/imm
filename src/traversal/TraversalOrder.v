Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import Lia.

Require Import Events.
Require Import Execution.
Require Import imm_bob.
Require Import imm_s.
Require Import imm_s_ppo.
Require Import imm_s_rfppo.
Require Import TraversalConfig.
Require Import Traversal.
Require Import TraversalConfigAlt.
Require Import AuxDef.
Require Import SetSize.
Require Import FairExecution.
Require Import ImmFair.
Require Import AuxRel2.
Import ListNotations.

Set Implicit Arguments.

Module TravAction.
  Inductive t := cover | issue.

  Definition get (TC : trav_config) ta :=
    match ta with
    | cover => covered TC
    | issue => issued TC
    end.
End TravAction. 

Module TravLabel.
  Record t :=
    mkTL {
        action : TravAction.t;
        event  : actid;
      }.

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

  Definition SB :=
    ⦗action ↓₁ (eq TravAction.cover)⦘
      ⨾ (event ↓ (sb ∪ sc)⁺)
      ⨾ ⦗action ↓₁ (eq TravAction.cover)⦘.
         
  Definition RF :=
    ⦗action ↓₁ (eq TravAction.issue)⦘
      ⨾ (event ↓ (⦗W⦘ ⨾ rf^?))
      ⨾ ⦗action ↓₁ (eq TravAction.cover)⦘.

  Definition FWBOB :=
    ⦗action ↓₁ (eq TravAction.cover)⦘
      ⨾ (event ↓ (fwbob ⨾ ⦗W⦘))
      ⨾ ⦗action ↓₁ (eq TravAction.issue)⦘.

  Definition AR :=
    ⦗action ↓₁ (eq TravAction.issue)⦘
      ⨾ (event ↓ (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗W⦘))
      ⨾ ⦗action ↓₁ (eq TravAction.issue)⦘.
  
  (* Essentially, it is an alternative representation of a part of tc_coherent *)
  Definition iord : relation t :=
    restr_rel (event ↓₁ (E \₁ is_init))
              (SB ∪ RF ∪ FWBOB ∪ AR).

  Lemma iord_irreflexive WF COMP WFSC CONS : irreflexive iord.
  Proof using.
    assert (transitive sc) as TSC.
    { now apply WFSC. }
    assert (transitive sb) as TSB.
    { apply sb_trans. }

    unfold iord, SB, RF, FWBOB, AR.
    apply irreflexive_restr.
    repeat (apply irreflexive_union; splits).
    2-4: unfolder; intros [y z]; ins; desf; eauto.
    2: now eapply ar_rf_ppo_loc_acyclic; eauto.
    rewrite <- restr_relE.
    apply irreflexive_restr.
    apply map_rel_irr.
    apply sb_sc_acyclic; auto.
    apply CONS.
  Qed.
  
  Lemma AR_trans : transitive AR.
  Proof using.
    unfold AR.
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
    unfold AR.
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
  
  Local Ltac iord_dom_solver :=
    unfold SB, RF, FWBOB, AR;
    clear; unfolder; intros [a b] [c d]; ins; desc;
    (try match goal with
        | z : t |- _ => destruct z; desf; ins; desf
        end);
    desf.
  
  Lemma SBRF : SB ⨾ RF ⊆ ∅₂.
  Proof using. iord_dom_solver. Qed.
  
  Lemma SBAR : SB ⨾ AR ⊆ ∅₂.
  Proof using. iord_dom_solver. Qed.

  Lemma RFAR : RF ⨾ AR ⊆ ∅₂.
  Proof using. iord_dom_solver. Qed.

  Lemma RFRF : RF ;; RF ⊆ ∅₂.
  Proof using. iord_dom_solver. Qed.
  
  Lemma RF_trans : transitive RF.
  Proof using. iord_dom_solver. Qed.

  Lemma RF_irr : irreflexive RF.
  Proof using. iord_dom_solver. Qed.

  Local Hint Resolve SBRF SBAR RFAR RFRF RF_trans RF_irr : lbase.

  Lemma eSB_in_sb_sc_ct : event ↑ SB ⊆ (sb ∪ sc)⁺.
  Proof using. unfold SB. clear. basic_solver 10. Qed.

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
    unfold SB.
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

  Lemma FWBOBFWBOB : FWBOB ;; FWBOB ⊆ ∅₂.
  Proof using. iord_dom_solver. Qed.

  Local Hint Resolve SB_acyclic SB_trans SB_irr FWBOBFWBOB : lbase.

  Lemma FWBOB_trans : transitive FWBOB.
  Proof using.
    apply transitiveI. rewrite FWBOBFWBOB. clear; basic_solver 1.
  Qed.

  Lemma FWBOB_irr : irreflexive FWBOB.
  Proof using. iord_dom_solver. Qed.

  Local Hint Resolve FWBOB_trans FWBOB_irr : lbase.

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

  Lemma event_finite_inj y : set_finite (fun x => y = event x).
  Proof using.
    ins. exists [mkTL TravAction.issue y;
                 mkTL TravAction.cover y].
    ins. subst. destruct x as [[]]; ins; auto.
  Qed.

  Lemma event_surj y : exists x, y = event x.
  Proof using.
    ins. exists (mkTL TravAction.cover y); ins.
  Qed.

  Local Hint Resolve RFSB_trans FWBOBSB event_finite_inj event_surj : lbase.

  Lemma ERF : event ↑ RF ⊆ rf^?.
  Proof using. unfold RF. clear. basic_solver 10. Qed.
  Lemma EFWBOB : event ↑ FWBOB ⊆ fwbob.
  Proof using. unfold FWBOB. clear. basic_solver 10. Qed.
  Lemma EAR : event ↑ AR ⊆ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺.
  Proof using. unfold AR. clear. basic_solver 10. Qed.

  Lemma RFSBFWBOBINAR WF WFSC CONS : RF ⨾ SB^? ⨾ FWBOB ⊆ AR.
  Proof using.
    unfold AR, RF, FWBOB, SB.
    rewrite !seqA.
    hahn_frame.
    arewrite_id ⦗action ↓₁ eq TravAction.cover⦘. rewrite !seq_id_l, !seq_id_r.
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

    red. unfold iord.
    apply acyclic_restr.

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
    assert (FSUPPSB : fsupp (<|set_compl is_init|> ;; sb)).
    { now apply fsupp_sb. }
    unfold SB. rewrite inclusion_t_rt.
    rewrite sb_sc_rt; auto; try apply CONS.
    rewrite <- restr_relE, restrC.
    apply fsupp_restr.
    rewrite <- map_rel_restr.
    apply fsupp_map_rel; auto with lbase.
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
    repeat (apply fsupp_seq); try now apply fsupp_eqv.
    arewrite_id ⦗W⦘. rewrite !seq_id_l.
    apply fsupp_map_rel; auto with lbase.
    now apply fsupp_cr.
  Qed.
  
  Lemma AR_fsupp WF WFSC MF CONS COMP
        (* (FSUPP : fsupp (ar ∪ rf ⨾ ppo ∩ same_loc)⁺) : *)
        (IMM_FAIR: imm_s_fair G sc):
    fsupp (⦗event ↓₁ (set_compl is_init)⦘ ⨾ AR).
  Proof using.
    unfold AR. seq_rewrite seq_eqvC. rewrite seqA. 
    rewrite <- seqA with (r2 := event ↓ _).
    rewrite map_rel_eqv with (f := event), map_rel_seq.  
    repeat apply fsupp_seq; try now apply fsupp_eqv.
    apply fsupp_map_rel; auto with lbase.
    eapply fsupp_mori.
    2: { eapply fsupp_ar_implies_fsupp_ar_rf_ppo_loc; eauto. }
    red. basic_solver 10. 
  Qed.
  
  Lemma FWBOB_fsupp WF : fsupp (restr_rel (event ↓₁ (E \₁ is_init)) FWBOB).
  Proof using.
    assert (FSUPPSB : fsupp (<|set_compl is_init|> ;; sb)).
    { now apply fsupp_sb. }
    unfold FWBOB.
    arewrite_id ⦗action ↓₁ eq TravAction.cover⦘.
    arewrite_id ⦗action ↓₁ eq TravAction.issue⦘.
    arewrite_id ⦗W⦘.
    rewrite !seq_id_l, !seq_id_r.
    rewrite restr_relE, <- !seqA.
    apply fsupp_seq; auto using fsupp_eqv.
    rewrite map_rel_eqv.
    rewrite map_rel_seq.
    apply fsupp_map_rel; auto with lbase.
    rewrite fwbob_in_sb.
    arewrite (E \₁ is_init ⊆₁ set_compl is_init); auto.
    clear; basic_solver.
  Qed.

  Local Hint Resolve SB_fsupp RF_fsupp FWBOB_fsupp AR_fsupp : lbase.

  (* TODO: move to ImmFair *)
  Lemma imm_s_fair_fsupp_sc WF WFSC (IMM_FAIR: imm_s_fair G sc):
    fsupp sc. 
  Proof using. 
    eapply fsupp_mori; [| by apply IMM_FAIR].
    red. rewrite <- ct_step. unfold "ar". do 2 rewrite <- inclusion_union_r1.
    apply doma_helper. inversion WFSC. rewrite wf_scD.
    red. intros ? ? ?%seq_eqv_lr.
    eapply read_or_fence_is_not_init; eauto. type_solver. 
  Qed. 

  Lemma iord_fsupp WF WFSC MF CONS COMP
        (* (FSUPP : fsupp (ar ∪ rf ⨾ ppo ∩ same_loc)⁺)  *)
        (IMM_FAIR: imm_s_fair G sc):
    fsupp (⦗event ↓₁ (set_compl is_init)⦘ ⨾ iord).
  Proof using.
    assert (FSUPPRF : fsupp rf).
    { now apply fsupp_rf. }
    assert (FSUPPSC : fsupp sc).
    { by apply imm_s_fair_fsupp_sc. }
    unfold iord. rewrite !restr_union, !seq_union_r. 
    repeat (apply fsupp_union).
    4: { eapply fsupp_mori; [| apply AR_fsupp]; auto. red. basic_solver. }
    all: apply fsupp_seq; [by apply fsupp_eqv| ].
    1, 3: by auto using SB_fsupp, FWBOB_fsupp. 
    apply fsupp_restr. by apply RF_fsupp. 
  Qed.

  (* TODO: move to hahn / AuxRel2 *)
  Lemma clos_trans_domb_l_strong {B: Type} (r: relation B) (s: B -> Prop)
      (DOMB_S: domb (⦗s⦘ ⨾ r) s):
  ⦗s⦘ ⨾ r^+ ⊆ (⦗s⦘ ⨾ r ⨾ ⦗s⦘)^+. 
  Proof using.
    red. intros x y TT. apply seq_eqv_l in TT as [Sx R'xy].
    apply ctEE in R'xy as [n [_ Rnxy]].
    generalize dependent y. induction n.
    { ins. apply ct_step. apply seq_eqv_l in Rnxy as [_ Rnxy].
      apply seq_eqv_lr. splits; auto.
      eapply DOMB_S. basic_solver. }
    ins. destruct Rnxy as [z [Rnxz Rzy]]. specialize (IHn _ Rnxz).
    apply ct_unit. eexists. split; eauto.
    eapply same_relation_exp in IHn.
    2: { rewrite <- restr_relE. reflexivity. }
    apply clos_trans_restrD in IHn. desc. 
    apply seq_eqv_lr. splits; auto.
    eapply DOMB_S. basic_solver.
  Qed.

  Lemma no_RF_to_init_weak WF:
    ⦗event ↓₁ set_compl is_init⦘ ⨾ RF ≡ ⦗event ↓₁ set_compl is_init⦘ ⨾ RF ⨾ ⦗event ↓₁ set_compl is_init⦘. 
  Proof using.
    split; [| basic_solver]. rewrite <- seqA. apply domb_helper. 
    unfold RF. rewrite crE. repeat case_union _ _.
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
    apply seq_eqv_compl in AR'_NI. unfold AR. rewrite AR'_NI.
    rewrite ct_end. basic_solver.
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
    assert (FSUPPSB : fsupp (<|set_compl is_init|> ;; sb)).
    { now apply fsupp_sb. }
    assert (FSUPPRF : fsupp rf).
    { now apply fsupp_rf. }
    assert (FSUPPSC : fsupp sc).
    { by apply imm_s_fair_fsupp_sc. }

    unfold iord.
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

    assert (rSB ∪ RF ⊆ RF^? ;; rSB^?) as SBRFT.
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

    rewrite clos_trans_domb_l_strong. 
    2: { subst rSB rFWBOB. rewrite !seq_union_r.
         repeat apply union_domb; try basic_solver. 
         { rewrite no_RF_to_init_weak; auto. basic_solver. }
         rewrite no_AR_to_init; auto. basic_solver. }  
                  
    apply fsupp_rt_ct. 
    rewrite <- seqA. rewrite inclusion_seq_eqv_r. repeat case_union _ _ . 

    rewrite path_ut; auto with lbase.
    rewrite <- !seq_union_r. 
    repeat apply fsupp_seq.
    3: now apply fsupp_cr; auto with lbase.
    { by apply fsupp_ct_rt. }
    2: { apply seq_eqv_l_trans; auto with lbase. } 
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

    arewrite ((rSB ∪ RF)＊ ⨾ rFWBOB ⊆ RF^? ;; rSB^? ;; rFWBOB).
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
    { subst. unfold AR, FWBOB. iord_dom_solver. }
    assert (AR ⨾ rSB ⊆ ∅₂) as ARSB.
    { subst. unfold AR, SB.  iord_dom_solver. }

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

  Lemma iord_wf : well_founded iord.
  Proof using.
    
  Admitted.
  
        
End TravLabel.
