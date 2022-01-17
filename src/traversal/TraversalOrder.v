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
Require Import SimTraversal.
Require Import SimTraversalProperties.
Require Import AuxDef.

Import ListNotations.

Set Implicit Arguments.

(* TODO: move to AuxRel2.v *)
Require Import IndefiniteDescription.
Lemma fsupp_rt_ct {A} (r : relation A)
      (FSUPP : fsupp r＊) :
  fsupp r⁺.
Proof using.
  intros y. specialize (FSUPP y).
  desf. exists findom.
  ins. apply FSUPP.
  apply rtE. now right.
Qed.

(* TODO: move to AuxRel2.v *)
Lemma fsupp_wf_implies_fsupp_ct {A} (r : relation A)
      (WF    : well_founded r)
      (FSUPP : fsupp r) : 
  fsupp r⁺.
Proof using.
  apply fsupp_rt_ct.
  red; intros y.
  induction y as [y HH] using (well_founded_ind WF).
  specialize (FSUPP y). desf.
  set (f :=
         fun (a : A) =>
           match
             excluded_middle_informative (r a y)
           with
           | left  PF =>
               proj1_sig (constructive_indefinite_description _ (HH a PF))
           | right _  => nil
           end
      ).
  exists (y :: flat_map f findom).
  ins. apply rtE in REL. red in REL. desf.
  { red in REL. desf. auto. }
  right.
  apply ct_end in REL.
  destruct REL as [z [AA BB]].
  apply in_flat_map.
  exists z. splits.
  { now apply FSUPP. }
  subst f. ins. unfold proj1_sig. desf.
  intuition.
Qed.

(* TODO: move to AuxRel2.v *)
Lemma fsupp_map_rel {A B} (f : B -> A)
      (FININJ : forall y, set_finite (fun x => y = f x))
      r (FSUPP : fsupp r) :
  fsupp (map_rel f r).
Proof using.
  unfolder. ins. red in FSUPP.
  specialize (FSUPP (f y)). desf.
  set (g :=
         fun (a : A) =>
           proj1_sig
             (constructive_indefinite_description _ (FININJ a))
      ).
  exists (flat_map g findom).
  ins. apply in_flat_map.
  exists (f x). splits; auto.
  subst g. unfold proj1_sig. desf.
  intuition.
Qed.

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
           (WFSC : wf_sc G sc) (CONS : imm_consistent G sc).

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
  
  (* Essentially, it is an alternative representation of a part of tc_coherent *)
  Definition iord : relation t :=
    restr_rel (event ↓₁ (E \₁ is_init))

              (⦗action ↓₁ (eq TravAction.cover)⦘ ⨾
               (event ↓ (sb ∪ sc)) ⨾
               ⦗action ↓₁ (eq TravAction.cover)⦘
                 ∪

               ⦗action ↓₁ (eq TravAction.issue)⦘ ⨾
               (event ↓ rf^?) ⨾
               ⦗action ↓₁ (eq TravAction.cover)⦘
                 ∪

               ⦗action ↓₁ (eq TravAction.cover)⦘ ⨾
               (event ↓ fwbob) ⨾
               ⦗action ↓₁ (eq TravAction.issue)⦘
                 ∪

               ⦗action ↓₁ (eq TravAction.issue)⦘ ⨾
               (event ↓ (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺)) ⨾
               ⦗action ↓₁ (eq TravAction.issue)⦘).
  
  Lemma iord_irreflexive WF COMP WFSC CONS : irreflexive iord.
  Proof using.
    unfold iord. unfolder. intros [y z]; ins; desf; eauto.
    { eapply sb_irr; eauto. }
    { eapply (sc_irr WFSC); eauto. }
    eapply ar_rf_ppo_loc_acyclic; eauto.
  Qed.

  Lemma iord_acyclic WF WFSC COMP CONS : acyclic iord.
  Proof using.
    assert (transitive sb) as SBTRANS.
    { apply sb_trans. }

    red. unfold iord.
    rewrite !restr_union.
    remember 
      (restr_rel (event ↓₁ (E \₁ (fun a : actid => is_init a)))
                 (⦗action ↓₁ eq TravAction.cover⦘
                    ⨾ event ↓ (sb ∪ sc) ⨾ ⦗action ↓₁ eq TravAction.cover⦘)) as SB.
    remember 
      (restr_rel (event ↓₁ (E \₁ (fun a : actid => is_init a)))
                 (⦗action ↓₁ eq TravAction.issue⦘
                    ⨾ event ↓ rf^? ⨾ ⦗action ↓₁ eq TravAction.cover⦘)) as RF.

    remember 
      (restr_rel (event ↓₁ (E \₁ (fun a : actid => is_init a)))
                 (⦗action ↓₁ eq TravAction.cover⦘
                    ⨾ event ↓ fwbob ⨾ ⦗action ↓₁ eq TravAction.issue⦘)) as FWBOB.

    remember
      (restr_rel (event ↓₁ (E \₁ (fun a : actid => is_init a)))
                 (⦗action ↓₁ eq TravAction.issue⦘
                    ⨾ event ↓ (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺)
                    ⨾ ⦗action ↓₁ eq TravAction.issue⦘)) as AR.
    
    assert (transitive AR) as TAR.
    { subst.
      apply transitive_restr.
      rewrite <- restr_relE.
      apply transitive_restr.
      apply transitiveI. rewrite map_rel_seq.
      apply map_rel_mori; auto.
      arewrite_id ⦗W⦘ at 2.
      now rewrite seq_id_l, ct_ct. }
    
    assert (irreflexive AR) as IAR.
    { subst.
      apply irreflexive_restr.
      rewrite <- restr_relE.
      apply irreflexive_restr.
      apply map_rel_irr.
      arewrite_id ⦗W⦘. rewrite seq_id_l.
      now apply ar_rf_ppo_loc_acyclic. }
    
    assert (acyclic AR) as AAR.
    { now apply trans_irr_acyclic. }

    assert (SB ⨾ RF ⊆ ∅₂) as SBRF.
    { subst. clear. unfolder. intros [a b] [c d]; ins. desc.
      destruct z; desf; ins; desf. }
    assert (SB⁺ ⨾ RF ⊆ RF) as SBCTRF.
    { rewrite ct_end, !seqA.
      rewrite SBRF. clear; basic_solver 1. }
    assert (SB＊ ⨾ RF ⊆ RF) as SBRTRF.
    { rewrite rtE, !seq_union_l, seq_id_l.
      rewrite SBCTRF. eauto with hahn. }
    
    assert (SB⁺ ⨾ AR ⊆ ∅₂) as SBAR.
    { rewrite ct_end, !seqA.
      arewrite_false (SB ⨾ AR).
      2: clear; basic_solver 1.
      subst. clear. unfolder. intros [a b] [c d]; ins. desc.
      destruct z; desf; ins; desf. }

    assert (RF ⨾ AR ⊆ ∅₂) as RFAR.
    { subst. clear. unfolder. intros [a b] [c d]; ins. desc.
      destruct z; desf; ins; desf. }
    
    assert (RF ;; RF ⊆ ∅₂) as RFRF.
    { subst. clear. unfolder. intros [a b] [c d]; ins. desc.
      destruct z; desf; ins; desf. }
    assert (transitive RF) as RFT.
    { apply transitiveI. rewrite RFRF. clear; basic_solver 1. }
    assert (RF⁺ ⊆ RF) as RFCT.
    { now apply ct_of_trans. }

    assert (RF⁺ ⨾ AR ⊆ ∅₂) as RFCTAR.
    { now rewrite RFCT. }
    
    assert (FWBOB ;; FWBOB ⊆ ∅₂) as FWFW.
    { subst. clear. unfolder. intros [a b] [c d]; ins. desc.
      destruct z; desf; ins; desf. }

    assert (event ↑ RF ⊆ rf^?) as ERF.
    { subst RF. clear. basic_solver 10. }

    assert (event ↑ SB ⊆ sb ∪ sc) as ESB.
    { subst SB. clear. basic_solver 10. }

    assert (event ↑ FWBOB ⊆ fwbob) as EFWBOB.
    { subst FWBOB. clear. basic_solver 10. }

    (* TODO: move to imm_s.v? *)
    assert (acyclic (sb ∪ sc)) as SBSCA.
    { apply acyclic_utt; splits; auto.
      all: try now apply WFSC.
      { apply sb_irr. }
      rewrite (wf_scD WFSC). rewrite <- !seqA, acyclic_seqC, !seqA.
      arewrite (⦗F ∩₁ Sc⦘ ⨾ sb ⨾ ⦗F ∩₁ Sc⦘ ⊆ sc).
      2: { rewrite rewrite_trans; try apply WFSC.
           red. rewrite ct_of_trans; apply WFSC. }
      rewrite <- f_sc_hb_f_sc_in_sc with (sc:=sc); eauto; try apply CONS.
      hahn_frame. apply imm_s_hb.sb_in_hb. }

    assert (acyclic SB) as SBA.
    { eapply collect_rel_acyclic with (f:=event).
      now rewrite ESB. }

    assert (acyclic (SB ∪ RF)) as SBRFA.
    { apply acyclic_ut; splits; auto.
      { subst RF. clear. intros [a b].
        unfolder. ins. desc. destruct z; desf. }
      rewrite acyclic_seqC. rewrite ct_end, !seqA.
      rewrite SBRF. rewrite seq_false_r.
      (* TODO: add a lemma to AuxRel.v/Hahn *)
      red. rewrite ct_of_trans; [|apply transitiveI].
      all: clear; basic_solver. }
    
    assert (sb^? ⨾ fwbob ⊆ fwbob⁺) as SBFINA.
    { rewrite crE, seq_union_l, seq_id_l.
      apply inclusion_union_l; eauto with hahn.
      apply sb_fwbob_in_fwbob. }
    assert (sb^? ⨾ fwbob⁺ ⊆ fwbob⁺) as SBFCTINA.
    { rewrite ct_begin at 1. rewrite <- !seqA, SBFINA.
      now rewrite ct_rt. }

    assert (event ↑ (RF^? ⨾ SB＊ ⨾ FWBOB) ⊆ ar⁺) as RSFAR.
    { rewrite !collect_rel_seq, !collect_rel_cr, !collect_rel_crt.
      rewrite ERF, ESB, EFWBOB. rewrite cr_of_cr.
      rewrite unionC. rewrite path_ut; auto.
      rewrite !seqA.
      rewrite SBFINA.
      arewrite (sc⁺ ⊆ sc).
      { apply ct_of_trans. apply WFSC. }
      arewrite (sc＊ ⨾ (sb ⨾ sc)＊ ⊆ sc^?).
      { admit. }
      arewrite (rf^? ⊆ rfe^? ;; sb^?).
      { rewrite rfi_union_rfe, cr_union_r.
        rewrite rfi_in_sb. clear. basic_solver 10. }
      arewrite (sb^? ⨾ sc^? ⨾ fwbob⁺ ⊆ ar⁺).
      2: { rewrite rfe_in_ar. now rewrite cr_ct. }
      arewrite (sb^? ⨾ sc^? ⊆ sb^? ∪ fwbob^? ;; sc^?).
      2: { rewrite seq_union_l, SBFCTINA, !seqA.
           rewrite sc_in_ar with (G:=G) (sc:=sc) at 1.
           rewrite fwbob_in_bob, bob_in_ar with (sc:=sc).
           rewrite !cr_ct. eauto with hahn. }
      rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l, !seq_id_r.
      unionL; eauto with hahn.
      transitivity (fwbob ⨾ sc); eauto with hahn.
      rewrite (dom_l (wf_scD WFSC)) at 1.
      hahn_frame. unfold imm_bob.fwbob.
      clear. mode_solver 10. }

    assert (acyclic (RF^? ⨾ SB＊ ⨾ FWBOB)) as RFSBFA.
    { eapply collect_rel_acyclic with (f:=event).
      rewrite RSFAR. red. rewrite ct_of_ct. apply CONS. }

    assert (acyclic (FWBOB ⨾ (SB ∪ RF)⁺)) as FWSBRFA.
    { rewrite acyclic_seqC.
      rewrite path_ut2; auto.
      arewrite ((RF ⨾ SB⁺)＊ ⨾ RF ⊆ RF).
      { rewrite rtE, !seq_union_l, seq_id_l.
        unionL; eauto with hahn.
        rewrite ct_end, !seqA.
        rewrite SBCTRF, RFRF. clear; basic_solver 1. }
      rewrite <- !seqA. rewrite SBRTRF.
      rewrite ct_begin. rewrite <- seq_union_l, !seqA.
      arewrite ((SB ∪ RF) ⨾ SB＊ ⊆ RF^? ;; SB＊); auto.
      rewrite seq_union_l. rewrite <- ct_begin, inclusion_t_rt.
      rewrite crE. clear; basic_solver 10. }

    assert (acyclic (SB ∪ RF ∪ FWBOB)) as SRFA.
    { apply acyclic_ut; splits; auto.
      { apply transitiveI. rewrite FWFW. clear; basic_solver 1. }
      unfolder. subst FWBOB. clear. intros [a b].
      unfolder. ins. desc. destruct z; desf. }

    apply acyclic_ut; auto.
    splits; auto.
    rewrite acyclic_seqC.
    rewrite unionA, unionC.
    arewrite (FWBOB ⊆ SB^* ⨾ FWBOB).
    { clear. rewrite rtE. basic_solver 10. }

    rewrite path_absorb.
    2: { left. rewrite seq_union_r.
         rewrite SBRF, union_false_l.
         unionR right.
         hahn_frame_r.
         rewrite rt_begin at 2. eauto with hahn. }
    rewrite !seq_union_l, !seqA. rewrite !SBAR.
    rewrite seq_false_r, !union_false_r.
    rewrite path_union, !seq_union_l.
    rewrite RFCTAR, union_false_l, !seqA.
    arewrite (RF＊ ⨾ AR ⊆ AR).
    { rewrite rtE, !seq_union_l, seq_id_l. rewrite RFCTAR.
      clear; basic_solver 1. }
    arewrite (RF＊ ⊆ RF^?).
    { now apply rt_of_trans. }

    eapply collect_rel_acyclic with (f:=event).
    rewrite collect_rel_seq, collect_rel_ct.
    rewrite RSFAR. rewrite ct_of_ct.
    admit.
  Admitted.
  
  Lemma iord_fsupp 
        (* (NOSC  : E ∩₁ F ∩₁ Sc ⊆₁ ∅) *)
        (FSUPPSB : fsupp sb) (* TODO: remove the requirement *)
        (FSUPPRF : fsupp rf) (* TODO: remove the requirement *)
        (FSUPP   : fsupp (ar ∪ rf ⨾ ppo ∩ same_loc)⁺) :
    fsupp iord.
  Proof using.
    assert (forall y, set_finite (fun x => y = event x)) as AA.
    { ins. exists [mkTL TravAction.issue y;
                   mkTL TravAction.cover y].
      ins. subst. destruct x as [[]]; ins; auto. }

    unfold iord. rewrite fwbob_in_sb.
    rewrite !restr_union.
    repeat (apply fsupp_union).
    4: { apply fsupp_restr.
         repeat (apply fsupp_seq); try now apply fsupp_eqv.
         apply fsupp_map_rel; auto.
         arewrite_id ⦗W⦘. now rewrite seq_id_l. }
    2: { apply fsupp_restr.
         repeat (apply fsupp_seq); try now apply fsupp_eqv.
         apply fsupp_map_rel; auto.
         now apply fsupp_cr. }
    2: { apply fsupp_restr.
         repeat (apply fsupp_seq); try now apply fsupp_eqv.
         apply fsupp_map_rel; auto. }
    admit.
  Admitted.

  Lemma iord_ct_fsupp WF WFSC COMP CONS
        (* (NOSC  : E ∩₁ F ∩₁ Sc ⊆₁ ∅) *)
        (FSUPPSB : fsupp sb) (* TODO: remove the requirement *)
        (FSUPPRF : fsupp rf) (* TODO: remove the requirement *)
        (FSUPP : fsupp (ar ∪ rf ⨾ ppo ∩ same_loc)⁺) :
    fsupp iord⁺.
  Proof using.
    assert (transitive sb) as SBTRANS.
    { apply sb_trans. }

    unfold iord.
    rewrite !restr_union.
    remember 
      (restr_rel (event ↓₁ (E \₁ (fun a : actid => is_init a)))
                 (⦗action ↓₁ eq TravAction.cover⦘
                    ⨾ event ↓ (sb ∪ sc) ⨾ ⦗action ↓₁ eq TravAction.cover⦘)) as SB.
    remember 
      (restr_rel (event ↓₁ (E \₁ (fun a : actid => is_init a)))
                 (⦗action ↓₁ eq TravAction.issue⦘
                    ⨾ event ↓ rf^? ⨾ ⦗action ↓₁ eq TravAction.cover⦘)) as RF.

    remember 
      (restr_rel (event ↓₁ (E \₁ (fun a : actid => is_init a)))
                 (⦗action ↓₁ eq TravAction.cover⦘
                    ⨾ event ↓ fwbob ⨾ ⦗action ↓₁ eq TravAction.issue⦘)) as FWBOB.

    remember
      (restr_rel (event ↓₁ (E \₁ (fun a : actid => is_init a)))
                 (⦗action ↓₁ eq TravAction.issue⦘
                    ⨾ event ↓ (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺)
                    ⨾ ⦗action ↓₁ eq TravAction.issue⦘)) as AR.
    
    assert (transitive AR) as TAR.
    { subst.
      apply transitive_restr.
      rewrite <- restr_relE.
      apply transitive_restr.
      apply transitiveI. rewrite map_rel_seq.
      apply map_rel_mori; auto.
      arewrite_id ⦗W⦘ at 2.
      now rewrite seq_id_l, ct_ct. }
    
    assert (irreflexive AR) as IAR.
    { subst.
      apply irreflexive_restr.
      rewrite <- restr_relE.
      apply irreflexive_restr.
      apply map_rel_irr.
      arewrite_id ⦗W⦘. rewrite seq_id_l.
      now apply ar_rf_ppo_loc_acyclic. }
    
    assert (acyclic AR) as AAR.
    { now apply trans_irr_acyclic. }

    assert (SB ⨾ RF ⊆ ∅₂) as SBRF.
    { subst. clear. unfolder. intros [a b] [c d]; ins. desc.
      destruct z; desf; ins; desf. }
    assert (SB⁺ ⨾ RF ⊆ RF) as SBCTRF.
    { rewrite ct_end, !seqA.
      rewrite SBRF. clear; basic_solver 1. }
    assert (SB＊ ⨾ RF ⊆ RF) as SBRTRF.
    { rewrite rtE, !seq_union_l, seq_id_l.
      rewrite SBCTRF. eauto with hahn. }
    
    assert (SB⁺ ⨾ AR ⊆ ∅₂) as SBAR.
    { rewrite ct_end, !seqA.
      arewrite_false (SB ⨾ AR).
      2: clear; basic_solver 1.
      subst. clear. unfolder. intros [a b] [c d]; ins. desc.
      destruct z; desf; ins; desf. }

    assert (RF ⨾ AR ⊆ ∅₂) as RFAR.
    { subst. clear. unfolder. intros [a b] [c d]; ins. desc.
      destruct z; desf; ins; desf. }
    
    assert (RF ;; RF ⊆ ∅₂) as RFRF.
    { subst. clear. unfolder. intros [a b] [c d]; ins. desc.
      destruct z; desf; ins; desf. }
    assert (transitive RF) as RFT.
    { apply transitiveI. rewrite RFRF. clear; basic_solver 1. }
    assert (RF⁺ ⊆ RF) as RFCT.
    { now apply ct_of_trans. }

    assert (RF⁺ ⨾ AR ⊆ ∅₂) as RFCTAR.
    { now rewrite RFCT. }
    
    assert (FWBOB ;; FWBOB ⊆ ∅₂) as FWFW.
    { subst. clear. unfolder. intros [a b] [c d]; ins. desc.
      destruct z; desf; ins; desf. }

    assert (event ↑ RF ⊆ rf^?) as ERF.
    { subst RF. clear. basic_solver 10. }

    assert (event ↑ SB ⊆ sb ∪ sc) as ESB.
    { subst SB. clear. basic_solver 10. }

    assert (event ↑ FWBOB ⊆ fwbob) as EFWBOB.
    { subst FWBOB. clear. basic_solver 10. }

    (* TODO: move to imm_s.v? *)
    assert (acyclic (sb ∪ sc)) as SBSCA.
    { apply acyclic_utt; splits; auto.
      all: try now apply WFSC.
      { apply sb_irr. }
      rewrite (wf_scD WFSC). rewrite <- !seqA, acyclic_seqC, !seqA.
      arewrite (⦗F ∩₁ Sc⦘ ⨾ sb ⨾ ⦗F ∩₁ Sc⦘ ⊆ sc).
      2: { rewrite rewrite_trans; try apply WFSC.
           red. rewrite ct_of_trans; apply WFSC. }
      rewrite <- f_sc_hb_f_sc_in_sc with (sc:=sc); eauto; try apply CONS.
      hahn_frame. apply imm_s_hb.sb_in_hb. }

    assert (acyclic SB) as SBA.
    { eapply collect_rel_acyclic with (f:=event).
      now rewrite ESB. }

    assert (acyclic (SB ∪ RF)) as SBRFA.
    { apply acyclic_ut; splits; auto.
      { subst RF. clear. intros [a b].
        unfolder. ins. desc. destruct z; desf. }
      rewrite acyclic_seqC. rewrite ct_end, !seqA.
      rewrite SBRF. rewrite seq_false_r.
      (* TODO: add a lemma to AuxRel.v/Hahn *)
      red. rewrite ct_of_trans; [|apply transitiveI].
      all: clear; basic_solver. }
    
    assert (sb^? ⨾ fwbob ⊆ fwbob⁺) as SBFINA.
    { rewrite crE, seq_union_l, seq_id_l.
      apply inclusion_union_l; eauto with hahn.
      apply sb_fwbob_in_fwbob. }
    assert (sb^? ⨾ fwbob⁺ ⊆ fwbob⁺) as SBFCTINA.
    { rewrite ct_begin at 1. rewrite <- !seqA, SBFINA.
      now rewrite ct_rt. }

    assert (event ↑ (RF^? ⨾ SB＊ ⨾ FWBOB) ⊆ ar⁺) as RSFAR.
    { rewrite !collect_rel_seq, !collect_rel_cr, !collect_rel_crt.
      rewrite ERF, ESB, EFWBOB. rewrite cr_of_cr.
      rewrite unionC. rewrite path_ut; auto.
      rewrite !seqA.
      rewrite SBFINA.
      arewrite (sc⁺ ⊆ sc).
      { apply ct_of_trans. apply WFSC. }
      arewrite (sc＊ ⨾ (sb ⨾ sc)＊ ⊆ sc^?).
      { admit. }
      arewrite (rf^? ⊆ rfe^? ;; sb^?).
      { rewrite rfi_union_rfe, cr_union_r.
        rewrite rfi_in_sb. clear. basic_solver 10. }
      arewrite (sb^? ⨾ sc^? ⨾ fwbob⁺ ⊆ ar⁺).
      2: { rewrite rfe_in_ar. now rewrite cr_ct. }
      arewrite (sb^? ⨾ sc^? ⊆ sb^? ∪ fwbob^? ;; sc^?).
      2: { rewrite seq_union_l, SBFCTINA, !seqA.
           rewrite sc_in_ar with (G:=G) (sc:=sc) at 1.
           rewrite fwbob_in_bob, bob_in_ar with (sc:=sc).
           rewrite !cr_ct. eauto with hahn. }
      rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l, !seq_id_r.
      unionL; eauto with hahn.
      transitivity (fwbob ⨾ sc); eauto with hahn.
      rewrite (dom_l (wf_scD WFSC)) at 1.
      hahn_frame. unfold imm_bob.fwbob.
      clear. mode_solver 10. }

    assert (acyclic (RF^? ⨾ SB＊ ⨾ FWBOB)) as RFSBFA.
    { eapply collect_rel_acyclic with (f:=event).
      rewrite RSFAR. red. rewrite ct_of_ct. apply CONS. }

    assert (acyclic (FWBOB ⨾ (SB ∪ RF)⁺)) as FWSBRFA.
    { rewrite acyclic_seqC.
      rewrite path_ut2; auto.
      arewrite ((RF ⨾ SB⁺)＊ ⨾ RF ⊆ RF).
      { rewrite rtE, !seq_union_l, seq_id_l.
        unionL; eauto with hahn.
        rewrite ct_end, !seqA.
        rewrite SBCTRF, RFRF. clear; basic_solver 1. }
      rewrite <- !seqA. rewrite SBRTRF.
      rewrite ct_begin. rewrite <- seq_union_l, !seqA.
      arewrite ((SB ∪ RF) ⨾ SB＊ ⊆ RF^? ;; SB＊); auto.
      rewrite seq_union_l. rewrite <- ct_begin, inclusion_t_rt.
      rewrite crE. clear; basic_solver 10. }

    assert (transitive FWBOB) as FWBOBTRANS.
    { apply transitiveI. rewrite FWFW. clear; basic_solver 1. }

    assert (acyclic (SB ∪ RF ∪ FWBOB)) as SRFA.
    { apply acyclic_ut; splits; auto.
      unfolder. subst FWBOB. clear. intros [a b].
      unfolder. ins. desc. destruct z; desf. }

    assert (fsupp AR) as FAR.
    { (* follows from fsupp_iord *)
      admit. }

    assert (fsupp FWBOB) as FFWBOB.
    { (* follows from fsupp_iord *)
      admit. }

    assert (fsupp (SB ∪ RF)＊) as SRA.
    { admit. }

    assert (FWBOB ⨾ (SB ∪ RF)⁺ ⊆ FWBOB ⨾ RF ⨾ SB＊) as FWBOBSBRF.
    { admit. }

    assert (fsupp (SB ∪ RF ∪ FWBOB)⁺) as FSRFW.
    { apply fsupp_rt_ct.
      rewrite path_ut; auto.
      repeat apply fsupp_seq; auto.
      2: now apply fsupp_cr. 
      rewrite FWBOBSBRF.
      admit. }

    apply fsupp_rt_ct.
    rewrite path_ut; auto.
    repeat apply fsupp_seq.
    3: now apply fsupp_cr.
    { now apply fsupp_ct_rt. }
    apply fsupp_ct_rt.
    rewrite ct_rotl.
    repeat (apply fsupp_seq; auto).
    rewrite ct_end, !seqA.
    arewrite ((SB ∪ RF ∪ FWBOB) ⨾ AR ⊆ FWBOB ⨾ AR).
    { admit. }
    rewrite path_ut; auto.
    rewrite !seqA.
    arewrite (FWBOB^? ⨾ FWBOB ⊆ FWBOB).
    { admit. }
    rewrite FWBOBSBRF.
    arewrite ((FWBOB ⨾ RF ⨾ SB＊)＊ ⊆ (FWBOB ⨾ RF ⨾ SB＊)^?).
    { admit. }
    arewrite ((FWBOB ⨾ RF ⨾ SB＊)^? ⨾ FWBOB ⨾ AR ⊆ FWBOB ⨾ AR).
    { admit. }
    arewrite ((SB ∪ RF)＊ ⨾ FWBOB ⊆ RF^? ⨾ SB＊ ⨾ FWBOB).
    { admit. }
    arewrite (RF^? ⨾ SB＊ ⨾ FWBOB ⊆ AR).
    { admit. }
  Admitted.


  Lemma iord_wf : well_founded iord.
  Proof using.
    (* TODO: The idea is to prove the lemma by introducing two functions: 
             1) nwrite : E∩W    -> nat  
             2) nfence : E∩F∩Sc -> nat  
             w    tc_sb_C : dom_rel ( sb ⨾ ⦗covered T⦘) ⊆₁ covered T ;
hich totally order writes and SC fences separately
             and respectively and are monotone on ar⁺.
             Then, on each iord-descending chain of traversal actions
             we can pick an issuing label w/ nwrite-minimal write
             since action ↓ <|issue|> ;; iord^+ ;; <|issue|> ⊆ ar⁺.
             The same could be done for SC fences.
     *)
    (* TODO: Would like to have smth like reversed
             'wf_impl_no_inf_seq' *)
  Admitted.
  
  Lemma iord_ct_fsupp WF WFSC COMP CONS
        (* (NOSC  : E ∩₁ F ∩₁ Sc ⊆₁ ∅) *)
        (FSUPPSB : fsupp sb) (* TODO: remove the requirement *)
        (FSUPPRF : fsupp rf) (* TODO: remove the requirement *)
        (FSUPP : fsupp (ar ∪ rf ⨾ ppo ∩ same_loc)⁺) :
    fsupp iord⁺.
  Proof using.
    apply fsupp_wf_implies_fsupp_ct.
    { now apply iord_wf. }
    now apply iord_fsupp.
  Qed.
  
  (* NEXT TODO: Combination of iord_ct_fsupp and iord_acyclic should
                allow to get lineralization of traversal actions.
   *)
End TravLabel.
