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
Require Import SetSize.
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
  fsupp (f ↓ r).
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

(* (* TODO: move to AuxRel2.v *) *)
(* Lemma fsupp_collect_rel {A B} (f : A -> B) *)
(*       (FSURJ : forall y, exists x, y = f x) *)
(*       r (FSUPP : fsupp r) : *)
(*   fsupp (f ↑ r). *)
(* Proof using. *)
(*   unfolder. ins. red in FSUPP. *)
(*   destruct (FSURJ y) as [x AA]; subst. *)
(*   destruct (FSUPP x) as [l BB]. *)
(*   specialize (FSUPP x). desf. *)
(*   exists (map f findom). *)
(*   ins. desf. apply in_map_iff. *)
(*   eexists; splits; eauto. *)
(*   apply FSUPP. *)
(* Qed. *)

(* TODO: move to AuxRel2.v *)
Lemma fsupp_map_rel2 {A B} (f : B -> A)
      (FSURJ : forall y, exists x, y = f x)
      r (FSUPP : fsupp (f ↓ r)) :
  fsupp r.
Proof using.
  unfolder. ins. red in FSUPP.
  unfold map_rel in *.
  destruct (FSURJ y) as [x AA]; subst.
  destruct (FSUPP x) as [l BB].
  exists (map f l).
  ins. apply in_map_iff.
  destruct (FSURJ x0) as [z CC]; subst.
  eexists; eauto.
Qed.

Lemma map_rel_seq2 {A B} {f : A -> B} r r'
      (FSURJ : forall y, exists x, y = f x) :
  f ↓ r ⨾ f ↓ r' ≡ f ↓ (r ⨾ r').
Proof using.
  split.
  { apply map_rel_seq. }
  unfolder. ins. desf.
  specialize (FSURJ z). desf.
  eauto.
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
               (event ↓ (⦗W⦘ ⨾ rf^?)) ⨾
               ⦗action ↓₁ (eq TravAction.cover)⦘
                 ∪

               ⦗action ↓₁ (eq TravAction.cover)⦘ ⨾
               (event ↓ (fwbob ⨾ ⦗W⦘)) ⨾
               ⦗action ↓₁ (eq TravAction.issue)⦘
                 ∪

               ⦗action ↓₁ (eq TravAction.issue)⦘ ⨾
               (event ↓ (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗W⦘)) ⨾
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
                    ⨾ event ↓ (⦗W⦘ ⨾ rf^?) ⨾ ⦗action ↓₁ eq TravAction.cover⦘)) as RF.

    remember 
      (restr_rel (event ↓₁ (E \₁ (fun a : actid => is_init a)))
                 (⦗action ↓₁ eq TravAction.cover⦘
                    ⨾ event ↓ (fwbob ⨾ ⦗W⦘) ⨾ ⦗action ↓₁ eq TravAction.issue⦘)) as FWBOB.

    remember
      (restr_rel (event ↓₁ (E \₁ (fun a : actid => is_init a)))
                 (⦗action ↓₁ eq TravAction.issue⦘
                    ⨾ event ↓ (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗W⦘)
                    ⨾ ⦗action ↓₁ eq TravAction.issue⦘)) as AR.
    
    assert (transitive AR) as TAR.
    { subst.
      apply transitive_restr.
      rewrite <- restr_relE.
      apply transitive_restr.
      apply transitiveI. rewrite map_rel_seq.
      apply map_rel_mori; auto.
      hahn_frame.
      arewrite_id ⦗W⦘.
      now rewrite !seq_id_l, ct_ct. }
    
    assert (irreflexive AR) as IAR.
    { subst.
      apply irreflexive_restr.
      rewrite <- restr_relE.
      apply irreflexive_restr.
      apply map_rel_irr.
      arewrite_id ⦗W⦘. rewrite !seq_id_l, seq_id_r.
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
         arewrite_id ⦗W⦘. now rewrite !seq_id_l, !seq_id_r. }
    2: { apply fsupp_restr.
         repeat (apply fsupp_seq); try now apply fsupp_eqv.
         apply fsupp_map_rel; auto.
         arewrite_id ⦗W⦘. rewrite !seq_id_l.
         now apply fsupp_cr. }
    2: { apply fsupp_restr.
         repeat (apply fsupp_seq); try now apply fsupp_eqv.
         arewrite_id ⦗W⦘. rewrite !seq_id_r.
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
                    ⨾ event ↓ (⦗W⦘ ⨾ rf^?) ⨾ ⦗action ↓₁ eq TravAction.cover⦘)) as RF.

    remember 
      (restr_rel (event ↓₁ (E \₁ (fun a : actid => is_init a)))
                 (⦗action ↓₁ eq TravAction.cover⦘
                    ⨾ event ↓ (fwbob ⨾ ⦗W⦘) ⨾ ⦗action ↓₁ eq TravAction.issue⦘)) as FWBOB.

    remember
      (restr_rel (event ↓₁ (E \₁ (fun a : actid => is_init a)))
                 (⦗action ↓₁ eq TravAction.issue⦘
                    ⨾ event ↓ (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺ ⨾ ⦗W⦘)
                    ⨾ ⦗action ↓₁ eq TravAction.issue⦘)) as AR.
    
    assert (transitive AR) as TAR.
    { subst.
      apply transitive_restr.
      rewrite <- restr_relE.
      apply transitive_restr.
      apply transitiveI. rewrite map_rel_seq.
      apply map_rel_mori; auto.
      hahn_frame. arewrite_id ⦗W⦘.
      now rewrite !seq_id_l, ct_ct. }
    
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

    assert (sb^? ⨾ fwbob ⊆ fwbob⁺) as SBFINA.
    { rewrite crE, seq_union_l, seq_id_l.
      apply inclusion_union_l; eauto with hahn.
      apply sb_fwbob_in_fwbob. }
    assert (sb^? ⨾ fwbob⁺ ⊆ fwbob⁺) as SBFCTINA.
    { rewrite ct_begin at 1. rewrite <- !seqA, SBFINA.
      now rewrite ct_rt. }

    assert (transitive FWBOB) as FWBOBTRANS.
    { apply transitiveI. rewrite FWFW. clear; basic_solver 1. }

    assert (fsupp AR) as FAR.
    { arewrite (AR ⊆ iord).
      2: now apply iord_fsupp.
      unfold iord. rewrite !restr_union.
      subst AR. eauto with hahn. }

    assert (fsupp FWBOB) as FFWBOB.
    { arewrite (FWBOB ⊆ iord).
      2: now apply iord_fsupp.
      unfold iord. rewrite !restr_union.
      subst FWBOB. eauto with hahn. }

    assert (fsupp RF) as FRF.
    { arewrite (RF ⊆ iord).
      2: now apply iord_fsupp.
      unfold iord. rewrite !restr_union.
      subst RF. eauto with hahn. }

    assert (transitive (RF^? ⨾ SB＊)) as TRFSB.
    { apply transitiveI. rewrite !seqA.
      rewrite crE, !seq_union_l, !seq_union_r, !seq_id_l.
      arewrite (SB＊ ⨾ SB＊ ⊆ SB＊).
      sin_rewrite !SBRTRF.
      sin_rewrite !RFRF.
      clear. basic_solver 10. }

    assert (fsupp SB＊) as FSBRT.
    { admit. }

    assert (fsupp AR＊) as FARRT.
    { rewrite rt_of_trans; auto.
      now apply fsupp_cr. }

    assert (SB ∪ RF ⊆ RF^? ;; SB＊) as SBRFT.
    { rewrite rtE. clear; basic_solver 10. }

    assert (fsupp (SB ∪ RF)＊) as SRA.
    { rewrite SBRFT. rewrite rt_of_trans; auto.
      apply fsupp_cr. apply fsupp_seq; auto.
      now apply fsupp_cr. }
    
    assert (FWBOB ⨾ SB ⊆ ∅₂) as FWBOBSB.
    { subst FWBOB SB. clear. intros [a b] [c d].
      unfolder. ins. desc; subst; ins.
      destruct z0 as [[]]; desf; ins. }
    
    assert (RF ⨾ SB＊ ⨾ RF ⊆ ∅₂) as RFSBRF.
    { rewrite rtE, !seq_union_l, !seq_union_r, seq_id_l.
      rewrite RFRF. rewrite ct_end, !seqA.
      rewrite SBRF. clear; basic_solver 1. }

    assert (RF ⨾ SB＊ ⨾ (RF ⨾ SB⁺)＊ ⊆ RF ⨾ SB＊) as RFSBRFSB.
    { rewrite rtE with (r:=RF ⨾ SB⁺). rewrite !seq_union_r, seq_id_r.
      unionL; eauto with hahn. rewrite ct_begin, !seqA.
      sin_rewrite RFSBRF. clear; basic_solver 1. }

    assert (FWBOB ⨾ (SB ∪ RF)⁺ ⊆ FWBOB ⨾ RF ⨾ SB＊) as FWBOBSBRF.
    { rewrite ct_begin. rewrite path_ut; auto.
      arewrite (FWBOB ⨾ (SB ∪ RF) ⊆ FWBOB ⨾ RF).
      { rewrite seq_union_r. rewrite FWBOBSB.
        unionL; eauto with hahn. clear; basic_solver 1. }
      sin_rewrite RFSBRFSB. rewrite !seqA.
      rewrite crE, !seq_union_r, !seq_id_r.
      rewrite RFSBRF. unionL; eauto with hahn.
      clear; basic_solver 1. }

    assert (forall y, exists x, y = event x) as EVENTSURJ.
    { ins. exists (mkTL TravAction.cover y); ins. }

    assert (RF ⨾ SB＊ ⨾ FWBOB ⊆ AR) as RFSBFWBOBINAR.
    { subst AR. rewrite restr_relEE.
      apply inclusion_inter_r.
      2: { subst RF FWBOB. clear. basic_solver 10. }
      subst RF FWBOB.
      rewrite !inclusion_restr.
      hahn_frame.
      arewrite_id ⦗action ↓₁ eq TravAction.cover⦘. rewrite !seq_id_l.
      rewrite <- !map_rel_seq2; auto.
      rewrite !seqA.
      hahn_frame.
      admit. }

    assert (fsupp (SB ∪ RF ∪ FWBOB)⁺) as FSRFW.
    { apply fsupp_rt_ct.
      rewrite path_ut; auto.
      repeat apply fsupp_seq; auto.
      2: now apply fsupp_cr. 
      rewrite FWBOBSBRF.
      apply fsupp_ct_rt.
      rewrite ct_rotl, !seqA.
      repeat apply fsupp_seq; auto.
      now rewrite RFSBFWBOBINAR. }

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
    { arewrite (SB ⊆ SB⁺).
      rewrite !seq_union_l. rewrite SBAR, RFAR.
      unionL; eauto with hahn.
      all: clear; basic_solver 1. }
    rewrite path_ut; auto.
    rewrite !seqA.
    sin_rewrite rewrite_trans_seq_cr_l; auto.
    rewrite FWBOBSBRF.
    arewrite ((FWBOB ⨾ RF ⨾ SB＊)＊ ⨾ FWBOB ⨾ AR ⊆ FWBOB ⨾ AR).
    { rewrite rtE with (r:=FWBOB ⨾ RF ⨾ SB＊).
      rewrite seq_union_l, seq_id_l. unionL; eauto with hahn.
      rewrite ct_rotl, !seqA.
      sin_rewrite !RFSBFWBOBINAR.
      hahn_frame_l. seq_rewrite <- ct_end.
      rewrite ct_unit. now apply ct_of_trans. }

    arewrite ((SB ∪ RF)＊ ⨾ FWBOB ⊆ RF^? ;; SB＊ ;; FWBOB).
    { rewrite SBRFT. rewrite rt_of_trans; auto.
      rewrite cr_seq, !seqA.
      unionL; eauto with hahn.
      clear. basic_solver 10. }

    rewrite crE, !seq_union_l, seq_id_l.
    sin_rewrite RFSBFWBOBINAR.
    rewrite rewrite_trans; auto.
    rewrite rt_of_trans with (r:=SB＊ ⨾ FWBOB ⨾ AR ∪ AR).
    { apply fsupp_cr, fsupp_union; auto.
      repeat apply fsupp_seq; auto. }

    assert (AR ⨾ FWBOB ⊆ ∅₂) as ARFWBOB.
    { subst. clear. unfolder. intros [a b] [c d]; ins. desc.
      destruct z; desf; ins; desf. }
    assert (AR ⨾ SB ⊆ ∅₂) as ARSB.
    { subst. clear. unfolder. intros [a b] [c d]; ins. desc.
      destruct z; desf; ins; desf. }

    assert (AR ⨾ SB＊ ⨾ FWBOB ⊆ ∅₂) as ARSBFW.
    { rewrite rtE, !seq_union_l, !seq_union_r, !seq_id_l.
      rewrite ct_begin, !seqA.
      rewrite ARFWBOB. sin_rewrite ARSB.
      clear; basic_solver 1. }
    apply transitiveI.
    rewrite !seq_union_r, !seq_union_l, !seqA.
    unionL.
    { sin_rewrite ARSBFW. clear; basic_solver 1. }
    { sin_rewrite ARSBFW. clear; basic_solver 1. }
    all: rewrite rewrite_trans; eauto with hahn.
  Admitted.

  Lemma iord_wf : well_founded iord.
  Proof using.
  Admitted.
  
  (* NEXT TODO: Combination of iord_ct_fsupp and iord_acyclic should
                allow to get lineralization of traversal actions.
   *)

  Definition respects_rel {A: Type} (enum: nat -> A) (r: relation A) (S: A -> Prop) :=
    forall i j (DOMi: NOmega.lt_nat_l i (set_size S))
      (DOMj: NOmega.lt_nat_l j (set_size S))
      (Rij: r (enum i) (enum j)),
      i < j.

  Definition graph_steps: t -> Prop := event ↓₁ (E \₁ is_init). 

  Definition set2trav_config (S: t -> Prop) :=
    mkTC
      (event ↑₁ (action ↓₁ (eq TravAction.cover) ∩₁ S) ∪₁ is_init ∩₁ E)
      (event ↑₁ (action ↓₁ (eq TravAction.issue) ∩₁ S) ∩₁ W ∪₁ is_init ∩₁ E).

  (* TODO: move upper *)
  Require Import Coq.Logic.FinFun. 
  
  Lemma add_map_collect {A B: Type} (f : A -> B) (ra : relation A):
    ra ⊆ map_rel f (collect_rel f ra).
  Proof using. basic_solver 10. Qed. 
    
  Lemma add_collect_map_rel {A B: Type} (f : B -> A) (ra : relation A)
        (SUR: Surjective f):
    ra ⊆ collect_rel f (map_rel f ra).
  Proof using.
    unfolder. ins.
    red in SUR. destruct (SUR x), (SUR y). 
    do 2 eexists. splits; vauto.
  Qed. 
    
  Lemma add_collect_set_map {A B: Type} (f : B -> A) (sa : A -> Prop)
        (SUR: Surjective f):
    sa ⊆₁ set_collect f (set_map f sa).
  Proof using.
    unfolder. ins.
    red in SUR. destruct (SUR x). 
    eexists. splits; vauto.
  Qed. 
    
  Lemma event_sur: Surjective event.
  Proof using. red. ins. by exists (mkTL TravAction.cover y). Qed. 

  Lemma s2tc_closed_coherent_alt WF COMP WFSC CONS
        (S: t -> Prop)
        (IN_E: event ↑₁ S ⊆₁ acts_set G)
        (PREF_CLOS: dom_rel (iord⁺ ;; ⦗S⦘) ⊆₁ S):
    tc_coherent_alt G sc (set2trav_config S).
  Proof using. 
    split; simpl. 
    { basic_solver. }
    { apply set_subset_union_l. split; [| basic_solver]. 
      rewrite <- IN_E. basic_solver. }
    { rewrite id_union, seq_union_r, dom_union. apply set_subset_union_l. split.
      2: { rewrite no_sb_to_init. basic_solver. }
      apply set_subset_union_r. left.
      (* TODO: ? *)
      admit. }
    { admit. }
    { admit. }
    { admit. }
    { apply set_subset_union_l. split; [| basic_solver].
      rewrite <- IN_E. basic_solver. }
    { apply set_subset_union_l. split; [| rewrite init_w]; basic_solver. }
    { admit. }
    { admit. }
  Admitted.
  
  Section StepsEnum.
    Variable (steps: nat -> t).
    Hypothesis (ENUM: enumerates steps graph_steps).
    Hypothesis (RESP: respects_rel steps iord⁺ graph_steps). 

    Lemma steps_prefix_coherent_alt WF COMP WFSC CONS
          i (DOMi: NOmega.lt_nat_l i (set_size graph_steps)):
      tc_coherent_alt G sc (set2trav_config (⋃₁ j < i, eq (steps j))).
    Proof using RESP ENUM.
      apply s2tc_closed_coherent_alt; auto.
      { rewrite set_collect_bunion.
        apply set_subset_bunion_l. ins.
        apply enumeratesE' in ENUM. cdes ENUM.
        forward eapply INSET as IN. 
        { eapply NOmega.lt_lt_nat; eauto. }
        red. ins. red in H. desc. subst.
        do 3 red in IN. by desc. }
      red. intros e' [e DOMe']. apply seq_eqv_r in DOMe' as [REL ENUMe].
      red in ENUMe. destruct ENUMe as [j [LTji STEPje]].
      apply enumeratesE' in ENUM. cdes ENUM.
      specialize (IND e'). specialize_full IND.
      { red. apply clos_trans_restrD in REL. by desc. }
      destruct IND as [k [DOMk STEPke']].
      red. exists k. splits; eauto.
      etransitivity; [| apply LTji]. 
      red in RESP. apply RESP with (j := j); eauto.
      2: congruence.
      eapply NOmega.lt_lt_nat; eauto.
    Qed. 
      
  End StepsEnum. 

  Lemma iord_enum_exists WF COMP WFSC CONS:
    exists (steps: nat -> t),
      enumerates steps graph_steps /\
      respects_rel steps iord⁺ graph_steps. 
  Proof using.
    edestruct countable_ext with (s := graph_steps) (r := iord⁺)
      as [| [steps [ENUM RESP]]].
    { eapply countable_subset; [| by apply set_subset_full_r].
      admit. }
    { red. split; [apply iord_acyclic | apply transitive_ct]; auto. }
    { apply iord_ct_fsupp; auto.
      all: admit. }
    { edestruct H. constructor. econstructor; vauto. }
    exists steps. splits; eauto.
    red. ins. apply RESP; auto.
    all: by apply set_lt_size. 
  Admitted.
            
        
End TravLabel.
