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

  (* TODO: move to imm_s.v *)
  Lemma fsc_sb_fsc_in_sc WF WFSC CONS : ⦗F ∩₁ Sc⦘ ⨾ sb ⨾ ⦗F ∩₁ Sc⦘ ⊆ sc.
  Proof using.
    rewrite imm_s_hb.sb_in_hb.
    apply f_sc_hb_f_sc_in_sc; auto.
    apply CONS.
  Qed.

  (* TODO: move to imm_s.v *)
  Lemma sc_sb_sc_in_sc WF WFSC CONS : sc ⨾ sb ⨾ sc ⊆ sc.
  Proof using.
    assert (transitive sc) as TSC.
    { now apply WFSC. }
    rewrite (wf_scD WFSC) at 1 2.
    rewrite !seqA.
    sin_rewrite fsc_sb_fsc_in_sc; auto.
    sin_rewrite !rewrite_trans; auto.
    clear; basic_solver 1.
  Qed.

  Lemma sb_sc_acyclic WF WFSC CONS : acyclic (sb ∪ sc).
  Proof using.
    assert (transitive sc) as TSC.
    { now apply WFSC. }
    assert (transitive sb) as TSB.
    { apply sb_trans. }
    apply acyclic_utt; auto.
    splits.
    { apply sb_irr. }
    { apply WFSC. }
    rewrite (wf_scD WFSC).
    rewrite <- !seqA, acyclic_rotl, !seqA.
    sin_rewrite fsc_sb_fsc_in_sc; auto.
    rewrite rewrite_trans; auto.
    red. rewrite ct_of_trans; auto.
    apply CONS.
  Qed.
  
  (* TODO: move to imm_s.v *)
  Lemma sb_sc_rt WF WFSC CONS : (sb ∪ sc)^* ≡ sb^? ;; sc^? ;; sb^?.
  Proof using.
    assert (transitive sc) as TSC.
    { now apply WFSC. }
    assert (transitive sb) as TSB.
    { apply sb_trans. }
    assert (transitive (sb ⨾ sc)) as TSBSC.
    { apply transitiveI. rewrite seqA.
      now rewrite sc_sb_sc_in_sc; auto. }
    split.
    2: { arewrite (sb^? ⊆ (sb ∪ sc)＊).
         arewrite (sc^? ⊆ (sb ∪ sc)＊).
         now rewrite !rt_rt. }
    rewrite unionC.
    rewrite path_ut; auto.
    rewrite ct_of_trans; auto.
    rewrite rt_of_trans; auto.
    rewrite rt_of_trans; auto.
    rewrite !crE. rewrite !seq_union_l, !seq_id_l, !seq_union_r, !seqA.
    rewrite !seq_id_r.
    rewrite sc_sb_sc_in_sc; auto.
    unionL; eauto with hahn.
    sin_rewrite sc_sb_sc_in_sc; auto.
    eauto with hahn.
  Qed.

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
    now apply sb_sc_acyclic.
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
    (* TODO: add a lemma to AuxRel.v/Hahn *)
    red. rewrite ct_of_trans; [|apply transitiveI].
    all: clear; basic_solver.
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

  (* TODO: move to imm_s.v? *)
  Lemma rf_sb_sc_sb_fwbob_in_ar WFSC : rf^? ⨾ sb^? ⨾ sc^? ⨾ sb^? ⨾ fwbob ⊆ ar⁺.
  Proof using.
    arewrite (rf^? ⊆ rfe^? ;; sb^?).
    { rewrite rfi_union_rfe, cr_union_r.
      rewrite rfi_in_sb. clear. basic_solver 10. }
    rewrite <- cr_ct.
    rewrite rfe_in_ar.
    hahn_frame_l.
    assert (sb^? ⨾ sb^? ⊆ sb^?) as SBSB.
    { apply transitiveI. apply transitive_cr. apply sb_trans. }
    sin_rewrite SBSB.
    arewrite (sb^? ⨾ sc^? ⊆ sb^? ∪ fwbob^? ;; sc^?).
    { rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l, !seq_id_r.
      unionL; eauto with hahn.
      transitivity (fwbob ⨾ sc); eauto with hahn.
      rewrite (dom_l (wf_scD WFSC)) at 1.
      hahn_frame. unfold imm_bob.fwbob.
      clear. mode_solver 10. }
    rewrite !seq_union_l. sin_rewrite SBSB.
    arewrite (sb^? ⨾ fwbob ⊆ ar⁺).
    { rewrite crE, !seq_union_l, seq_id_l.
      rewrite sb_fwbob_in_fwbob. rewrite fwbob_in_bob, bob_in_ar.
      eauto with hahn. }
    rewrite fwbob_in_bob, bob_in_ar.
    arewrite (sc^? ⊆ ar^?).
    rewrite !cr_ct.
    eauto with hahn.
  Qed.

  (* TODO: move to imm_s.v? *)
  Lemma rf_sb_sc_rt_sb_fwbob_in_ar WF WFSC CONS : rf^? ⨾ (sb ∪ sc)^* ⨾ fwbob ⊆ ar⁺.
  Proof using.
    rewrite sb_sc_rt, !seqA; auto.
    now apply rf_sb_sc_sb_fwbob_in_ar.
  Qed.

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
    rewrite cr_of_ct. rewrite sb_sc_rt; auto.
    rewrite !seqA.
    rewrite rf_sb_sc_sb_fwbob_in_ar; auto.
    apply clos_trans_mori. eauto with hahn.
  Qed.

  Lemma RFSBFINAR WF WFSC CONS : event ↑ (RF^? ⨾ SB^? ⨾ FWBOB) ⊆ ar⁺.
  Proof using.
    rewrite !collect_rel_seq, !collect_rel_cr.
    rewrite ERF, eSB_in_sb_sc_ct, EFWBOB. rewrite cr_of_cr.
    rewrite cr_of_ct. now apply rf_sb_sc_rt_sb_fwbob_in_ar.
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
    rewrite sb_sc_rt; auto.
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
  
  Lemma AR_fsupp (FSUPP : fsupp (ar ∪ rf ⨾ ppo ∩ same_loc)⁺) :
    fsupp AR.
  Proof using.
    repeat (apply fsupp_seq); try now apply fsupp_eqv.
    apply fsupp_map_rel; auto with lbase.
    arewrite_id ⦗W⦘. now rewrite !seq_id_l, !seq_id_r.
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
  
  Lemma iord_fsupp WF WFSC MF CONS
        (FSUPP : fsupp (ar ∪ rf ⨾ ppo ∩ same_loc)⁺) :
    fsupp iord.
  Proof using.
    assert (FSUPPRF : fsupp rf).
    { now apply fsupp_rf. }
    assert (FSUPPSC : fsupp sc).
    { now arewrite (sc ⊆ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺). }
    unfold iord. rewrite !restr_union.
    repeat (apply fsupp_union); auto using SB_fsupp, FWBOB_fsupp.
    all: apply fsupp_restr; auto using RF_fsupp, AR_fsupp.
  Qed.

  Lemma iord_ct_fsupp WF WFSC COMP MF CONS
        (FSUPP : fsupp (ar ∪ rf ⨾ ppo ∩ same_loc)⁺) :
    fsupp iord⁺.
  Proof using.
    assert (transitive sb) as SBTRANS.
    { apply sb_trans. }
    assert (FSUPPSB : fsupp (<|set_compl is_init|> ;; sb)).
    { now apply fsupp_sb. }
    assert (FSUPPRF : fsupp rf).
    { now apply fsupp_rf. }
    assert (FSUPPSC : fsupp sc).
    { now arewrite (sc ⊆ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺). }

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

    assert (fsupp AR^?) as FARCR.
    { apply fsupp_cr; auto with lbase. }

    assert (rSB ⊆ SB) as RSBIN.
    { subst rSB. apply inclusion_restr. }
    assert (rFWBOB ⊆ FWBOB) as RFWBOBIN.
    { subst rFWBOB. apply inclusion_restr. }

    assert (fsupp (rSB ∪ RF ∪ rFWBOB)⁺) as FSRFW.
    { apply fsupp_rt_ct.
      rewrite path_ut; auto.
      repeat apply fsupp_seq; auto.
      2: now apply fsupp_cr.
      rewrite FWBOBSBRF.
      apply fsupp_ct_rt.
      rewrite ct_rotl, !seqA.
      repeat (apply fsupp_seq; auto with lbase).
      rewrite RSBIN, RFWBOBIN.
      rewrite RFSBFWBOBINAR; auto.
      rewrite rt_of_trans; auto with lbase. }
    
    assert (RF ⨾ rSB^? ⨾ rFWBOB ⊆ AR) as RRFSBFWBOBINAR.
    { rewrite RSBIN, RFWBOBIN; auto with lbase. }

    apply fsupp_rt_ct.
    rewrite path_ut; auto with lbase.
    repeat apply fsupp_seq.
    3: now apply fsupp_cr; auto with lbase.
    { now apply fsupp_ct_rt. }
    apply fsupp_ct_rt.
    rewrite ct_rotl.
    repeat (apply fsupp_seq; auto with lbase).
    rewrite ct_end, !seqA.
    arewrite ((rSB ∪ RF ∪ rFWBOB) ⨾ AR ⊆ rFWBOB ⨾ AR).
    { rewrite !seq_union_l.
      rewrite RSBIN, SBAR, RFAR.
      now rewrite !union_false_l. }
    rewrite path_ut; auto.
    rewrite !seqA.
    sin_rewrite rewrite_trans_seq_cr_l; auto.
    rewrite FWBOBSBRF.
    arewrite ((rFWBOB ⨾ RF ⨾ rSB^?)＊ ⨾ rFWBOB ⨾ AR ⊆ rFWBOB ⨾ AR).
    { rewrite rtE with (r:=rFWBOB ⨾ RF ⨾ rSB^?).
      rewrite seq_union_l, seq_id_l. unionL; eauto with hahn.
      rewrite ct_rotl, !seqA.
      sin_rewrite !RRFSBFWBOBINAR.
      hahn_frame_l. seq_rewrite <- ct_end.
      rewrite ct_unit. apply ct_of_trans; auto with lbase. }

    arewrite ((rSB ∪ RF)＊ ⨾ rFWBOB ⊆ RF^? ;; rSB^? ;; rFWBOB).
    { rewrite SBRFT. rewrite rt_of_trans; auto.
      rewrite cr_seq, !seqA.
      unionL; eauto with hahn.
      clear. basic_solver 10. }

    rewrite crE, !seq_union_l, seq_id_l.
    sin_rewrite RRFSBFWBOBINAR.
    rewrite rewrite_trans; auto with lbase.
    rewrite rt_of_trans with (r:=rSB^? ⨾ rFWBOB ⨾ AR ∪ AR).
    { apply fsupp_cr, fsupp_union; auto with lbase.
      repeat (apply fsupp_seq; auto with lbase). }

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
