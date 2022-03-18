(******************************************************************************)
(** * Compilation correctness from the S_IMM memory model to the ARMv8.3 model *)
(******************************************************************************)

From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import Arm.
Require Import imm_bob.
Require Import imm_s_ppo.
Require Import imm_s_rfppo.
Require Import imm_s_hb.
Require Import imm_s.
Require Import imm_ppo.
Require Import imm_hb.
Require Import imm.
Require Import immToARMhelper.
Require Import imm_s_hb_hb.
Require Import ImmFair.
Require Import FairExecution.
Require Import imm_sToARM.
Require Import HardwareFairness. 
Require Import Lia.
Import ListNotations. 

Set Implicit Arguments.

Section immToARMFairness.

Variable G : execution.

Notation "'E'" := (acts_set G).
Notation "'lab'" := (lab G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'deps'" := (deps G).
Notation "'rmw_dep'" := (rmw_dep G).

Notation "'fre'" := (fre G).
Notation "'rfe'" := (rfe G).
Notation "'coe'" := (coe G).
Notation "'rfi'" := (rfi G).
Notation "'fri'" := (fri G).
Notation "'coi'" := (coi G).
Notation "'fr'" := (fr G).
Notation "'eco'" := (eco G).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).
Notation "'detour'" := (detour G).
Notation "'bob'" := (bob G).

(* imm_s *)
Notation "'s_sw'" := (imm_s_hb.sw G).
Notation "'s_release'" := (imm_s_hb.release G).
Notation "'s_rs'" := (imm_s_hb.rs G).
Notation "'s_hb'" := (imm_s_hb.hb G).
Notation "'s_ppo'" := (imm_s_ppo.ppo G).
Notation "'s_psc_f'" := (imm_s.psc_f G).
Notation "'s_psc_base'" := (imm_s.psc_base G).
Notation "'s_ar_int'" := (imm_s_ppo.ar_int G).

(* imm *)
Notation "'sw'" := (imm_hb.sw G).
Notation "'release'" := (imm_hb.release G).
Notation "'rs'" := (imm_hb.rs G).
Notation "'hb'" := (imm_hb.hb G).
Notation "'ppo'" := (imm_ppo.ppo G).
Notation "'psc'" := (imm.psc G).
Notation "'psc_f'" := (imm.psc_f G).
Notation "'psc_base'" := (imm.psc_base G).
Notation "'ar_int'" := (imm_ppo.ar_int G).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

(* arm *)
Notation "'obs'" := (obs G).
Notation "'obs''" := (obs' G).
Notation "'aob'" := (aob G).
Notation "'boba'" := (Arm.bob G).
Notation "'boba''" := (bob' G).
Notation "'dob'" := (dob G).

Notation "'L'" := (W ∩₁ (fun a => is_true (is_rel lab a))).
Notation "'Q'" := (R ∩₁ (fun a => is_true (is_acq lab a))).
Notation "'A'" := (R ∩₁ (fun a => is_true (is_sc  lab a))).

Notation "'F^ld'" := (F ∩₁ (fun a => is_true (is_acq lab a))).
Notation "'F^sy'" := (F ∩₁ (fun a => is_true (is_rel lab a))).

Notation "'Loc_' l" := (fun x => loc x = l) (at level 1).

Hypothesis RMW_DEPS : rmw ⊆ ctrl ∪ data.
Hypothesis W_EX_ACQ_SB : ⦗W_ex_acq⦘ ⨾ sb ⊆ sb ⨾ ⦗F^ld⦘ ⨾  sb^?.
Hypothesis DEPS_RMW_SB : rmw_dep ⨾ sb ⊆ ctrl.
Hypothesis REX_IN_RMW_CTRL : ⦗R_ex⦘ ⨾ sb ⊆ ctrl.

Hypothesis CON: ArmConsistent G.


(* TODO: check if that is defined somewhere else *)
Definition ob' := obs' ∪ dob ∪ aob ∪ bob' G. 

Lemma no_ob'_to_init:
  ob' ≡ ob' ⨾ ⦗set_compl is_init⦘. 
Proof. 
  forward eapply WF as WF; eauto. 
  split; [| basic_solver]. apply domb_rewrite.
  unfold ob', "obs'". rewrite dob_in_sb, aob_in_sb, bob'_in_sb; auto.
  rewrite !unionA, !unionK.   
  rewrite rfe_in_rf, no_rf_to_init, no_co_to_init, no_fr_to_init, no_sb_to_init; auto.
  all: try by apply CON. 
  basic_solver.
Qed.  
  
Ltac contra name := 
  match goal with
  | |- ?goal => destruct (classic goal) as [? | name]; [done| exfalso]
  end. 

Lemma wf_ob'E:
  ob' ≡ ⦗E⦘ ⨾ ob' ⨾ ⦗E⦘. 
Proof. 
  split; [| basic_solver]. apply dom_helper_3.
  forward eapply WF as WF; eauto. 
  unfold ob', "obs'". rewrite dob_in_sb, aob_in_sb, bob'_in_sb; auto.
  rewrite wf_rfeE, wf_coE, wf_frE, wf_sbE; basic_solver. 
Qed.


Lemma fin_locs_arm_hb_ct_fsupp 
      (FINLOCS: exists locs, forall e (ENIe: (E \₁ is_init) e), In (loc e) locs)
      (FAIR: mem_fair G)
      :
      fsupp (⦗set_compl is_init⦘ ⨾ ob'^+). 
Proof using CON. 
  forward eapply WF as WF; eauto. desc.
  rewrite clos_trans_domb_begin.
  2: { rewrite no_ob'_to_init; basic_solver. }
  apply AuxDef.fsupp_wf_implies_fsupp_ct.
  2: { unfold ob'.
       unfold ob', "obs'". rewrite dob_in_sb, aob_in_sb, bob'_in_sb; auto.
       rewrite !unionA, !unionK. rewrite rfe_in_rf.
       repeat rewrite seq_union_r. repeat apply fsupp_union.
       1-3: rewrite inclusion_seq_eqv_l.
       all: (apply FAIR || apply fsupp_rf || apply fsupp_sb); auto. }

  contra NWF. apply not_wf_inf_decr_enum in NWF as [f DECR].
  assert (forall i, (transp ob') (f i) (f (i + 1))) as DECR'.
  { ins. red. eapply seq_eqv_l. eauto. }

  assert (f ↑₁ set_full ⊆₁ E \₁ is_init) as ENUM_E.
  { intros e [i [_ Fie]].
    specialize (DECR i). eapply same_relation_exp in DECR.
    2: { rewrite no_ob'_to_init, wf_ob'E; auto. }
    generalize DECR. subst e. basic_solver. }
  
  assert (~ set_finite (f ↓₁ W)) as INFW'.
  { intros [iws FINW].
    set (wb := list_max iws + 1).
    assert (forall j (GE: j >= wb), sb (f (j + 1)) (f j)) as SB_STEPS.
    { intros. specialize (DECR j). apply seq_eqv_l in DECR. desc.
      unfold ob' in DECR0. eapply hahn_inclusion_exp in DECR0.
      2: { unfold "obs'". rewrite dob_in_sb, aob_in_sb, bob'_in_sb; auto.
           rewrite !unionA, !unionK, <- !unionA.
           eapply union_mori with (y := W × set_full ∪ set_full × W); [| reflexivity].
           rewrite wf_rfeD, wf_coD, wf_frD; auto. basic_solver. }      
      destruct DECR0; auto.
      destruct H; red in H; desc;
        [specialize (FINW (j + 1)) | specialize (FINW j)];
        specialize_full FINW; try basic_solver. 
      all: apply In_gt_list_max in FINW; vauto; lia. }
    
    forward eapply fsupp_dom_enum with (f0 := fun k => f (wb + k))
                                       (r := ⦗set_compl is_init⦘ ⨾ sb) as []. 
    { ins. apply seq_eqv_l. split.
      { apply ENUM_E. vauto. }
      rewrite PeanoNat.Nat.add_assoc. apply SB_STEPS. lia. }
    { eapply acyclic_mori; [| by apply sb_acyclic]. red. basic_solver. }
    eapply fsupp_mori; [| by apply fsupp_sb; eauto]. 
    red. rewrite inclusion_ct_seq_eqv_l.
    rewrite ct_of_trans; vauto. apply sb_trans. }
  
  eapply exists_inf_loc in INFW' as [ol [Ll INFtl]]; eauto. 
  destruct ol.
  2: { destruct INFtl. exists []. unfolder. ins. desc.
       forward eapply is_w_loc; eauto. ins. desc. vauto. }

  eapply enum_order_contradiction with (r' := co)
                                       (S0 := (E \₁ is_init) ∩₁ (W ∩₁ Loc_ (Some l))); eauto.
  { intros FIN. destruct INFtl. eapply set_finite_mori; eauto.
    red. rewrite set_map_inter with (d := _ \₁ _).
    apply set_subset_inter_r. split; [| basic_solver].
    red. ins. red. red in H. apply ENUM_E. vauto. }
  { red. ins. forward eapply wf_co_total with (a := a) (b := b);  
      try by (generalize IWa; generalize IWb; (vauto || basic_solver)).
    unfolder in IWa. unfolder in IWb. unfolder. desc. splits; congruence. }
  { by apply external_alt. }
  { apply FAIR. }

  rewrite <- ct_unit at 2. apply seq_mori; [reflexivity| ].
  unfold ob', "obs'". basic_solver 10. 
Qed. 


End immToARMFairness. 
