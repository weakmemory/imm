(******************************************************************************)
(** * Proof of Power fairness for Power-consistent,                           *)
(** * location- and thread-finite executions.                                 *)
(******************************************************************************)

From hahn Require Import Hahn.
From ZornsLemma Require Classical_Wf. 
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import Power_fences.
Require Import Power_ppo.
Require Import Power.
Require Import imm_bob.
Require Import imm_ppo.
Require Import imm_hb.
Require Import imm_rfppo. 
Require Import imm.
Require Import ImmFair.
Require Import FairExecution.
Require Import immToPower.
Require Import FinThreads.
Require Import Lia.
Require Import ClassicalChoice.
Require Import ChoiceFacts.
Require Import IndefiniteDescription. 
Require Import AuxRel2.
Require Import Program.Basics.
Require Import HardwareFairness.
Require Import AuxDef.
Import ListNotations. 

Set Implicit Arguments.

Section immToPowerFairness.

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
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'W_ex'" := (W_ex G).
Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).


(* power *)
Notation "'ctrli'" := (ctrli G).
Notation "'sync'" := (sync G).
Notation "'lwsync'" := (lwsync G).
Notation "'fence'" := (fence G).
Notation "'ppop'" := (Power_ppo.ppo G).
Notation "'hbp'" := (Power.hb G).
(* Notation "'S'" := (S G). *)
Notation "'detour'" := (detour G).

Notation "'F^isync'" := (F ∩₁ (fun a => is_true (is_rlx lab a))).
Notation "'F^lwsync'" := (F ∩₁ (fun a => is_true (is_ra lab a))).
Notation "'F^sync'" := (F ∩₁ (fun a => is_true (is_sc lab a))).

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'Loc_' l" := (fun x => loc x = l) (at level 1).

Hypothesis SC_F: Sc ⊆₁ F∩₁Sc.
Hypothesis NO_W_REL : W∩₁Rel ≡₁ ∅.
Hypothesis R_ACQ_SB : ⦗R∩₁Acq⦘ ⨾ sb ⊆ rmw ∪ ctrl ⨾ ⦗F^isync⦘ ⨾ sb^? ∪ sb ⨾ ⦗F^lwsync⦘ ⨾ sb^?.
Hypothesis RMW_DEPS : rmw ⊆ ctrl ∪ data.
Hypothesis RMW_CTRL_FAIL : ⦗R_ex⦘ ⨾ sb ⊆ ctrl.
Hypothesis DATA_RMW : data ⨾ ⦗W_ex⦘ ⨾ sb ⊆ ctrl.
Hypothesis DEPS_RMW_FAIL : rmw_dep ⨾ (rmw ∪ ctrl) ⊆ ctrl.

Hypothesis CON: PowerConsistent G.


Lemma wf_hbpE:
  hbp ≡ ⦗E⦘ ⨾ hbp ⨾ ⦗E⦘.
Proof using CON.
  apply dom_helper_3. unfold "hbp".
  rewrite Power_ppo.wf_ppoE, wf_fenceE, wf_rfeE; auto; try apply CON. 
  basic_solver.
Qed. 

Lemma hb_po_loc_hb:
  hbp⁺ ⨾ sb ∩ same_loc ⊆ hbp⁺. 
Proof using CON. 
Admitted. 

Lemma exists_inf_thread (f: nat -> actid) (S: actid -> Prop) b 
      (IN_E: f ↑₁ set_full ⊆₁ E \₁ is_init)
      (INF: ~ set_finite (f ↓₁ S))
      (FINTHREADS : threads_bound G b):
    exists t, BinPos.Pos.lt t b /\ ~ set_finite (f ↓₁ (S ∩₁ Tid_ t)).
Proof using. 
  apply set_infinite_bunion.
  { exists (mk_list (Datatypes.S (BinPos.Pos.to_nat b)) BinPos.Pos.of_nat). intros.
    apply in_mk_list_iff. eexists. split.
    2: { symmetry. apply Pnat.Pos2Nat.id. }
    red in IN. apply Pnat.Pos2Nat.inj_lt in IN. lia. }
  intros FIN. destruct INF.
  rewrite AuxRel2.set_bunion_separation with (fab := tid).
  rewrite set_map_bunion. 
  rewrite AuxRel2.set_full_split with (S := flip BinPos.Pos.lt b).
  rewrite set_bunion_union_l, set_finite_union. split; auto. 
  exists []. ins. unfolder in IN. desc. destruct IN. red. 
  rewrite <- IN1. apply FINTHREADS. apply IN_E. vauto.
Qed. 

Lemma exists_inf_loc (f: nat -> actid) (S: actid -> Prop) locs
      (IN_E: f ↑₁ set_full ⊆₁ E \₁ is_init)
      (INF: ~ set_finite (f ↓₁ S))
      (FINLOCS: forall e (ENIe: (E \₁ is_init) e), In (loc e) locs):
    exists l, In l locs /\ ~ set_finite (f ↓₁ (S ∩₁ Loc_ l)).
Proof using.
  eapply set_infinite_bunion; [by vauto| ]. 
  intros FIN. destruct INF.
  rewrite AuxRel2.set_bunion_separation with (fab := loc).
  rewrite set_map_bunion.
  rewrite AuxRel2.set_full_split with (S := fun l => In l locs).
  rewrite set_bunion_union_l, set_finite_union. split; auto.
  exists []. ins. unfolder in IN. desc.    
  destruct IN. rewrite <- IN1. apply FINLOCS. apply IN_E. vauto.
Qed.
  

Lemma fin_threads_locs_power_hb_ct_fsupp 
      (FINLOCS: exists locs, forall e (ENIe: (E \₁ is_init) e), In (loc e) locs)
      (FINTHREADS: exists b, threads_bound G b):
  fsupp (⦗set_compl is_init⦘ ⨾ hbp^+). 
Proof using CON.
  desc. 
  assert (Wf G) as WF by apply CON. 
  rewrite clos_trans_domb_begin.
  2: { rewrite no_hbp_to_init; basic_solver. }
  apply AuxDef.fsupp_wf_implies_fsupp_ct.
  2: { unfold "hbp".
       rewrite Power_ppo.ppo_in_sb, fence_in_sb, unionK, rfe_in_rf; auto.
       rewrite seq_union_r. apply fsupp_union.
       { by apply fsupp_sb. }
       eapply fsupp_mori; [| by apply fsupp_rf; eauto]. red. basic_solver. }

  contra NWF. apply not_wf_inf_decr_enum in NWF as [f DECR].
  assert (forall i, (transp hbp) (f i) (f (i + 1))) as DECR'.
  { ins. red. eapply seq_eqv_l. eauto. }

  assert (f ↑₁ set_full ⊆₁ E \₁ is_init) as ENUM_E.
  { intros e [i [_ Fie]].
    specialize (DECR i). eapply same_relation_exp in DECR.
    2: { rewrite no_hbp_to_init, wf_hbpE; auto. }
    generalize DECR. subst e. basic_solver. }
  
  assert (~ set_finite (f ↓₁ W)) as INFW'.
  { intros [iws FINW].
    set (wb := list_max iws + 1).
    assert (forall j (GE: j >= wb), sb (f (j + 1)) (f j)) as SB_STEPS.
    { intros. specialize (DECR j). apply seq_eqv_l in DECR. desc.
      unfold "hbp" in DECR0. eapply hahn_inclusion_exp in DECR0.
      2: { rewrite Power_ppo.ppo_in_sb, fence_in_sb, unionK; auto. reflexivity. }
      destruct DECR0; auto.
      specialize (FINW (j + 1)). specialize_full FINW.
      { apply wf_rfeD, seq_eqv_lr in H; auto. desc. vauto. }
      apply In_gt_list_max in FINW; vauto. lia. }
    
    forward eapply fsupp_dom_enum with (f := fun k => f (wb + k))
                                       (r := ⦗set_compl is_init⦘ ⨾ sb) as []. 
    { ins. apply seq_eqv_l. split.
      { apply ENUM_E. vauto. }
      rewrite PeanoNat.Nat.add_assoc. apply SB_STEPS. lia. }
    { eapply acyclic_mori; [| by apply sb_acyclic]. red. basic_solver. }
    eapply fsupp_mori; [| by apply fsupp_sb; eauto]. 
    red. rewrite inclusion_ct_seq_eqv_l.
    rewrite ct_of_trans; vauto. apply sb_trans. }
  
  eapply exists_inf_thread in INFW' as [t [TBt INFt]]; eauto.

  eapply exists_inf_loc in INFt as [ol [Ll INFtl]]; eauto. 
  destruct ol.
  2: { destruct INFtl. exists []. unfolder. ins. desc.
       forward eapply is_w_loc; eauto. ins. desc. vauto. }

  eapply enum_order_contradiction with (r' := sb ∩ same_loc)
                                       (S := (E \₁ is_init) ∩₁ (W ∩₁ Tid_ t ∩₁ Loc_ (Some l))); eauto.
  { intros FIN. destruct INFtl. eapply set_finite_mori; eauto.
    red. rewrite set_map_inter with (d := _ \₁ _).
    apply set_subset_inter_r. split; [| basic_solver].
    red. ins. red. red in H. apply ENUM_E. vauto. }
  { red. ins. forward eapply sb_total with (a := a) (b := b0) (t := t) as SB;
      try by (generalize IWa; generalize IWb; vauto || basic_solver). 
    unfolder in IWa. unfolder in IWb. desc. 
    des; [left | right]; split; congruence. }
  { by apply CON. }
  { by apply fsupp_sb_loc. }

  apply hb_po_loc_hb.
Qed.


End immToPowerFairness.
