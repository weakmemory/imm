(******************************************************************************)
(** * Compilation correctness from the IMM memory model to the POWER model *)
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
Require Import ThreadBoundedExecution.
Require Import Lia.
Require Import ClassicalChoice.
Require Import ChoiceFacts.
Require Import IndefiniteDescription. 


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

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).


(* imm *)
Notation "'sw'" := (sw G).
Notation "'release'" := (release G).
Notation "'rs'" := (rs G).
Notation "'hb'" := (hb G).
Notation "'ppo'" := (ppo G).
Notation "'psc'" := (psc G).
Notation "'bob'" := (bob G).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

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

Ltac contra name := 
  match goal with
  | |- ?goal => destruct (classic goal) as [? | name]; [done| exfalso]
  end. 


Lemma not_wf_inf_decr_enum {A: Type} (r: relation A)
      (NWF: ~ well_founded r):
  exists (f: nat -> A), forall i, r (f (i + 1)) (f i).
Proof.
  contra DECR. destruct NWF.
  apply Classical_Wf.DSP_implies_WF. red. apply not_ex_not_all. 
  intros [f DECR']. destruct DECR. exists f.
  ins. contra Nri. destruct DECR'. exists i. by rewrite <- PeanoNat.Nat.add_1_r. 
Qed. 

Import ListNotations.

(* TODO: move to lib *)
Lemma set_finite_set_collect_inj {A B: Type} (f: A -> B) (S: A -> Prop)
      (FIN_MAP: set_finite (f ↑₁ S))
      (INJ_S: forall (x y: A) (Sx: S x) (Sy: S y), f x = f y -> x = y)
:
  set_finite S.
Proof using.
  red in FIN_MAP. desc.
  rewrite AuxRel2.set_bunion_separation with (fab := f).
  rewrite AuxRel2.set_full_split with (S0 := (fun b => In b findom)).
  rewrite set_bunion_union_l. apply set_finite_union. split.
  2: { exists []. ins. red in IN. desc. red in IN0. desc.
       destruct IN. apply FIN_MAP. basic_solver. }
  apply set_finite_bunion.
  { by vauto. }
  intros b INb. 
  destruct (classic (exists a, S a /\ f a = b)).
  2: { exists []. ins. destruct H. exists x. apply IN. }
  desc. exists [a]. ins. unfolder in IN. desc.  left. apply INJ_S; congruence.
Qed.  

Lemma set_infinite_nat:
  ~ set_finite (@set_full nat).
Proof using.
  intros [findom FIN].
  specialize (FIN (list_max findom + 1)). specialize_full FIN; [done| ].
  forward eapply (list_max_le findom (list_max findom)) as [CONTRA _].
  specialize_full CONTRA; [lia| ].
  eapply Forall_in in CONTRA; eauto. lia.
Qed. 

Lemma set_infinite_minus_finite {A: Type} (S S': A -> Prop)
      (INF: ~ set_finite S) (FIN': set_finite S'):
  ~ set_finite (S \₁ S'). 
Proof using.
  intros [findom FIN]. destruct FIN' as [findom' FIN']. 
  destruct INF. exists (findom ++ findom'). ins. apply in_or_app.
  destruct (classic (S' x)); intuition. 
Qed.


Lemma set_infinite_bunion {A B: Type} (As: A -> Prop) (ABs: A -> B -> Prop)
      (FINa: set_finite As)
      (INF: ~ set_finite (⋃₁ a ∈ As, ABs a)):
      (* (INF: ~ set_finite (⋃₁ a ∈ As, ABs a)): *)
  exists a, As a /\ ~ set_finite (ABs a).
Proof using. 
  contra FIN_ALL. destruct INF. apply set_finite_bunion; auto.
  ins. contra INF. destruct FIN_ALL. eauto.
Qed. 

(* (* TODO: move to ThreadBoundedExecution *) *)
(* Lemma threads_bound_separation G b (TB: threads_bound G b): *)

(* Lemma BinPos_Pos_lt_ge x y: *)
(*   BinPos.Pos.lt x y <-> BinPos.Pos.ge y x. *)
(* Proof using. *)
(*   etransitivity; [apply Pnat.Pos2Nat.inj_lt| ].  *)
(*   etransitivity; [| symmetry; apply Pnat.Pos2Nat.inj_ge]. *)
  
(*   unfold BinPos.Pos.lt, BinPos.Pos.ge. *)
(*   destruct (BinPos.Pos.compare x y). *)

Require Import Program.Basics.

Lemma wf_hbpE:
  hbp ≡ ⦗E⦘ ⨾ hbp ⨾ ⦗E⦘.
Proof using CON.
  forward eapply WF as WF; eauto. apply dom_helper_3. unfold "hbp".
  rewrite Power_ppo.wf_ppoE, wf_fenceE, wf_rfeE; auto. basic_solver.
Qed. 

Lemma fin_threads_locs_power_hb_ct_fsupp 
      (FINLOCS: exists locs, forall e (ENIe: (E \₁ is_init) e), In (loc e) locs)
      (FINTHREADS: exists b, threads_bound G b):
  fsupp (⦗set_compl is_init⦘ ⨾ hbp^+). 
Proof using. 
  forward eapply WF as WF; eauto. desc.
  rewrite clos_trans_domb_begin.
  2: { rewrite no_hbp_to_init; basic_solver. }
  apply AuxDef.fsupp_wf_implies_fsupp_ct.
  2: { unfold "hbp".
       rewrite Power_ppo.ppo_in_sb, fence_in_sb, unionK, rfe_in_rf; auto.
       rewrite seq_union_r. apply fsupp_union.
       { by apply fsupp_sb. }
       eapply fsupp_mori; [| by apply fsupp_rf; eauto]. red. basic_solver. } 

  contra NWF. apply not_wf_inf_decr_enum in NWF as [f DECR].

  assert (forall i d, hbp ^^ d (f (i + d)) (f i)) as STEPS.
  { intros. induction d. 
    { simpl. rewrite PeanoNat.Nat.add_0_r. vauto. }
    apply pow_S_begin. eexists. split; eauto.
    rewrite NPeano.Nat.add_succ_r, <- NPeano.Nat.add_1_r. 
    eapply seq_eqv_l. apply DECR. }
  assert (forall i j (LT: i < j), hbp^+ (f j) (f i)) as STEPS'.
  { ins. apply PeanoNat.Nat.le_exists_sub in LT. desc. subst j.
    apply ctEE. exists p. split; auto.
    rewrite NPeano.Nat.add_comm, PeanoNat.Nat.add_succ_comm. eauto. }
  
  set (enum_evs := f ↑₁ @set_full nat).
  assert (~ set_finite enum_evs) as INF_ENUM.
  { intros FIN. 
    apply set_finite_set_collect_inj in FIN; [by destruct set_infinite_nat| ]. 
    ins. cdes CON.
    pose proof (NPeano.Nat.lt_trichotomy x y) as LT. des; auto; 
      destruct (NO_THIN_AIR (f x)); [rewrite H at 1| rewrite H at 2]; by apply STEPS'. }
  assert (enum_evs ⊆₁ E \₁ is_init) as ENUM_E.
  { subst enum_evs. intros e [i [_ Fie]].
    specialize (DECR i). eapply same_relation_exp in DECR.
    2: { rewrite no_hbp_to_init, wf_hbpE; auto. }
    generalize DECR. subst e. basic_solver. }  

  functional_choice

  assert (~ set_finite (enum_evs ∩₁ W)) as INF_W.
  { intros [finw FINW].
    assert (exists i, forall j (GE: j >= i), ~ In (f j) finw) as [i W_BOUND].
    { induction finw.
      { exists 0. ins. vauto. }
      destruct (
    enough (set_finite (f ↓₁ W)) as FINW'.
    2: { 

  red in FINTHREADS. 
  forward eapply set_infinite_bunion 
    with (As := flip BinPos.Pos.lt b) (ABs := fun t => enum_evs ∩₁ Tid_ t).
  { exists (mk_list (Datatypes.S (BinPos.Pos.to_nat b)) BinPos.Pos.of_nat). intros.
    apply in_mk_list_iff. eexists. split.
    2: { symmetry. apply Pnat.Pos2Nat.id. }
    red in IN. apply Pnat.Pos2Nat.inj_lt in IN. lia. }
  { intros FIN. destruct INF_ENUM.
    rewrite AuxRel2.set_bunion_separation with (fab := tid).
    rewrite AuxRel2.set_full_split with (S := flip BinPos.Pos.lt b).
    rewrite set_bunion_union_l, set_finite_union. split; auto.
    exists []. ins. unfolder in IN. desc. destruct IN. red. 
    rewrite <- IN1. apply FINTHREADS. by apply ENUM_E. }
  intros [t [TBt INFt]]. red in TBt.

  (* red in FINLOCS.  *)
  forward eapply set_infinite_bunion 
    with (As := fun l => In l locs) (ABs := fun l => enum_evs ∩₁ Tid_ t ∩₁ Loc_ l).
  { vauto. }
  { intros FIN. destruct INFt.
    rewrite AuxRel2.set_bunion_separation with (fab := loc).
    rewrite AuxRel2.set_full_split with (S := fun l => In l locs).
    rewrite set_bunion_union_l, set_finite_union. split; auto.
    exists []. ins. unfolder in IN. desc. destruct IN. red. 
    rewrite <- IN1. apply FINLOCS. intuition. }
  intros [t [TBt INFt]]. red in TBt.

  

  (* assert (~ set_finite (enum_evs ∩₁ W)) as INF_W. *)
  (* { intros FIN.  *)
  


End immToPowerFairness.
