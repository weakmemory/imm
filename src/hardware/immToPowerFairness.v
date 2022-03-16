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
Require Import AuxRel2.


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
Lemma set_finite_set_collect_inv_inj {A B: Type} (f: A -> B) (S: A -> Prop)
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

Lemma enum_exact_steps {A: Type} (r: relation A) (f: nat -> A)
      (STEPS: forall i : nat, r (f i) (f (i + 1))):
  forall i d, r ^^ d (f i) (f (i + d)). 
Proof using. 
  intros. induction d. 
  { simpl. rewrite PeanoNat.Nat.add_0_r. vauto. }
  eexists. split; eauto.
  rewrite NPeano.Nat.add_succ_r, <- NPeano.Nat.add_1_r.
  apply STEPS. 
Qed.   
  
Lemma enum_steps {A: Type} (r: relation A) (f: nat -> A)
      (STEPS: forall i : nat, r (f i) (f (i + 1))):
  ⟪STEPS: forall i j (LT: i < j), r^+ (f i) (f j) ⟫. 
Proof using.
  red. ins. apply PeanoNat.Nat.le_exists_sub in LT. desc. subst j.
  apply ctEE. exists p. split; auto.
  rewrite NPeano.Nat.add_comm, PeanoNat.Nat.add_succ_comm.
  apply enum_exact_steps. auto. 
Qed.

Lemma enum_steps_inv {A: Type} (r: relation A) (f: nat -> A)
      (STEPS: forall i : nat, r (f (i + 1)) (f i)):
  ⟪STEPS: forall i j (LT: i < j), r^+ (f j) (f i) ⟫.
Proof using.
  red. 
  ins. fold (transp r⁺ (f i) (f j)). apply transp_ct.
  apply enum_steps; auto. 
Qed.

(* TODO: move to lib *)
Lemma fin_dom_rel_fsupp {A: Type} (r: relation A):
  (forall S (FINS: set_finite S), set_finite (dom_rel (r ⨾ ⦗S⦘))) <-> fsupp r.
Proof.
  split. 
  2: { intros FSUPPr S FINS.  
  red in FSUPPr. apply functional_choice in FSUPPr as [supp_map FSUPPr].
  destruct FINS as [Sl DOMS]. 
  exists (concat (map supp_map Sl)).
  intros a [s DOM%seq_eqv_r]. desc.
  apply in_concat_iff. eexists. split.
  - eapply FSUPPr; eauto.
  - apply in_map. intuition. }
  ins. red. ins. 
  specialize (H (eq y)). specialize_full H; [by exists [y]; vauto|].
  destruct H as [findom FIN]. exists findom. ins. apply FIN.
  red. eexists. apply seq_eqv_r. eauto.  
Qed.

Lemma In_gt_list_max (l: list nat) (n: nat)
      (GT_MAX: n > list_max l):
  ~ In n l. 
Proof using.
  intros IN.
  forward eapply (list_max_le l (list_max l)) as [IMPL _].
  specialize_full IMPL; [lia| ].
  eapply Forall_in in IMPL; eauto. lia.
Qed.  

(* TODO: move to lib *)
Lemma same_relation_exp_iff {A: Type} (r r': relation A):
  r ≡ r' <-> (forall x y, r x y <-> r' x y).
Proof.
  red. split.
  { apply same_relation_exp. }
  ins. red. split.
  all: red; ins; apply H; auto.
Qed.  

Lemma excluded_middle_or (A B: Prop)
      (OR: A \/ B):
  A \/ (~ A) /\ B.
Proof. tauto. Qed. 

Lemma orders_contradiction {A: Type} (r1 r2: relation A) (S: A -> Prop)
      (ORD1: is_total S r1) (ORD2: is_total S r2):
  restr_rel S (r1 \ eq) ≡ restr_rel S (r2 \ eq) \/
  exists x y, S x /\ S y /\ r1 x y /\ r2 y x. 
Proof using.
  destruct (classic (restr_rel S (r1 \ eq) ≡ restr_rel S (r2 \ eq)))
    as [| NEQ]; [tauto| right]. 
  contra AGREE. destruct NEQ.
  apply same_relation_exp_iff. ins.
  destruct (classic (S x /\ S y)) as [[Sx Sy] |].
  2: { unfold restr_rel. split; ins; desc; by destruct H. }
  destruct (classic (x = y)) as [| NEQ].
  { subst. vauto. unfolder. tauto. }
  specialize (ORD1 x Sx y Sy NEQ). specialize (ORD2 x Sx y Sy NEQ).
  apply excluded_middle_or in ORD1, ORD2. 
  des; try by vauto.
  all: try by (edestruct AGREE; do 2 eexists; eauto). 
  pose proof not_ex_all_not. specialize (H _ _ AGREE).
  unfolder. tauto. 
Qed.

Lemma enum_inj {A: Type} (f: nat -> A) (r: relation A)
      (STEPS: forall i, r (f i) (f (i + 1)))
      (AC: acyclic r):
  forall x y, f x = f y -> x = y. 
Proof. 
  ins. forward eapply enum_steps as STEPS'; eauto.
  pose proof (NPeano.Nat.lt_trichotomy x y) as LT.
  des; auto;
    destruct (AC (f x)); [rewrite H at 2| rewrite H at 1]; 
    specialize (STEPS' _ _ LT); auto.
Qed. 

Lemma acyclic_transp {A: Type} (r: relation A)
      (AC: acyclic r):
  acyclic (transp r). 
Proof. red. rewrite <- transp_ct. vauto. Qed.   


(* Lemma fsupp_dom_enum {A: Type} (f: nat -> A) (r r': relation A) *)
(*       (STEPS: forall i, r (f (i + 1)) (f i)) *)
(*       (AC: acyclic r) *)
(*       (INCL: r' ⊆ r) *)
(*       (FSUPP: fsupp r'^+): *)
(*   False. *)
(* Proof.  *)
(*   apply fin_dom_rel_fsupp with (S := eq (f 0)) in FSUPP; [| by exists [f 0]; vauto]. *)
(*   eapply set_finite_mori in FSUPP. *)
(*   2: { red. apply set_collect_map with (f := f). } *)
(*   apply set_finite_set_collect_inv_inj in FSUPP.  *)
(*   2: { ins. eapply enum_inj with (r0 := transp r); eauto.  *)
(*        by apply acyclic_transp. } *)
(*   destruct FSUPP as [inds FSUPP]. *)
(*   specialize (FSUPP (list_max inds + 1)). specialize_full FSUPP. *)
(*   { red. eexists. apply seq_eqv_r. splits; [| reflexivity]. *)
(*     apply enum_steps_inv; eauto. *)
(*     2: lia. *)
(*     ins. specialize (STEPS i). apply INCL in *)
(*   } *)
(*   apply In_gt_list_max in FSUPP; auto. lia. *)
(* Qed.  *)

Lemma set_infinite_has_element {A: Type} (S: A -> Prop)
      (INF: ~ set_finite S):
  exists e, S e.
Proof. contra NO. destruct INF. exists []. ins. edestruct NO; vauto. Qed. 


Lemma fsupp_dom_enum_general {A: Type} (f: nat -> A) (r: relation A) (S: A -> Prop)
      (* (STEPS': forall i j (LT: i < j), r^+ (f j) (f i)) *)
      (STEPS: forall i, r (f (i + 1)) (f i))
      (AC: acyclic r)
      (* (FSUPP: fsupp (restr_rel S r^+)) *)
      (FSUPP: fsupp (restr_rel (S ∩₁ f ↑₁ set_full) r^+))
      (* (INF_S: ~ set_finite (S ∩₁ f ↑₁ set_full)): *)
      (INF_S': ~ set_finite (f ↓₁ S)):
  False.
Proof.
  pose proof (proj2 (fin_dom_rel_fsupp _) FSUPP) as FSUPP'.

  (* assert (~ set_finite (S ∩₁ f ↑₁ set_full)) as INF_S. *)
  (* { intros FIN. destruct INF_S'. red in FIN. *)
  forward eapply (set_infinite_has_element INF_S') as [ie1 Ie1].
  specialize (FSUPP' (eq (f ie1))). specialize_full FSUPP'; [by exists [f ie1]; vauto| ].

  eapply set_finite_mori in FSUPP'.
  2: { red. apply set_collect_map with (f := f). }
  apply set_finite_set_collect_inv_inj in FSUPP'.
  2: { ins. eapply enum_inj with (r0 := transp r); eauto.
       by apply acyclic_transp. }

  destruct INF_S'.
  rewrite <- set_inter_full_r with (s := _ ↓₁ _). 
  rewrite set_full_split with (S0 := ge ie1), set_inter_union_r.
  apply set_finite_union. split.
  { exists (List.seq 0 (ie1 + 1)). ins. unfolder in IN. desc. 
    apply in_seq. lia. }

  eapply set_finite_mori; [| by apply FSUPP'].
  red. red. ins. unfolder in H. desc.
  red. eexists. apply seq_eqv_r. split; eauto.
  red. splits; try by vauto.
  eapply enum_steps_inv; eauto. lia.
Qed. 

Lemma set_finite_set_collect {A B: Type} (S: A -> Prop) (f: A -> B)
      (FIN: set_finite S):
  set_finite (f ↑₁ S). 
Proof. 
  red in FIN. desc. exists (map f findom). 
  ins. apply in_map_iff. red in IN. desc. vauto.
  eexists. split; eauto. 
Qed. 

Lemma fsupp_dom_enum {A: Type} (f: nat -> A) (r: relation A)
      (STEPS: forall i, r (f (i + 1)) (f i))
      (AC: acyclic r)
      (FSUPP: fsupp r^+):
  False.
Proof. 
  eapply fsupp_dom_enum_general with (S := set_full); eauto.
  { eapply fsupp_mori; eauto. red. basic_solver. }
  intros FIN. eapply set_infinite_nat.
  eapply set_finite_mori; eauto. basic_solver. 
Qed. 

(* TODO: move to lib *)
Lemma rel_collect_map {A: Type} (f: nat -> A) r:
  f ↑ (f ↓ r) ⊆ r.
Proof. basic_solver. Qed.

Lemma fsupp_inv_inj {A B: Type} (f: A -> B) (r: relation A)
      (FSUPP: fsupp (f ↑ r))
      (INJ_S: forall (x y: A) (Rx: dom_rel r x) (Ry: dom_rel r y),
          f x = f y -> x = y):
  fsupp r.
Proof. 
  apply fin_dom_rel_fsupp. ins. 
  pose proof (proj2 (fin_dom_rel_fsupp (f ↑ r)) FSUPP).
  eapply set_finite_set_collect_inv_inj.
  2: { ins. eapply INJ_S; eauto; generalize Sx, Sy; basic_solver. }
  rewrite set_collect_dom. eapply set_finite_mori.
  { red. apply dom_rel_mori. apply collect_rel_seq. }
  rewrite collect_rel_eqv. apply H. by apply set_finite_set_collect. 
Qed.

(* TODO: rename? *)
Lemma enum_order_contradiction {A: Type} (f: nat -> A) (r r': relation A) (S: A -> Prop)
      (STEPS: forall i, r (f (i + 1)) (f i))
      (INF_S: ~ set_finite (f ↓₁ S))
      (TOTAL': is_total S r')
      (AC: acyclic r)
      (* (FS': fsupp r'^+) *)
      (FS': fsupp r')
      (SEQ: r^+ ⨾ r' ⊆ r^+):
  False.
Proof.
  forward eapply enum_steps_inv as STEPS'; eauto.  
  forward eapply orders_contradiction with (r1 := r^+) (r2 := r') (S0 := S ∩₁ (f ↑₁ set_full)).  
  { red. ins. unfolder in IWa. unfolder in IWb. desc. subst. rename y0 into x.
    pose proof (NPeano.Nat.lt_trichotomy x y). 
    des; (try by vauto); [right | left]; eauto. }
  { eapply is_total_mori; eauto; [red| ]; basic_solver. }

  intros [EQUIV | CYCLE].
  2: { desc. apply (AC x). apply SEQ. vauto. }

  eapply fsupp_mori in FS'.
  2: { red. etransitivity.
       { apply proj1 in EQUIV. apply EQUIV. }
       basic_solver. }

  eapply fsupp_dom_enum_general; eauto.
  eapply fsupp_mori; eauto. red.
  eapply restr_rel_mori; [reflexivity| ].
  red. ins. split; auto. intros ->. edestruct AC; eauto. 
Qed. 

(* TODO: move to Execution *)
Lemma sb_total t:
  is_total ((E \₁ is_init) ∩₁ Tid_ t) sb. 
Proof.
  red. ins. unfolder in IWa. unfolder in IWb. desc. subst. 
  destruct a, b; try by vauto. simpl in *. subst.
  pose proof (NPeano.Nat.lt_trichotomy index index0) as LT. 
  des; [left | congruence | right]. 
  all: red; apply seq_eqv_lr; splits; vauto. 
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
  assert (forall i, (transp hbp) (f i) (f (i + 1))) as DECR'.
  { ins. red. eapply seq_eqv_l. eauto. }

  pose proof (enum_steps_inv _ _ DECR') as STEPS'. 

  assert (forall x y, f x = f y -> x = y) as F_INJ. 
  { ins. cdes CON.    
    pose proof (NPeano.Nat.lt_trichotomy x y) as LT.
    des; auto;
      destruct (NO_THIN_AIR (f x)); [rewrite H at 1| rewrite H at 2]; 
      specialize (STEPS' _ _ LT); auto.  }

  set (enum_evs := f ↑₁ @set_full nat).
  assert (~ set_finite enum_evs) as INF_ENUM.
  { intros FIN. 
    apply set_finite_set_collect_inv_inj in FIN; auto. by destruct set_infinite_nat. }

  assert (enum_evs ⊆₁ E \₁ is_init) as ENUM_E.
  { subst enum_evs. intros e [i [_ Fie]].
    specialize (DECR i). eapply same_relation_exp in DECR.
    2: { rewrite no_hbp_to_init, wf_hbpE; auto. }
    generalize DECR. subst e. basic_solver. }

  (* TODO: no need to restrict to writes here? *)
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
    
    forward eapply fsupp_dom_enum with (f0 := fun k => f (wb + k))
                                       (r := ⦗set_compl is_init⦘ ⨾ sb) as []. 
    { ins. apply seq_eqv_l. split.
      { apply ENUM_E. vauto. }
      rewrite PeanoNat.Nat.add_assoc. apply SB_STEPS. lia. }
    { eapply acyclic_mori; [| by apply sb_acyclic]. red. basic_solver. }
    eapply fsupp_mori; [| by apply fsupp_sb; eauto]. 
    red. rewrite inclusion_ct_seq_eqv_l.
    rewrite ct_of_trans; vauto. apply sb_trans. }
  

  red in FINTHREADS. 
  forward eapply set_infinite_bunion 
    with (As := flip BinPos.Pos.lt b) (ABs := fun t => f ↓₁ (W ∩₁ Tid_ t)).
  { exists (mk_list (Datatypes.S (BinPos.Pos.to_nat b)) BinPos.Pos.of_nat). intros.
    apply in_mk_list_iff. eexists. split.
    2: { symmetry. apply Pnat.Pos2Nat.id. }
    red in IN. apply Pnat.Pos2Nat.inj_lt in IN. lia. }
  { intros FIN. destruct INFW'.
    rewrite AuxRel2.set_bunion_separation with (fab := tid). 
    rewrite set_map_bunion.
    rewrite AuxRel2.set_full_split with (S := flip BinPos.Pos.lt b).
    rewrite set_bunion_union_l, set_finite_union. split; auto. 
    exists []. ins. unfolder in IN. desc. destruct IN. red. 
    rewrite <- IN1. apply FINTHREADS. apply ENUM_E. vauto. }
  intros [t [TBt INFt]]. red in TBt.
  
  forward eapply set_infinite_bunion 
    with (As := fun l => In l locs) (ABs := fun l => f ↓₁ (W ∩₁ Tid_ t ∩₁ Loc_ l)).
  { vauto. }
  { intros FIN. destruct INFt.
    rewrite AuxRel2.set_bunion_separation with (fab := loc).
    rewrite set_map_bunion.
    rewrite AuxRel2.set_full_split with (S := fun l => In l locs).
    rewrite set_bunion_union_l, set_finite_union. split; auto.
    exists []. ins. unfolder in IN. desc.    
    destruct IN. rewrite <- IN1. apply FINLOCS. apply ENUM_E. vauto. }
  intros [ol [Ll INFtl]].
  destruct ol.
  2: { destruct INFtl. exists []. unfolder. ins. desc.
       forward eapply is_w_loc; eauto. ins. desc. vauto. }

  eapply enum_order_contradiction with (r' := sb ∩ same_loc)
                                       (S := (E \₁ is_init) ∩₁ (W ∩₁ Tid_ t ∩₁ Loc_ (Some l))); eauto.
  { intros FIN. destruct INFtl. eapply set_finite_mori; eauto.
    red. rewrite set_map_inter with (d := _ \₁ _).
    apply set_subset_inter_r. split; [| basic_solver].
    red. ins. red. red in H. apply ENUM_E. vauto. }
  { red. ins. forward eapply (@sb_total t) with (a := a) (b := b0) as SB;
      try by (generalize IWa; generalize IWb; vauto || basic_solver). 
    unfolder in IWa. unfolder in IWb. desc. 
    des; [left | right]; split; congruence. }
  { apply CON. }
  { by apply fsupp_sb_loc. }
  unfold "hbp", "ppop". unfold "hbp", "ppop".
  
  
Admitted.   
  


End immToPowerFairness.
