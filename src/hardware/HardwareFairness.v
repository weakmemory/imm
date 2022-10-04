(******************************************************************************)
(** * Helper lemmas for proving prefix-finiteness                             *)
(** * of model-specific "hb" relations.                                       *)
(******************************************************************************)

From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import ImmFair.
Require Import FairExecution.
Require Import FinThreads.
Require Import Lia.
Require Import ClassicalChoice.
Require Import ChoiceFacts.
Require Import IndefiniteDescription. 
Require Import AuxRel2.
Require Import AuxDef.
Require Import Program.Basics.
Import ListNotations.
Require Import EnumProperties.


Set Implicit Arguments.

Section HardwareFairness.

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

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'Loc_' l" := (fun x => loc x = l) (at level 1).

Lemma enum_steps_inv {A: Type} (r: relation A) (f: nat -> A)
      (STEPS: forall i : nat, r (f (i + 1)) (f i)):
  ⟪STEPS: forall i j (LT: i < j), r^+ (f j) (f i) ⟫.
Proof using.
  red. 
  ins. fold (transp r⁺ (f i) (f j)). apply transp_ct.
  apply enum_steps; auto. 
Qed.

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

Lemma fsupp_dom_enum_general {A: Type} (f: nat -> A) (r: relation A) (S: A -> Prop)
      (STEPS: forall i, r (f (i + 1)) (f i))
      (AC: acyclic r)
      (FSUPP: fsupp (restr_rel (S ∩₁ f ↑₁ set_full) r^+))
      (INF_S': ~ set_finite (f ↓₁ S)):
  False.
Proof using.
  pose proof (proj2 (fin_dom_rel_fsupp _) FSUPP) as FSUPP'.

  forward eapply (@set_infinite_has_element _ _ INF_S')  as [ie1 Ie1].
  specialize (FSUPP' (eq (f ie1))). specialize_full FSUPP'; [by exists [f ie1]; vauto| ].

  eapply set_finite_mori in FSUPP'.
  2: { red. apply set_collect_map with (f := f). }
  apply set_finite_set_collect_inv_inj in FSUPP'.
  2: { ins. eapply enum_inj with (r := transp r); eauto.
       by apply acyclic_transp. }

  destruct INF_S'.
  rewrite <- set_inter_full_r with (s := _ ↓₁ _). 
  rewrite set_full_split with (S := ge ie1), set_inter_union_r.
  apply set_finite_union. split.
  { exists (List.seq 0 (ie1 + 1)). ins. unfolder in IN. desc. 
    apply in_seq. lia. }

  eapply set_finite_mori; [| by apply FSUPP'].
  red. red. ins. unfolder in H. desc.
  red. eexists. apply seq_eqv_r. split; eauto.
  red. splits; try by vauto.
  eapply enum_steps_inv; eauto. lia.
Qed. 

Lemma fsupp_dom_enum {A: Type} (f: nat -> A) (r: relation A)
      (STEPS: forall i, r (f (i + 1)) (f i))
      (AC: acyclic r)
      (FSUPP: fsupp r^+):
  False.
Proof using. 
  eapply fsupp_dom_enum_general with (S := set_full); eauto.
  { eapply fsupp_mori; eauto. red. basic_solver. }
  intros FIN. eapply set_infinite_nat.
  eapply set_finite_mori; eauto. basic_solver. 
Qed. 

Lemma fsupp_inv_inj {A B: Type} (f: A -> B) (r: relation A)
      (FSUPP: fsupp (f ↑ r))
      (INJ_S: forall (x y: A) (Rx: dom_rel r x) (Ry: dom_rel r y),
          f x = f y -> x = y):
  fsupp r.
Proof using. 
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
      (FS': fsupp r')
      (SEQ: r^+ ⨾ r' ⊆ r^+):
  False.
Proof using.
  forward eapply enum_steps_inv as STEPS'; eauto.  
  forward eapply orders_contradiction with (r1 := r^+) (r2 := r') (S := S ∩₁ (f ↑₁ set_full)).  
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
  

End HardwareFairness. 
