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
  rewrite set_bunion_separation with (fab := tid).
  rewrite set_map_bunion. 
  rewrite set_full_split with (S := flip BinPos.Pos.lt b).
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
  rewrite set_bunion_separation with (fab := loc).
  rewrite set_map_bunion.
  rewrite set_full_split with (S := fun l => In l locs).
  rewrite set_bunion_union_l, set_finite_union. split; auto.
  exists []. ins. unfolder in IN. desc.    
  destruct IN. rewrite <- IN1. apply FINLOCS. apply IN_E. vauto.
Qed.
  

End HardwareFairness. 
