Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import Lia.

Require Import Events.
Require Import Execution.
Require Import imm_s.
Require Import imm_s_ppo.
Require Import imm_s_rfppo.
Require Import TraversalConfig.
Require Import Traversal.
Require Import SimTraversal.
Require Import SimTraversalProperties.
Require Import AuxDef.

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
  
  Definition ord G sc (l l' : t) :=
    forall TC (TCCOH : tc_coherent G sc TC)
           (INA : TravAction.get TC (action l') (event l')),
      TravAction.get TC (action l) (event l).
  
  Definition strict_ord G sc := ord G sc \ eq.
  
  Lemma strict_ord_irreflexive G sc : irreflexive (strict_ord G sc).
  Proof using. unfold strict_ord. basic_solver. Qed.

  Lemma ord_transitive G sc : transitive (ord G sc).
  Proof using.
    red. intros x y z XY YZ.
  Admitted.

  Lemma strict_ord_transitive G sc : transitive (strict_ord G sc).
    red. intros x y z XY YZ.
    split.
    { eapply ord_transitive; [apply XY|apply YZ]. }
  Admitted.
  
  Lemma strict_ord_acyclic G sc : acyclic (strict_ord G sc).
  Proof using.
  Admitted.

  Lemma strict_ord_fsupp G sc
        (NOSC  : acts_set G ∩₁ is_f (lab G) ∩₁ is_sc (lab G) ⊆₁ ∅)
        (FSUPP : fsupp (ar G sc ∪ rf G ⨾ ppo G ∩ same_loc (lab G))⁺) :
    fsupp (strict_ord G sc).
  Proof using.
  Admitted.
  
  (* NEXT TODO: Combination of strict_ord_fsupp and strict_ord_acyclic should
                allow to get lineralization of traversal actions.
   *)
End TravLabel.
