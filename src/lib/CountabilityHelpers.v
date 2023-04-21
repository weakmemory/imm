From hahn Require Import Hahn.
Require Import SetSize.
Require Import Lia.
Require Import PeanoNat.
Require Import IndefiniteDescription.

(* TODO: find exising definitions? *)
Definition isomorphism {A B: Type} (fab: A -> B) (fba: B -> A) :=
  (forall a, fba (fab a) = a) /\ (forall b, fab (fba b) = b).

Lemma isomorphism_sym {A B: Type} (fab: A -> B) (fba: B -> A)
      (ISO: isomorphism fab fba):
  isomorphism fba fab.
Proof using. unfold isomorphism in *. tauto. Qed. 


Lemma isomorphism_fin_inf {A B: Type} (fab: A -> B) (fba: B -> A)
      (ISO: isomorphism fab fba)
      (FINA: set_finite (@set_full A))
      (INFB: ~ set_finite (@set_full B)):
  False.
Proof using. 
  destruct INFB. destruct FINA as [la LA]. 
  exists (map fab la). ins.
  apply in_map_iff. exists (fba x). split; auto. apply ISO.
Qed.

Lemma filterP_set_full {A: Type} (l: list A):
  filterP set_full l = l.
Proof using.
  induction l; vauto. simpl.
  destruct excluded_middle_informative; [congruence | by destruct n]. 
Qed.

Lemma isomorphism_dom_len_helper {A B: Type} (fab: A -> B) (fba: B -> A)
      (la: list A) (lb: list B)
      (ISO: isomorphism fab fba)
      (LA: forall x : A, set_full x -> In x la)                                
      (LB: forall x : B, set_full x -> In x lb):
  length (undup la) <= length (undup lb).
Proof using.
  rewrite <- map_length with (f := fab).
  apply NoDup_incl_length.
  2: { red. intros b INb. apply in_undup_iff. intuition (auto with *). }
  apply FinFun.Injective_map_NoDup; [| apply nodup_undup].
  red. ins. apply f_equal with (f := fba) in H.
  destruct ISO. congruence. 
Qed. 

(* It can be generalized to subsets, but currently we don't need it *)
Lemma set_size_full_isomorphic {A B: Type} (fab: A -> B) (fba: B -> A)
      (ISO: isomorphism fab fba):
  set_size (@set_full A) = set_size (@set_full B).
Proof using.
  unfold set_size. do 2 destruct excluded_middle_informative; auto; cycle 1.
  { destruct constructive_indefinite_description as [la LA]. simpl.
    edestruct @isomorphism_fin_inf; eauto. }
  { destruct constructive_indefinite_description as [lb LB]. simpl.
    edestruct (@isomorphism_fin_inf B A); eauto.
    apply isomorphism_sym. eauto. }

  f_equal.
  destruct constructive_indefinite_description as [la LA].
  destruct constructive_indefinite_description as [lb LB].
  simpl in *. rewrite !filterP_set_full. 
  
  apply NPeano.Nat.le_antisymm.
  { eapply isomorphism_dom_len_helper; eauto. }
  apply isomorphism_sym in ISO. eapply isomorphism_dom_len_helper; eauto.
Qed.

Lemma countable_isomorphic {A B: Type} (fab: A -> B) (fba: B -> A)
      (ISO: isomorphism fab fba)
      (CNT: countable (@set_full A)):
  countable (@set_full B).
Proof using.
  unfold countable in *. des.
  { left. intros BB. destruct CNT. inversion BB.
    eauto. }
  cdes ISO.
  forward eapply isomorphism_sym as ISO'; eauto. 
  right. exists (fun n => fab (nu n)).
  apply enumeratesE'. apply enumeratesE' in CNT. desc. simpl. splits.
  { ins. }
  { ins. apply f_equal with (f := fba) in H1.
    erewrite set_size_full_isomorphic in H, H0; eauto; cycle 1. 
    rewrite !ISO0 in H1. apply INJ; auto. }
  ins. specialize (IND (fba a)). specialize_full IND; [done| ]. desc.
  exists i. split.
  2: { rewrite IND0. auto. }
  erewrite set_size_full_isomorphic; eauto.
Qed.

Lemma countable_prod {A B: Type}
      (CNTA: countable (@set_full A)) (CNTB: countable (@set_full B)):
  countable (@set_full (A * B)).
Proof using.
  unfold countable in *. des. 
  2: left; intros [INH]; apply CNTB; econstructor; apply INH.
  1, 2: left; intros [INH]; apply CNTA; econstructor; apply INH.
  
  rename nu0 into nuA, nu into nuB.
  set (nuAB := (fun i => (nuA (nat_fst i), nuB (nat_snd i)))).
  apply surjection_countable with (f := nuAB).
  intros [a b] _.
  apply enumeratesE' in CNTA. apply enumeratesE' in CNTB. desc.
  specialize (IND0 a I). specialize (IND b I). desc.
  exists (nat_tup i0 i). subst nuAB. simpl.
  rewrite nat_fst_tup, nat_snd_tup. congruence. 
Qed. 

Lemma empty_sum_isomorphism_l {A B: Type} (NB: ~ inhabited B):
  exists (fab: A -> A + B) fba, isomorphism fab fba.
Proof using.
  exists (fun a => inl a).
  exists (fun ab => match ab with | inl a => a
                     | inr b => False_rect A (NB (inhabits b)) end).
  split; auto. ins. destruct b; vauto.
Qed.     

Lemma countable_sum {A B: Type}
      (CNTA: countable (@set_full A)) (CNTB: countable (@set_full B)):
  countable (@set_full (A + B)).
Proof using.
  unfold countable in *. des. 
  { left. intros [INH]. destruct INH; auto. }
  { apply surjection_countable with (f := fun i => inl (nu i)).
    ins. destruct a; [| by destruct CNTB].
    apply enumeratesE' in CNTA. desc.
    specialize (IND a I). desc. exists i. congruence. }  
  { apply surjection_countable with (f := fun i => inr (nu i)).
    ins. destruct a; [by destruct CNTA|].
    apply enumeratesE' in CNTB. desc.
    specialize (IND b I). desc. exists i. congruence. }

  apply surjection_countable with
      (f := fun n => if (Nat.even n)
                  then (inl (nu0 (Nat.div2 n)))
                  else (inr (nu (Nat.div2 n)))).
  ins. destruct a as [a | b].
  { apply enumeratesE' in CNTA. desc. specialize (IND a I). desc.
    exists (2 * i). rewrite <- Nat.add_0_l at 1. rewrite Nat.even_add_mul_2.
    simpl. f_equal. fold (2 * i). by rewrite Nat.div2_double. }
  apply enumeratesE' in CNTB. desc. specialize (IND b I). desc.
  exists (2 * i + 1). rewrite NPeano.Nat.add_comm at 1. 
  rewrite <- Nat.add_0_l at 1.
  rewrite Nat.add_assoc. rewrite Nat.even_add_mul_2. 
  simpl. f_equal. fold (2 * i).
  by rewrite Nat.add_1_r, NPeano.Nat.div2_succ_double. 
Qed.


Lemma pos_countable: countable (@set_full BinNums.positive).
Proof using.
  apply surjection_countable with (f := BinPos.Pos.of_nat). 
  ins. exists (BinPos.Pos.to_nat a). apply Pnat.Pos2Nat.id.
Qed. 

Lemma nat_countable: countable (@set_full nat).
Proof using. apply surjection_countable with (f := id). vauto. Qed.     
