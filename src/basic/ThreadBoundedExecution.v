Require Import Program.Basics.
From hahn Require Import Hahn.
From imm Require Import Execution Events.
Require Import Lia.


Definition threads_bound (G: execution) (b: thread_id) :=
  forall e (Ge: acts_set G e), BinPos.Pos.lt (tid e) b.

Lemma BinPos_lt_fin b:
  set_finite (fun t => BinPos.Pos.lt t b). 
Proof using.
  exists (map BinPos.Pos.of_nat (List.seq 0 (BinPos.Pos.to_nat b))).
  ins. apply Pnat.Pos2Nat.inj_lt in IN. 
  apply in_map_iff. eexists. splits.
  { by apply Pnat.Pos2Nat.id. }
  apply in_seq. lia.
Qed. 

Lemma dupE A (l : list A) (DUP: ~ NoDup l) :
  exists l1 a l2 l3, l = l1 ++ a :: l2 ++ a :: l3.
Proof using.
  induction l; ins.
  rewrite nodup_cons in *; clarify_not.
    by apply in_split in DUP; desf; exists nil; ins; eauto.
  specialize (IHl DUP); desf; eexists (_ :: _); ins; eauto.
Qed.

Lemma has_finite_antichains_sb (G: execution) b (WF: Wf G) (B: threads_bound G b):
  has_finite_antichains (acts_set G \₁ is_init) (⦗set_compl is_init⦘ ⨾ sb G).
Proof using.
  set (nb := BinPos.Pos.to_nat b). 
  red. exists nb. red. ins.  
  cut (exists a b, a <> b /\ In a l /\ In b l /\ tid a = tid b).
  { intro X; desc.
    destruct (INCL _ X0); destruct (INCL _ X1); desc.
    eapply (same_thread G) in X2; unfolder in X2; desf.
    1: exists a, b0. 2: exists b0, a. 
    all: splits; eauto; basic_solver. }
  assert (M: incl (map tid l) (map BinPos.Pos.of_nat (List.seq 0 nb))).
  { red; ins; rewrite in_map_iff in *; desf.
    exists (BinPos.Pos.to_nat (tid x)). split.
    { apply Pnat.Pos2Nat.id. }
    apply in_seq0_iff.
    subst nb. apply Pnat.Pos2Nat.inj_lt.
    apply B, INCL. auto. }
  destruct (classic (NoDup (map tid l))).
  { eapply NoDup_incl_length in M; ins.
    rewrite !length_map, length_seq in *. lia. }
  apply dupE in H; desf.
  apply map_eq_app_inv in H; desf.
  destruct l2'; ins; desf.
  apply map_eq_app_inv in H0; desf.
  destruct l2'0; ins; desf.
  exists a0, a; splits; eauto with hahn.
  intro; desf; rewrite nodup_app, nodup_cons in *; desf; eauto with hahn.
Qed.


(* TODO: move to hahn *)
Lemma clos_trans_domb_l {B: Type} (r: relation B) (s: B -> Prop)
      (DOMB_S: domb r s):
  ⦗s⦘ ⨾ r^+ ⊆ (⦗s⦘ ⨾ r ⨾ ⦗s⦘)^+.
Proof using.
  erewrite (@domb_rewrite _ r) at 1; eauto.
  rewrite <- seq_eqvK at 2. rewrite <- seqA. rewrite ct_rotl.
  do 2 rewrite <- seqA. rewrite <- ct_begin. basic_solver. 
Qed.

Lemma thread_bounds_fsupp_ninit_ct G b r (WF: Wf G)
      (TB: threads_bound G b)
      (SB_R: sb G ⊆ r)
      (AC_R: acyclic r)
      (R_NI: domb r (set_compl is_init))
      (E_R: doma r (acts_set G))
      (FS_R: fsupp (⦗set_compl is_init⦘ ⨾ r)):
  fsupp (⦗set_compl is_init⦘ ⨾ r^+). 
Proof using.
  eapply fsupp_mori.
  { red. rewrite clos_trans_domb_l; auto. 
    eapply clos_trans_mori. rewrite <- seqA. apply inclusion_seq_eqv_r. }
  eapply fsupp_ct with (s := acts_set G \₁ is_init); auto.
  { eapply acyclic_mori; eauto. red. basic_solver. }
  { erewrite doma_rewrite with (r := r); eauto. basic_solver. } 
  eapply has_finite_antichains_mori; [reflexivity| ..]; eauto. 
  2: { eapply has_finite_antichains_sb; eauto. }
  basic_solver.  
Qed.  
  
