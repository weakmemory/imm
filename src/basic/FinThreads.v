Require Import Program.Basics.
From hahn Require Import Hahn.
From imm Require Import Execution Events.
Require Import Lia.
Require Import AuxRel2.

Definition fin_threads G := set_finite (threads_set G).

Definition threads_bound (G: execution) (b: thread_id) :=
  forall e (Ge: acts_set G e), BinPos.Pos.lt (tid e) b.

Lemma fin_threads_bound G (WF: Wf G) (FIN : fin_threads G) :
  exists b, threads_bound G b.
Proof using.
  do 2 red in FIN. desf.
  unfold threads_bound.
  enough (exists b, forall t, List.In t findom -> BinPos.Pos.lt t b) as [b HH].
  { exists b. ins. apply HH. apply FIN. now apply WF. }
  clear. induction findom.
  { exists BinPos.xH. ins. }
  desf.
  exists (Basic.Ident.add (BinPos.Pos.max a b) BinPos.xH).
  ins. desf.
  { lia. }
  etransitivity.
  { now apply IHfindom. }
  lia.
Qed.

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

Lemma has_finite_antichains_sb (G: execution) (WF: Wf G) (B : fin_threads G):
  has_finite_antichains (acts_set G \₁ is_init) (⦗set_compl is_init⦘ ⨾ sb G).
Proof using.
  edestruct fin_threads_bound as [b HH]; eauto.
  set (nb := BinPos.Pos.to_nat b).
  red. exists nb. red. ins.  
  cut (exists a b, a <> b /\ In a l /\ In b l /\ tid a = tid b).
  { intro X; desc.
    destruct (INCL _ X0); destruct (INCL _ X1); desc.
    eapply (same_thread G) in X2; unfolder in X2; desf.
    1: exists a, b0. 2: exists b0, a. 
    all: splits; eauto; basic_solver. }
  assert (M: incl (map tid l) (map BinPos.Pos.of_nat (List.seq 0 nb))).
  { red. intros n IN. rewrite in_map_iff in *. destruct IN as [x [TT IN]]; subst.
    exists (BinPos.Pos.to_nat (tid x)). split.
    { apply Pnat.Pos2Nat.id. }
    apply in_seq0_iff.
    subst nb. apply Pnat.Pos2Nat.inj_lt.
    apply HH. now apply INCL. }
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

Lemma thread_bounds_fsupp_ninit_ct G r (WF: Wf G)
      (TB : fin_threads G)
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
  
