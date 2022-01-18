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

