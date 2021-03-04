(******************************************************************************)
(** * Definition of the Power memory model *)
(******************************************************************************)
From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.

Set Implicit Arguments.

Section Power_fences.

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
(* Notation "'ctrli'" := (ctrli G). *)
Notation "'deps'" := (deps G).
Notation "'fre'" := (fre G).
Notation "'rfe'" := (rfe G).
Notation "'coe'" := (coe G).
Notation "'rfi'" := (rfi G).
Notation "'fri'" := (fri G).
Notation "'fr'" := (fr G).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'F^lwsync'" := (F ∩₁ (fun a => is_true (is_ra lab a))).
Notation "'F^sync'" := (F ∩₁ (fun a => is_true (is_sc lab a))).

Implicit Type WF : Wf G.

Definition sync := ⦗RW⦘ ⨾ sb ⨾ ⦗F^sync⦘ ⨾ sb ⨾ ⦗RW⦘.
Definition lwsync := (⦗RW⦘ ⨾ sb ⨾ ⦗F^lwsync⦘ ⨾ sb ⨾ ⦗RW⦘) \ (fun x y => W x /\ R y).
Definition fence := sync ∪ lwsync.

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_syncE WF: sync ≡ ⦗E⦘ ⨾ sync ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold sync.
rewrite (wf_sbE) at 1 2.
basic_solver 42.
Qed.

Lemma wf_lwsyncE WF: lwsync ≡ ⦗E⦘ ⨾ lwsync ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold lwsync.
rewrite (wf_sbE) at 1 2.
basic_solver 42.
Qed.

Lemma wf_fenceE WF: fence ≡ ⦗E⦘ ⨾ fence ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold fence.
rewrite (wf_syncE WF) at 1.
rewrite (wf_lwsyncE WF) at 1.
basic_solver 42.
Qed.

(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

Lemma wf_syncD WF: sync ≡ ⦗RW⦘ ⨾ sync ⨾ ⦗RW⦘.
Proof using.
split; [|basic_solver].
unfold sync.
basic_solver 42.
Qed.

Lemma wf_lwsyncD WF: lwsync ≡ ⦗RW⦘ ⨾ lwsync ⨾ ⦗RW⦘.
Proof using.
split; [|basic_solver].
unfold lwsync.
basic_solver 42.
Qed.

Lemma wf_fenceD WF: fence ≡ ⦗RW⦘ ⨾ fence ⨾ ⦗RW⦘.
Proof using.
split; [|basic_solver].
unfold fence.
rewrite (wf_syncD WF) at 1.
rewrite (wf_lwsyncD WF) at 1.
basic_solver 42.
Qed.

(******************************************************************************)
(** ** Properties *)
(******************************************************************************)

Lemma sync_in_sb : sync ⊆ sb.
Proof using.
unfold sync; generalize (@sb_trans G); basic_solver.
Qed.

Lemma lwsync_alt : lwsync ≡ 
  ⦗R⦘ ⨾ sb ⨾ ⦗F^lwsync⦘ ⨾ sb ⨾ ⦗RW⦘ ∪ ⦗W⦘ ⨾ sb ⨾ ⦗F^lwsync⦘ ⨾ sb ⨾ ⦗W⦘.
Proof using.
unfold lwsync.
split.
by apply inclusion_minus_l; basic_solver 12.
by unfolder; ins; desf; splits; eauto 10; intro; type_solver.
Qed.

Lemma lwsync_in_sb : lwsync ⊆ sb.
Proof using.
rewrite lwsync_alt.
generalize (@sb_trans G); basic_solver.
Qed.

Lemma fence_in_sb : fence ⊆ sb.
Proof using.
unfold fence.
rewrite sync_in_sb, lwsync_in_sb.
basic_solver.
Qed.

Lemma sync_sb_w_in_sync WF : sync ⨾ sb ⨾ ⦗W⦘ ⊆ sync.
Proof using.
unfold sync.
generalize (@sb_trans G).
basic_solver 20.
Qed.

Lemma sync_fri_in_sync WF : sync ⨾ fri ⊆ sync.
Proof using.
rewrite (wf_friD WF).
ie_unfolder.
generalize (sync_sb_w_in_sync WF).
basic_solver 12.
Qed.

Lemma lwsync_sb_w_in_lwsync WF : lwsync ⨾ sb ⨾ ⦗W⦘ ⊆ lwsync.
Proof using.
rewrite lwsync_alt.
generalize (@sb_trans G).
basic_solver 20.
Qed.

Lemma lwsync_fri_in_lwsync WF : lwsync ⨾ fri ⊆ lwsync.
Proof using.
rewrite (wf_friD WF).
ie_unfolder.
generalize (lwsync_sb_w_in_lwsync WF).
basic_solver 12.
Qed.

Lemma fence_sb_w_in_fence WF : fence ⨾ sb ⨾ ⦗W⦘ ⊆ fence ⨾ ⦗W⦘.
Proof using.
unfold fence.
generalize (sync_sb_w_in_sync WF) (lwsync_sb_w_in_lwsync WF).
basic_solver 12.
Qed.

Lemma fence_fri_in_fence WF : fence ⨾ fri ⊆ fence.
Proof using.
unfold fence.
generalize (sync_fri_in_sync WF) (lwsync_fri_in_lwsync WF).
basic_solver 12.
Qed.

Lemma RW_sb_sync_in_sync : ⦗RW⦘ ⨾ sb ⨾ sync ⊆ sync.
Proof using.
unfold sync.
generalize (@sb_trans G).
basic_solver 12.
Qed.

Lemma RW_sb_lwsync_in_lwsync : ⦗RW⦘ ⨾ sb ⨾ lwsync ⨾ ⦗W⦘ ⊆ lwsync.
Proof using.
rewrite lwsync_alt.
generalize (@sb_trans G).
basic_solver 20.
Qed.

Lemma RW_sb_fence_in_fence WF: ⦗RW⦘ ⨾ sb ⨾ fence ⨾ ⦗W⦘ ⊆ fence.
Proof using.
unfold fence.
generalize (RW_sb_sync_in_sync) (RW_sb_lwsync_in_lwsync).
basic_solver 12.
Qed.

Lemma RW_sb_F_sb_W_in_fence : ⦗RW⦘ ⨾ sb ⨾ ⦗F^lwsync⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ fence.
Proof using.
unfold fence; rewrite lwsync_alt.
basic_solver 20.
Qed.

Lemma R_sb_F_sb_RW_in_fence : ⦗R⦘ ⨾ sb ⨾ ⦗F^lwsync⦘ ⨾ sb ⨾ ⦗RW⦘ ⊆ fence.
Proof using.
unfold fence; rewrite lwsync_alt.
basic_solver 12.
Qed.

Proposition sync_trans : transitive sync.
Proof using.
unfold sync.
apply transitiveI.
arewrite_id ⦗F^sync⦘ at 2; rels.
arewrite_id ⦗RW⦘ at 2; rels.
generalize (@sb_trans G).
basic_solver 42.
Qed.

Proposition lwsync_trans : transitive lwsync.
Proof using.
apply transitiveI.
rewrite lwsync_alt at 2.
arewrite_id !⦗F^lwsync⦘; rels.
sin_rewrite !(rewrite_trans (@sb_trans G)).
arewrite_id ⦗W⦘ at 1; rels.
rewrite lwsync_alt.
arewrite_id ⦗RW⦘ at 1; rels.
relsf.
rewrite !seqA.
arewrite_false (⦗W⦘ ⨾ ⦗R⦘). 
by type_solver.
rels.
arewrite_id ⦗R⦘ at 2; rels.
arewrite_id ⦗W⦘ at 3; rels.
sin_rewrite !(rewrite_trans (@sb_trans G)).
basic_solver 12.
Qed.

Proposition lwsync_sync : lwsync ⨾ sync ⊆ sync.
Proof using.
unfold lwsync, sync.
arewrite_id ⦗F^lwsync⦘.
generalize (@sb_trans G).
basic_solver 42.
Qed.

Proposition sync_lwsync : sync ⨾ lwsync ⊆ sync.
Proof using.
unfold lwsync, sync.
arewrite_id ⦗F^lwsync⦘.
generalize (@sb_trans G).
basic_solver 42.
Qed.

Proposition fence_trans : transitive fence.
Proof using.
unfold fence. 
apply transitiveI.
relsf.
sin_rewrite !(rewrite_trans sync_trans).
sin_rewrite !(rewrite_trans lwsync_trans).
sin_rewrite lwsync_sync.
sin_rewrite sync_lwsync.
basic_solver 12.
Qed.

Lemma rf_fence_W_in_fence WF: rf^? ⨾ fence ⨾ ⦗W⦘ ⊆ rfe^? ⨾ fence ⨾ ⦗W⦘.
Proof using.
rewrite (dom_l (wf_rfD WF)) at 1.
rewrite (@rfi_union_rfe G) at 1 3.
arewrite(rfi ⊆ sb).
generalize (RW_sb_fence_in_fence WF).
basic_solver 42.
Qed.

End Power_fences.
