(******************************************************************************)
(** * Definition of IMM PPO  *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob.

Set Implicit Arguments.

Section IMM_PPO.

Variable G : execution.

Notation "'E'" := (acts_set G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'data'" := (data G).
Notation "'addr'" := (addr G).
Notation "'ctrl'" := (ctrl G).
Notation "'rmw_dep'" := (rmw_dep G).

Notation "'fr'" := (fr G).
Notation "'eco'" := (eco G).
Notation "'coe'" := (coe G).
Notation "'coi'" := (coi G).
Notation "'deps'" := (deps G).
Notation "'rfi'" := (rfi G).
Notation "'rfe'" := (rfe G).
Notation "'detour'" := (detour G).

Notation "'lab'" := (lab G).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'fwbob'" := (fwbob G).
Notation "'bob'" := (bob G).

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

Definition ppo := ⦗R⦘ ⨾ (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ rmw ⨾ sb^? ∪ ⦗R_ex⦘ ⨾ sb ∪ rmw_dep)⁺ ⨾ ⦗W⦘.

Definition ar_int := bob ∪ ppo ∪ detour ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘
                     ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R∩₁Acq⦘.

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma ppo_in_sb WF: ppo ⊆ sb.
Proof using.
unfold ppo.
rewrite (addr_in_sb WF), (data_in_sb WF), (ctrl_in_sb WF).
rewrite (rmw_dep_in_sb WF), (rmw_in_sb WF).
arewrite (rfi ⊆ sb).
arewrite_id ⦗R_ex⦘.
generalize (@sb_trans G); ins; relsf.
basic_solver.
Qed.

Lemma rmw_in_ppo WF : rmw ⊆ ppo.
Proof using.
unfold ppo; rewrite (wf_rmwD WF) at 1.
hahn_frame; unfolder; econs; basic_solver 10.
Qed.

Lemma rmw_sb_W_in_ppo WF : rmw ⨾ sb ⨾ ⦗W⦘ ⊆ ppo.
Proof using.
unfold ppo; rewrite (wf_rmwD WF) at 1.
rewrite <- ct_step.
basic_solver 12.
Qed.

Lemma data_in_ppo WF : data ⊆ ppo.
Proof using.
unfold ppo; rewrite (wf_dataD WF) at 1.
hahn_frame; econs; basic_solver 12.
Qed.

Lemma R_ex_sb_in_ppo WF : ⦗R_ex⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ppo.
Proof using.
  arewrite (⦗R_ex⦘ ⊆ ⦗R⦘ ⨾ ⦗R_ex⦘) by type_solver.
  unfold ppo. hahn_frame. rewrite <- ct_step. eauto with hahn.
Qed.

Lemma rmw_sb_cr_W_in_ppo WF : rmw ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppo.
Proof using.
  rewrite crE. rewrite seq_union_l, seq_union_r, seq_id_l.
  rewrite (rmw_sb_W_in_ppo WF).
  rewrite (rmw_in_ppo WF). eauto with hahn hahn_full.
Qed.


(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma wf_ppoE WF : ppo ≡ ⦗E⦘ ⨾ ppo ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold ppo.
arewrite ((data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ rmw ⨾ sb^? ∪ ⦗R_ex⦘ ⨾ sb ∪ rmw_dep)⁺
  ⊆ ⦗E⦘ ⨾ (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ rmw ⨾ sb^?  ∪ ⦗R_ex⦘ ⨾ sb ∪ rmw_dep)⁺ ⨾ ⦗E⦘) at 1.
2: basic_solver 42.
rewrite <- inclusion_ct_seq_eqv_r, <- inclusion_ct_seq_eqv_l.
apply inclusion_t_t.
unfold Execution.rfi.
rewrite (wf_rfE WF), (wf_dataE WF), (wf_rmw_depE WF) at 1.
rewrite (wf_addrE WF), (wf_ctrlE WF), (wf_rmwE WF).
rewrite wf_sbE at 1 2 3 4.
basic_solver 21.
Qed.

Lemma wf_ar_intE WF : ar_int ≡ ⦗E⦘ ⨾ ar_int ⨾ ⦗E⦘.
Proof using.
split; [|basic_solver].
unfold ar_int.
rewrite (wf_bobE WF), (wf_ppoE WF) at 1.
rewrite (wf_detourE WF), (@wf_sbE G), (wf_rfiE WF).
basic_solver 42.
Qed.


(******************************************************************************)
(** ** more properties  *)
(******************************************************************************)

Lemma wf_ppoD: ppo ≡ ⦗R⦘ ⨾ ppo ⨾ ⦗W⦘.
Proof using.
split; [|basic_solver].
unfold ppo; basic_solver.
Qed.

Lemma fwbob_ppo WF: fwbob ⨾ ppo ⊆ fwbob.
Proof using.
rewrite wf_ppoD, (ppo_in_sb WF).
sin_rewrite fwbob_r_sb.
basic_solver.
Qed.

Lemma bob_ppo WF: bob ⨾ ppo ⊆ bob.
Proof using.
rewrite wf_ppoD, (ppo_in_sb WF).
sin_rewrite bob_r_sb.
basic_solver.
Qed.

Lemma ar_int_in_sb WF: ar_int ⊆ sb.
Proof using.
unfold ar_int.
rewrite bob_in_sb.
rewrite (ppo_in_sb WF).
arewrite (detour ⊆ sb).
arewrite (rfi ⊆ sb).
basic_solver 21.
Qed.

Lemma ppo_rfi_ppo : ppo ⨾ rfi ⨾ ppo ⊆ ppo.
Proof using.
unfold ppo.
rewrite !seqA.
arewrite_id ⦗W⦘ at 1.
arewrite_id ⦗R⦘ at 2.
arewrite (rfi ⊆ (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ rmw ⨾ sb^? ∪ ⦗R_ex⦘ ⨾ sb ∪ rmw_dep)＊) at 2.
{ rewrite rtE, <- ct_step. eauto with hahn. }
rewrite inclusion_t_rt at 1.
relsf.
Qed.

Lemma deps_rfi_in_ppo : ⦗R⦘ ⨾ (deps ∪ rfi)⁺ ⨾ ⦗W⦘ ⊆ ppo.
Proof using.
  unfold ppo, Execution.deps.
  hahn_frame.
  apply inclusion_t_t; basic_solver 21.
Qed.

Lemma ppo_alt WF 
  (RMW_DEPS : rmw ⊆ ctrl ∪ data)
  (RMW_CTRL_FAIL : ⦗R_ex⦘ ⨾ sb ⊆ rmw ∪ ctrl)
  (DATA_RMW : data ⨾ ⦗W_ex⦘ ⨾ sb ⊆ ctrl)
  (DEPS_RMW_FAIL : rmw_dep ⨾ (rmw ∪ ctrl) ⊆ ctrl) : 
  ppo ≡ ⦗R⦘ ⨾ (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi)⁺ ⨾ ⦗W⦘.
Proof using.
  generalize (@sb_trans G); ins.
  unfold ppo.
  split.
  2: by hahn_frame; apply inclusion_t_t; basic_solver 12.
  sin_rewrite RMW_CTRL_FAIL; rewrite <- !unionA.
  arewrite (rmw ⨾ sb^? ⊆ ctrl ∪ data).
  { rewrite rmw_W_ex, !seqA.
    rewrite RMW_DEPS.
    rewrite seq_union_l. unionL.
    { generalize (ctrl_sb WF). clear. basic_solver 10. }
    generalize DATA_RMW. clear. basic_solver 10. }
  arewrite (data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ (ctrl ∪ data)
                 ∪ rmw ∪ ctrl ∪ rmw_dep ⊆
            data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ rmw_dep).
  { rewrite RMW_DEPS. unionL; eauto with hahn. }
 
  rewrite path_ut_first; relsf; unionL.
  { hahn_frame. apply inclusion_t_t. basic_solver 12. }
  arewrite ((data ∪ ctrl ∪ addr ⨾ sb^? ∪ rfi ∪ rmw_dep) ⊆ sb).
  { rewrite (data_in_sb WF), (addr_in_sb WF), (ctrl_in_sb WF).
    arewrite (rfi ⊆ sb).
    rewrite (rmw_dep_in_sb WF).
    relsf. }
  relsf.
  rewrite (dom_r (wf_rmw_depD WF)), !seqA.
  rewrite (crE sb) at 2; relsf; unionL.
  { rewrite R_ex_in_R; type_solver. }
  hahn_frame.
  sin_rewrite RMW_CTRL_FAIL.
  rewrite DEPS_RMW_FAIL.
  rewrite ct_end.
  apply inclusion_seq_mon; [apply inclusion_rt_rt|]; basic_solver 42.
Qed.

Lemma bob_in_ar_int : bob ⊆ ar_int.
Proof using. unfold ar_int. basic_solver 10. Qed.

Lemma ppo_in_ar_int : ppo ⊆ ar_int.
Proof using. unfold ar_int. basic_solver 10. Qed.

Lemma detour_in_ar_int : detour ⊆ ar_int.
Proof using. unfold ar_int. basic_solver 10. Qed.

Lemma w_ex_acq_sb_w_in_ar_int : ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ar_int.
Proof using. unfold ar_int. basic_solver 10. Qed.

Lemma W_ex_rfi_Acq_in_ar_int : ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R∩₁Acq⦘ ⊆ ar_int.
Proof using. unfold ar_int. basic_solver 10. Qed.

Lemma bob_ppo_W_sb WF :
  (bob ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺ ⊆ ppo ∪ ppo ^? ⨾ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺.
Proof using.
arewrite (bob ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆
         (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘) ∪ ppo).
basic_solver 12.
apply ct_ind_left with (P:= fun r =>  r).
by auto with hahn.
- arewrite(bob ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺).
  arewrite(⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺) at 2.
  basic_solver 12.
- intros k H. rewrite H; clear k H; rewrite crE; relsf; unionL.
+ rewrite (bob_ppo WF). 
  arewrite(bob ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)⁺).
  basic_solver.
+ rewrite (wf_ppoD) at 1. type_solver.
+ rewrite (wf_ppoD) at 1 2. type_solver.
+ arewrite(bob ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)＊); relsf.
+ sin_rewrite (bob_ppo WF). 
  arewrite(bob ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)＊); relsf.
+ arewrite(⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ (bob ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘)＊) at 1; relsf.
+ rewrite (wf_ppoD) at 1. type_solver.
+ basic_solver 12.
+ rewrite (wf_ppoD) at 1 2. type_solver.
Qed.

End IMM_PPO.
