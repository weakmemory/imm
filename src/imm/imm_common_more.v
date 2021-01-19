(******************************************************************************)
(** * More Lemmas about imm_common *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_s_ppo.
Require Import imm_bob.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section IMM.

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
Notation "'fwbob'" := (fwbob G).
Notation "'bob'" := (bob G).
Notation "'ppo'" := (ppo G).
Notation "'ar_int'" := (ar_int G).

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
Notation "'R_ex'" := (R_ex G).
Notation "'W_ex'" := (W_ex G).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

Implicit Type WF : Wf G.
Implicit Type COMP : complete G.


Lemma ct_ar_int_alt1 WF: (ar_int)⁺ ⊆ 
sb^? ⨾ ⦗F∩₁Acq/Rel⦘ ⨾ sb ∪
⦗R∩₁Acq⦘ ⨾ sb ∪
(sb ⨾ ⦗W∩₁Rel⦘ ∪ ⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘ ∪
  sb ⨾ ⦗F∩₁Acq/Rel⦘ ∪
  detour ⨾ (⦗R∩₁Acq⦘ ⨾ sb)^? ∪ 
  ppo  ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R∩₁Acq⦘ ⨾ sb^?)⁺.
Proof using.
assert (helper: 
(sb ⨾ ⦗W ∩₁ Rel⦘ ∪ ⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ∪ sb ⨾ ⦗F ∩₁ Acq/Rel⦘
 ∪ ppo ∪ detour ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘)＊
⊆
(sb ⨾ ⦗W ∩₁ Rel⦘ ∪ ⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘
∪ sb ⨾ ⦗F ∩₁ Acq/Rel⦘ ∪ detour ⨾ (⦗R∩₁Acq⦘ ⨾ sb)^? ∪ ppo ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R∩₁Acq⦘ ⨾ sb^?)＊).
by apply inclusion_rt_rt; basic_solver 12.

unfold imm_s_ppo.ar_int, imm_bob.bob, imm_bob.fwbob.

arewrite (sb ⨾ ⦗W ∩₁ Rel⦘ ∪ ⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ∪ sb ⨾ ⦗F ∩₁ Acq/Rel⦘
 ∪ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb ∪ ⦗R ∩₁ Acq⦘ ⨾ sb ∪ ppo ∪ detour
 ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⊆
sb ⨾ ⦗W ∩₁ Rel⦘ ∪ ⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ∪ sb ⨾ ⦗F ∩₁ Acq/Rel⦘
  ∪ ppo ∪ detour
 ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ∪ (⦗R ∩₁ Acq⦘ ⨾ sb ∪ ⦗F ∩₁ Acq/Rel⦘ ⨾ sb)) at 1.
basic_solver 12.

rewrite path_ut_first; rels; unionL.
by unionR right; apply inclusion_t_t; basic_solver 12.
arewrite (sb ∩ same_loc ⊆ sb) at 2.
rewrite detour_in_sb, (ppo_in_sb WF) at 2.
arewrite (rfi ⊆ sb) at 2.
arewrite_id ⦗W_ex_acq⦘ at 2.
arewrite_id ⦗W_ex⦘ at 2.
arewrite_id ⦗W⦘ at 3.
arewrite_id ⦗R ∩₁ Acq⦘ at 3.
arewrite_id ⦗R ∩₁ Acq⦘ at 3.
arewrite_id  ⦗W ∩₁ Rel⦘ at 3.
arewrite_id  ⦗W ∩₁ Rel⦘ at 3.
arewrite_id ⦗W⦘ at 3.
arewrite_id ⦗F ∩₁ Acq/Rel⦘ at 3.
arewrite_id ⦗F ∩₁ Acq/Rel⦘ at 3.
generalize (@sb_trans G); ins; relsf.
rewrite !seqA; relsf.
unionL.
- rewrite rtE; relsf; unionL; [basic_solver 12|].
  unionR right.
  rewrite ct_end; relsf; unionL.
  * type_solver.
  * type_solver.
  * type_solver.
  * rewrite (dom_r (@wf_ppoD G)) at 2; type_solver.
  * rewrite ct_end, helper; basic_solver 40.
  * type_solver.
  * rewrite ct_end, helper; basic_solver 40.
- arewrite (sb ∩ same_loc ⊆ sb) at 1.
  rewrite detour_in_sb, (ppo_in_sb WF) at 1.
  arewrite_id ⦗W_ex_acq⦘ at 1.
  arewrite_id ⦗W⦘ at 1.
  arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
  arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
  arewrite_id ⦗W⦘ at 1.
  arewrite_id ⦗F ∩₁ Acq/Rel⦘ at 1.
  arewrite (rfi ⊆ sb) at 1.
  arewrite_id  ⦗R ∩₁ Acq⦘ at 1.
  arewrite_id  ⦗W_ex⦘ at 1.
  relsf.
Qed.

Lemma ct_ar_int_alt2 WF: 
 (sb ⨾ ⦗W∩₁Rel⦘ ∪ ⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘ ∪
  sb ⨾ ⦗F∩₁Acq/Rel⦘ ∪ detour ⨾ (⦗R∩₁Acq⦘ ⨾ sb)^? ∪ 
  ppo  ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb^?)⁺ ⊆ 
sb ⨾ ⦗F∩₁Acq/Rel⦘ ⨾ sb^? ∪
(sb ⨾ ⦗W∩₁Rel⦘ ∪ ⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘ ∪
  detour ⨾ (⦗R∩₁Acq⦘ ⨾ sb)^? ∪ 
  ppo  ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb^?)⁺.
Proof using.

arewrite (sb ⨾ ⦗W∩₁Rel⦘ ∪ ⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘ ∪
  sb ⨾ ⦗F∩₁Acq/Rel⦘ ∪ detour ⨾ (⦗R∩₁Acq⦘ ⨾ sb)^? ∪ 
  ppo  ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb^? ⊆
sb ⨾ ⦗W∩₁Rel⦘ ∪ ⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘ 
 ∪ detour ⨾ (⦗R∩₁Acq⦘ ⨾ sb)^? ∪ 
  ppo  ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb^? ∪
  sb ⨾ ⦗F∩₁Acq/Rel⦘) at 1.
basic_solver 12.

rewrite path_ut_first; rels; unionL.
by unionR right; apply inclusion_t_t; basic_solver 12.
arewrite (sb ∩ same_loc ⊆ sb) at 1.
arewrite (sb ∩ same_loc ⊆ sb) at 1.
rewrite detour_in_sb, (ppo_in_sb WF) at 1 2.

arewrite_id ⦗W⦘ at 1.
arewrite_id ⦗W⦘ at 1.
arewrite_id ⦗W⦘ at 1.
arewrite_id ⦗W⦘ at 1.
arewrite_id ⦗R ∩₁ Acq⦘ at 1.
arewrite_id ⦗R ∩₁ Acq⦘ at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id  ⦗W_ex_acq⦘ at 1.
arewrite_id  ⦗W_ex_acq⦘ at 1.

arewrite_id ⦗F ∩₁ Acq/Rel⦘ at 2.
  arewrite (rfi ⊆ sb) at 1.
  arewrite_id  ⦗R ∩₁ Acq⦘ at 1.
  arewrite_id  ⦗W_ex⦘ at 1.
  arewrite (rfi ⊆ sb) at 1.
  arewrite_id  ⦗R ∩₁ Acq⦘ at 1.
  arewrite_id  ⦗W_ex⦘ at 1.
generalize (@sb_trans G); ins; relsf.
Qed.

Lemma W_sb_same_loc_detour WF (SC_PER_LOC: sc_per_loc G) :
⦗fun x => ~ is_init x⦘ ⨾ ⦗W⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘ ⨾ detour ⊆ detour.
Proof using.
sin_rewrite (w_sb_loc_w_in_coi WF SC_PER_LOC).
unfold Execution.detour. 
unfolder; ins; desf.
splits.
- exists z0; splits; eauto.
apply coi_coe; eauto.
basic_solver.
- ie_unfolder; unfolder in*; desf.
eapply (@sb_trans G); eauto.
Qed.

Lemma ct_ar_int_alt3 WF (SC_PER_LOC: sc_per_loc G) : 
(sb ⨾ ⦗W∩₁Rel⦘ ∪ ⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘ ∪
  detour ⨾ (⦗R∩₁Acq⦘ ⨾ sb)^? ∪ 
  ppo  ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb^?)⁺ ⊆ 
⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘ ∪ 
(sb ⨾ ⦗W∩₁Rel⦘ ∪
  detour ⨾ (⦗R∩₁Acq⦘ ⨾ sb)^? ∪ 
  ppo  ∪ 
(⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘)^? ⨾ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘
∪ 
(⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘)^? ⨾ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb^?)⁺ ⨾
(⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘)^?.
Proof using.

arewrite (sb ⨾ ⦗W∩₁Rel⦘ ∪ ⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘ ∪
  detour ⨾ (⦗R∩₁Acq⦘ ⨾ sb)^? ∪ 
  ppo  ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb^? ⊆
⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘ ∪ (sb ⨾ ⦗W∩₁Rel⦘ ∪
  detour ⨾ (⦗R∩₁Acq⦘ ⨾ sb)^? ∪ 
  ppo  ∪ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb^?)) at 1.
basic_solver 12.

assert (transitive (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘)).
{ apply transitiveI.
arewrite_id ⦗W⦘ at 1.
arewrite_id ⦗W ∩₁ Rel⦘ at 2.
generalize (@sb_same_loc_trans G).
ins; relsf. }
rewrite path_union. relsf; unionL.

- basic_solver 12.
- unionR right. hahn_frame_r. 
 apply inclusion_t_t; unionL.
all: case_refl (⦗W ∩₁ Rel⦘ ⨾ sb ∩ same_loc ⨾ ⦗W⦘); [basic_solver 20|].
* arewrite (sb ∩ same_loc ⊆ sb) at 1.
arewrite_id ⦗W⦘ at 1.
generalize (@sb_trans G); ins; relsf.
basic_solver 12.
* rewrite !seqA.
arewrite (⦗W ∩₁ Rel⦘ ⊆ ⦗fun x => ~ is_init x⦘ ⨾ ⦗W⦘).
{ unfolder; ins; desf; splits; eauto.
intro K; apply (init_pln WF) in K; mode_solver. }
sin_rewrite (W_sb_same_loc_detour WF SC_PER_LOC).
basic_solver 12.
  * rewrite (dom_l (@wf_ppoD G)) at 1; type_solver.
* basic_solver 20.
* basic_solver 20.
Qed.

Lemma ct_ar_int_alt4 WF: 
(sb ⨾ ⦗W∩₁Rel⦘ ∪
  detour ⨾ (⦗R∩₁Acq⦘ ⨾ sb)^? ∪ 
  ppo  ∪ (⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘)^? ⨾ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘
∪ 
(⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘)^? ⨾ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb^?)⁺
 

⊆ 
sb ⨾ ⦗W∩₁Rel⦘ ∪
( (sb ⨾ ⦗W∩₁Rel⦘)^? ⨾ detour ⨾ (⦗R∩₁Acq⦘ ⨾ sb)^? ∪ 
  ppo  ∪ (sb ⨾ ⦗W∩₁Rel⦘)^? ⨾ (⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc)⨾ ⦗W⦘)^? ⨾ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘
∪ (sb ⨾ ⦗W∩₁Rel⦘)^? ⨾ (⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘)^? ⨾ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb^?)⁺.
Proof using.
rewrite !unionA.
assert (transitive (sb ⨾ ⦗W ∩₁ Rel⦘)).
{ apply transitiveI.
arewrite_id ⦗W ∩₁ Rel⦘ at 1.
generalize (@sb_trans G).
ins; relsf. }
rewrite path_union. relsf; unionL.

- basic_solver 12.
- rewrite crE at 5; relsf; unionL; cycle 1.
* arewrite (sb ∩ same_loc ⊆ sb) at 1.
rewrite detour_in_sb, (ppo_in_sb WF) at 1.

arewrite_id ⦗W⦘ at 1.
arewrite_id ⦗W⦘ at 1.
arewrite_id ⦗R ∩₁ Acq⦘ at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id  ⦗W_ex_acq⦘ at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
arewrite_id ⦗W⦘ at 1.
arewrite_id ⦗W_ex⦘ at 1.
arewrite_id ⦗R ∩₁ Acq⦘ at 1.
  arewrite (rfi ⊆ sb) at 1.
arewrite (sb ∩ same_loc ⊆ sb) at 1.
arewrite_id  ⦗W ∩₁ Rel⦘ at 1.
generalize (@sb_trans G); ins; relsf.

* unionR right. 
 apply inclusion_t_t; unionL.
+ basic_solver 12.
+ rewrite crE at 1; relsf; unionL; [basic_solver 12|].
rewrite (dom_l (@wf_ppoD G)) at 1; type_solver.
+ basic_solver 21.
+ basic_solver 30.
Qed.

Lemma ct_ar_int_alt5 WF: 
 ((sb ⨾ ⦗W∩₁Rel⦘)^? ⨾ detour ⨾ (⦗R∩₁Acq⦘ ⨾ sb)^? ∪ 
  ppo  ∪ (sb ⨾ ⦗W∩₁Rel⦘)^? ⨾ (⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc)⨾ ⦗W⦘)^? ⨾ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘
∪ (sb ⨾ ⦗W∩₁Rel⦘)^? ⨾ (⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘)^? ⨾ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb^?)⁺
 ⊆ 
ppo ∪
 (ppo^? ⨾ (sb ⨾ ⦗W∩₁Rel⦘)^? ⨾ detour ⨾ (⦗R∩₁Acq⦘ ⨾ sb)^? ∪ 
  ppo^? ⨾ (sb ⨾ ⦗W∩₁Rel⦘)^? ⨾ (⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘)^? ⨾ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪
ppo^? ⨾ (sb ⨾ ⦗W∩₁Rel⦘)^? ⨾ (⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘)^? ⨾ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb^?
)⁺
⨾ ppo^?.
Proof using.

arewrite ((sb ⨾ ⦗W ∩₁ Rel⦘)^? ⨾ detour ⨾ (⦗R ∩₁ Acq⦘ ⨾ sb)^? ∪ ppo
  ⊆
ppo
 ∪ ((sb ⨾ ⦗W ∩₁ Rel⦘)^? ⨾ detour ⨾ (⦗R ∩₁ Acq⦘ ⨾ sb)^?)) at 1.

rewrite !unionA.
assert (transitive ppo).
{ apply transitiveI.
rewrite (dom_r (@wf_ppoD G)) at 1; rewrite (dom_l (@wf_ppoD G)) at 2; type_solver. }

rewrite path_union. relsf; unionL.
Qed.


Lemma ct_ar_int_alt WF 
(SC_PER_LOC: sc_per_loc G) : 

(ar_int)⁺ ⊆ 

sb^? ⨾ ⦗F∩₁Acq/Rel⦘ ⨾ sb ∪
⦗R∩₁Acq⦘ ⨾ sb ∪
sb ⨾ ⦗F∩₁Acq/Rel⦘ ⨾ sb^? ∪
⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘ ∪ 
sb ⨾ ⦗W∩₁Rel⦘ ⨾ (⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘)^? ∪
ppo ⨾
(⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘)^? ∪
 (ppo^? ⨾ (sb ⨾ ⦗W∩₁Rel⦘)^? ⨾ detour ⨾ (⦗R∩₁Acq⦘ ⨾ sb)^? ∪ 
  ppo^? ⨾ (sb ⨾ ⦗W∩₁Rel⦘)^? ⨾ (⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘)^? ⨾ ⦗W_ex_acq⦘ ⨾ sb ⨾ ⦗W⦘ ∪ 
  ppo^? ⨾ (sb ⨾ ⦗W∩₁Rel⦘)^? ⨾ (⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘)^? ⨾ ⦗W_ex⦘ ⨾ rfi ⨾ ⦗R ∩₁ Acq⦘ ⨾ sb^?
)⁺ ⨾ ppo^? ⨾
(⦗W∩₁Rel⦘ ⨾ (sb ∩ same_loc) ⨾ ⦗W⦘)^?.


Proof using.
rewrite (ct_ar_int_alt1 WF).
unionL; [basic_solver 12| basic_solver 12|].
rewrite (ct_ar_int_alt2 WF).
unionL; [basic_solver 12|].
rewrite (ct_ar_int_alt3 WF SC_PER_LOC).
unionL; [basic_solver 12|].
rewrite (ct_ar_int_alt4 WF).
rewrite (ct_ar_int_alt5 WF).



basic_solver 21.
Qed.


End IMM.
