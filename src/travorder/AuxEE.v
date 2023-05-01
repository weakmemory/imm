(* TODO: split this file... *)
Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob.
Require Import imm_s.
Require Import imm_s_ppo.
Require Import imm_s_rfppo.
Require Import AuxDef.
Require Import AuxRel2.
(* Require Import travorder.TraversalOrder. *)
Require Import CombRelations.

Set Implicit Arguments.

Section E_E.
  Variables (G: execution) (sc: relation actid). 
  Hypotheses (WF: Wf G)
             (WFSC: wf_sc G sc)
             (SCPL: sc_per_loc G).
  Notation "'E'" := (acts_set G).
  Notation "'sb'" := (sb G).
  Notation "'rmw'" := (rmw G).
  Notation "'data'" := (data G).
  Notation "'addr'" := (addr G).
  Notation "'ctrl'" := (ctrl G).
  Notation "'rf'" := (rf G).
  Notation "'co'" := (co G).
  Notation "'coe'" := (coe G).
  Notation "'fr'" := (fr G).

  Notation "'fwbob'" := (fwbob G).
  Notation "'ppo'" := (ppo G).
  Notation "'ar'" := (ar G sc).
  Notation "'fre'" := (fre G).
  Notation "'rfi'" := (rfi G).
  Notation "'rfe'" := (rfe G).
  Notation "'deps'" := (deps G).
  Notation "'detour'" := (detour G).

  Notation "'lab'" := (lab G).
  Notation "'loc'" := (loc lab).
  Notation "'val'" := (val lab).
  Notation "'mod'" := (Events.mod lab).
  Notation "'same_loc'" := (same_loc lab).
  
  Notation "'E'" := (acts_set G).
  Notation "'R'" := (fun x => is_true (is_r lab x)).
  Notation "'W'" := (fun x => is_true (is_w lab x)).
  Notation "'F'" := (fun x => is_true (is_f lab x)).
  Notation "'Sc'" := (fun x => is_true (is_sc lab x)).
  Notation "'RW'" := (R ∪₁ W).
  Notation "'FR'" := (F ∪₁ R).
  Notation "'FW'" := (F ∪₁ W).
  Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
  Notation "'W_ex'" := (W_ex G).
  Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).
  Notation "'Rel'" := (fun x => is_true (is_rel lab x)).

  Let E_E := E × E.

  Lemma co_E_E : co ⊆ E_E.
  Proof using WF. rewrite wf_coE; basic_solver. Qed.

  Lemma fr_E_E : fr ⊆ E_E.
  Proof using WF. rewrite wf_frE; basic_solver. Qed.

  Lemma furr_E_E_cr: furr G sc ⊆ E_E^?.
  Proof using WF WFSC.
    rewrite wf_furrE; eauto.
    rewrite crE. apply union_mori; basic_solver 10.
  Qed.

  Lemma E_E_trans: transitive E_E.
  Proof using. unfold E_E. basic_solver. Qed.

  Let E_ENI := E × (E \₁ is_init).

  Lemma sb_E_ENI: sb ⊆ E_ENI. 
  Proof using. rewrite wf_sbE, no_sb_to_init. basic_solver. Qed. 

  Lemma co_E_ENI: co ⊆ E_ENI. 
  Proof using WF SCPL. rewrite wf_coE, no_co_to_init; auto. basic_solver. Qed.

  Lemma rf_E_ENI : rf ⊆ E_ENI. 
  Proof using WF. rewrite wf_rfE, no_rf_to_init; auto. basic_solver. Qed. 

  Lemma fr_E_ENI: fr ⊆ E_ENI. 
  Proof using WF SCPL. rewrite wf_frE, no_fr_to_init; auto. basic_solver. Qed.

  (* TODO: replace the original lemma with it*)
  Lemma no_ar_to_init': ar ⨾ ⦗is_init⦘ ≡ ∅₂.
  Proof using WF WFSC.
    split; [|basic_solver].
    unfold ar.
    rewrite (ar_int_in_sb WF). rewrite no_sb_to_init.
    rewrite wf_scD with (sc:=sc); eauto.  
    rewrite (wf_rfeD WF).
    rewrite seq_union_l. unionL; [|basic_solver].
    rewrite (init_w WF). type_solver 10.
  Qed.

  Lemma no_ar_to_init_alt:
    ar ≡ ar ⨾ ⦗set_compl is_init⦘. 
  Proof using WF WFSC.
    forward eapply no_ar_to_init'; eauto. basic_solver 10.
    Unshelve. all: eauto.
  Qed. 

  Lemma ar_E_ENI: ar ⊆ E_ENI. 
  Proof using WF WFSC.
    rewrite wf_arE, no_ar_to_init_alt; auto. basic_solver.
  Qed.

  Lemma sc_E_ENI: sc ⊆ E_ENI. 
  Proof using WF WFSC.
    rewrite wf_scE, (@no_sc_to_init _ WF _ WFSC); eauto. basic_solver.
  Qed.

  Lemma furr_E_ENI_cr: furr G sc ⊆ E_ENI^?.
  Proof using WFSC WF.
    rewrite furr_to_ninit, wf_furrE; auto.
    rewrite crE. unfold E_ENI. basic_solver.
  Qed.  

  Lemma E_ENI_trans: transitive E_ENI.
  Proof using. unfold E_ENI. basic_solver. Qed.

  Lemma ar_rf_ppo_loc_ct_E_ENI: 
    (ar ∪ rf ⨾ ppo ∩ same_loc)⁺ ⊆ E_ENI.
  Proof using WF WFSC. 
    rewrite inclusion_inter_l1, ppo_in_sb; auto. 
    rewrite sb_E_ENI, rf_E_ENI, ar_E_ENI; auto.
    repeat (rewrite ?(@rt_of_trans _ E_ENI), ?(@rewrite_trans _ E_ENI),
             ?unionK, ?(@rewrite_trans _ E_ENI),
             ?(@rewrite_trans_seq_cr_cr _ E_ENI), ?(@ct_of_trans _ E_ENI)
           ); try by (subst; apply E_ENI_trans).
    basic_solver. 
  Qed.
End E_E. 
