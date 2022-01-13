Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import Lia.

Require Import Events.
Require Import Execution.
Require Import imm_bob.
Require Import imm_s.
Require Import imm_s_ppo.
Require Import imm_s_rfppo.
Require Import TraversalConfig.
Require Import Traversal.
Require Import TraversalConfigAlt.
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

  Context (G : execution) (sc : relation actid).
  Implicit Types (WF : Wf G) (COMP : complete G)
           (WFSC : wf_sc G sc) (CONS : imm_consistent G sc).

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
  
  (* Essentially, it is an alternative representation of a part of tc_coherent *)
  Definition iord (l1 l2 : t) : Prop :=
    match l1, l2 with
    | mkTL a1 e1, mkTL a2 e2 =>
        << EE1 : (E \₁ is_init) e1 >> /\
        << EE2 : (E \₁ is_init) e2 >> /\
        match a1, a2 with
        | TravAction.cover, TravAction.cover =>
            << SBSC : (sb ∪ sc) e1 e2 >>
        | TravAction.issue, TravAction.cover =>
            << RFQ : rf^? e1 e2 >>
        | TravAction.cover, TravAction.issue =>
            << FWBOB : fwbob e1 e2 >>
        | TravAction.issue, TravAction.issue =>
            << ARRFPPO : (⦗W⦘ ⨾ (ar ∪ rf ⨾ ppo ∩ same_loc)⁺) e1 e2 >>
        end
    end. 
  
  Lemma iord_irreflexive WF COMP WFSC CONS : irreflexive iord.
  Proof using.
    unfold iord. red. ins. desf; desf.
    { destruct SBSC as [AA|AA].
      { eapply sb_irr; eauto. }
      eapply (sc_irr WFSC); eauto. }
    apply seq_eqv_l in ARRFPPO. destruct ARRFPPO as [_ AA].
    eapply ar_rf_ppo_loc_acyclic; eauto.
  Qed.
  
  Lemma iord_acyclic : acyclic iord.
  Proof using.
    red. (* TODO: probably reuse parts of exists_trav_step *)
  Admitted.

  Lemma iord_ct_fsupp
        (NOSC  : E ∩₁ F ∩₁ Sc ⊆₁ ∅)
        (FSUPP : fsupp (ar ∪ rf ⨾ ppo ∩ same_loc)⁺) :
    fsupp iord⁺.
  Proof using.
  Admitted.
  
  (* NEXT TODO: Combination of iord_ct_fsupp and iord_acyclic should
                allow to get lineralization of traversal actions.
   *)
End TravLabel.
