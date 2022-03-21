Require Import Classical Peano_dec Setoid PeanoNat.
From hahn Require Import Hahn.
Require Import Lia.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_bob.
Require Import imm_s.
Require Import imm_s_ppo.
Require Import imm_s_rfppo.
Require Import AuxDef.
Require Import SetSize.
Require Import FairExecution.
Require Import ImmFair.
Require Import AuxRel2.
Require Import TraversalOrder.

Import ListNotations.

Set Implicit Arguments.

Section TravOrderConfig.
  Context (G : execution) (sc : relation actid).
  Implicit Types (WF : Wf G) (COMP : complete G)
           (WFSC : wf_sc G sc) (CONS : imm_consistent G sc)
           (MF : mem_fair G).

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

Notation "'Rel'" := (is_rel lab).
  
Definition iord_coherent (tc : trav_label -> Prop) :=
  dom_rel (iord G sc ;; <|tc|>) ⊆₁ tc.
  
Definition iiord_step (tl : trav_label) : relation (trav_label -> Prop) :=
  restr_rel iord_coherent
            (<|fun tc => set_compl tc tl|> ;;
             (fun tc tc' => tc' ≡₁ tc ∪₁ eq tl)).
  
Definition iord_step (tc tc' : trav_label -> Prop) :=
  exists tl, iiord_step tl tc tc'.

Definition tl_issued   tc := event ↑₁ (tc ∩₁ action ↓₁ (eq ta_issue)).
Definition tl_covered  tc := event ↑₁ (tc ∩₁ action ↓₁ (eq ta_cover)).
Definition tl_reserved tc := event ↑₁ (tc ∩₁ action ↓₁ (eq ta_reserve)).
  
(* TODO: move to hahn *)
Definition pair_rel {A B} (s : A -> Prop) (t : B -> Prop) : A * B -> Prop := 
  fun ab =>
    match ab with
    | (a, b) => s a /\ t b
    end.
Notation "s <*> t" := (pair_rel s t) (at level 40, left associativity).
  
Definition rmw_clos (tc : trav_label -> Prop) : trav_label -> Prop :=
  (eq ta_cover ∪₁ eq ta_issue) <*> codom_rel (<|tl_covered tc|> ;; rmw).

Definition rel_clos (tc : trav_label -> Prop) : trav_label -> Prop :=
  (eq ta_cover) <*> (Rel ∩₁ tl_issued tc).
  
Definition sim_clos (tc : trav_label -> Prop) : trav_label -> Prop :=
  tc ∪₁ rmw_clos tc ∪₁ rel_clos tc.
  
Definition sim_coherent (tc : trav_label -> Prop) :=
  tc ≡₁ sim_clos tc.

Definition isim_clos_step (tll : list trav_label)
  : relation (trav_label -> Prop) :=
  match tll with 
  | [tl] => iiord_step tl
  | [(ta_issue, e); (ta_cover, e')] =>
      (fun _ _ => e = e' /\ Rel e) ∩
      (iiord_step (ta_issue, e) ;; 
       iiord_step (ta_cover, e'))
  | [(ta_cover, e); (ta_cover, e')] =>
      (fun _ _ => rmw e e') ∩
      (iiord_step (ta_cover, e) ;; 
       iiord_step (ta_cover, e'))
  | [(ta_cover, e); (ta_issue, e'); (ta_cover, e'')] =>
      (fun _ _ => rmw e e' /\ e' = e'' /\ Rel e') ∩
      (iiord_step (ta_cover, e) ;; 
       iiord_step (ta_issue, e') ;;
       iiord_step (ta_cover, e''))
  | _ => fun _ _ => False
  end.
  
Definition sim_clos_step :=
  restr_rel sim_coherent 
            (fun tc tc' => exists tll, isim_clos_step tll tc tc').
  
Lemma iord_step_implies_sim_clos_step :
  iord_step ⊆ sim_clos ↓ sim_clos_step^*.
Proof using.
  unfolder; intros x y STEP.
  red in STEP. desf.

  (* use trav_step_closures_isim from SimTravClosure.v  *)
Admitted.

End TravOrderConfig.
