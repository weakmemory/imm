(******************************************************************************)
(** * Definition of the OCaml memory model [Dolan-al:PLDI18] *)
(******************************************************************************)
From hahn Require Import Hahn.
Require Import AuxRel.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_s_hb.
Require Import imm_s.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section OCamlMM.

Variable G : execution.

Notation "'E'" := G.(acts_set).
Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'rfe'" := G.(rfe).
Notation "'co'" := G.(co).
Notation "'coe'" := G.(coe).
Notation "'rmw'" := G.(rmw).
Notation "'fr'" := G.(fr).
Notation "'fre'" := G.(fre).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

(******************************************************************************)
(** ** Consistency  *)
(******************************************************************************)

Definition on_sc rel := (<|Sc|>;;rel;;<|Sc|>). 

Definition hbinit e0 e := 
  match e0, e with 
  | InitEvent _, ThreadEvent _ _ => True
  | _, _ => False
  end.
Definition hb := hbinit ∪ sb ∪ (on_sc (coe ∪ rf)). (* see p. 6 *)

Definition ocaml_causal := acyclic (sb ∪ (on_sc (co ∪ fr)) ∪ rf). (* see expanded definition at p. 17 *)
Definition ocaml_coherent := irreflexive (hb ;; (co ∪ fr)). (* see p. 6 *)

Definition ocaml_consistent :=
  ⟪ Comp : complete G ⟫ /\
  ⟪ Cat  : rmw_atomicity G ⟫ /\
  ocaml_coherent /\
  ocaml_causal. 

End OCamlMM.

