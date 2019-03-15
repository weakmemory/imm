(******************************************************************************)
(** * Definition of the C11 memory model *)
(******************************************************************************)
From hahn Require Import Hahn.
Require Import AuxRel.
Require Import Events Execution Execution_eco imm_s_hb imm_s.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section C11.

Variable G : execution.

Notation "'E'" := G.(acts_set).
Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'fr'" := G.(fr).
Notation "'eco'" := G.(eco).
Notation "'hb'" := G.(hb).

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

(* This definition of consistency differs to one from [Batty et al. POPL11]:
   it is (strictly) stronger since it follows a fix from [Lahav et al. PLDI17].
 *)
Definition c11_consistent :=
  ⟪ Comp : complete G ⟫ /\
  ⟪ Coh : coherence G ⟫ /\
  ⟪ Cat  : rmw_atomicity G ⟫ /\
  ⟪ Csc : acyclic (psc_f G ∪ psc_base G) ⟫.

End C11.