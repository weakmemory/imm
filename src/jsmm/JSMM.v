(******************************************************************************)
(** * Definition of the JSMM memory model *)
(******************************************************************************)
From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.

Set Implicit Arguments.

Section JSMM.

Variable G : execution.

Notation "'E'" := (acts_set G).
Notation "'acts'" := (acts G).
Notation "'lab'" := (lab G).
Notation "'sb'" := (sb G).
Notation "'rf'" := (rf G).
Notation "'co'" := (co G).
Notation "'rmw'" := (rmw G).
Notation "'fr'" := (fr G).
Notation "'eco'" := (eco G).
Notation "'same_loc'" := (same_loc lab).

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

Definition sw := ⦗ Sc ⦘ ⨾ rf ⨾ ⦗ Sc ⦘.
Definition hb := (sb ∪ sw)⁺.

(******************************************************************************)
(** ** Consistency  *)
(******************************************************************************)

Definition jsmm_consistent tot :=
  ⟪ Ctot   : strict_total_order E tot ⟫ /\
  ⟪ Chbtot : hb ⊆ tot ⟫ /\
  ⟪ Chbrf : irreflexive (hb ⨾ rf) ⟫ /\
  ⟪ Chbrfhb :
      irreflexive (hb ⨾ rf⁻¹ ⨾ (hb ∩ same_loc) ⨾ ⦗ W ⦘) ⟫ /\
  ⟪ Cirr1 :
      irreflexive (⦗W∩₁Sc⦘ ⨾ tot ⨾ ⦗R∩₁Sc⦘ ⨾
                   rf⁻¹ ⨾ ⦗W∩₁Sc⦘ ⨾ (tot ∩ same_loc)) ⟫ /\
  ⟪ Cirr2 :
      irreflexive (⦗W∩₁Sc⦘ ⨾ hb ⨾
                   (hb ∩ rf)⁻¹ ⨾ ⦗W∩₁Sc⦘ ⨾ (tot ∩ same_loc)) ⟫ /\
  ⟪ Cirr3 :
      irreflexive (⦗W∩₁Sc⦘ ⨾ tot ⨾ ⦗R∩₁Sc⦘ ⨾
                   (hb ∩ rf)⁻¹ ⨾ (hb ∩ same_loc)) ⟫.

End JSMM.
