(******************************************************************************)
(** * OCaml MM is weaker than IMM_S   *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxRel.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_common.
Require Import imm_s_hb.
Require Import imm_s.
Require Import OCaml.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section OCamlMM_TO_IMM_S.

Variable G : execution.

Notation "'E'" := G.(acts_set).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'rmw_dep'" := G.(rmw_dep).

Notation "'fr'" := G.(fr).
Notation "'eco'" := G.(eco).
Notation "'coe'" := G.(coe).
Notation "'coi'" := G.(coi).
Notation "'deps'" := G.(deps).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).

Notation "'detour'" := G.(detour).

Notation "'rs'" := G.(rs).
Notation "'release'" := G.(release).
Notation "'sw'" := G.(sw).
Notation "'hb'" := G.(hb).

Notation "'ar_int'" := G.(ar_int).
Notation "'ppo'" := G.(ppo).
Notation "'bob'" := G.(bob).

Notation "'ar'" := G.(ar).

Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'Init'" := (fun a => is_true (is_init a)).

Hypothesis LSM : forall l,
    << LM : Loc_ l \₁ Init  ⊆₁ Rlx >> \/
    << LM : Loc_ l \₁ Init  ⊆₁ Sc >>.
Hypothesis WSCRMW : W∩₁Sc ⊆₁ codom_rel (<|R∩₁Sc|> ;; rmw).
Hypothesis WRLXF : W∩₁Rlx ⊆₁ codom_rel (<|F∩₁Acq/Rel|> ;; immediate sb).
Hypothesis RSCF : R∩₁Sc ⊆₁ codom_rel (<|F∩₁Acq|> ;; immediate sb).

Lemma co_sc_in_hb (WF : Wf G) : <|Sc|> ;; co ;; <|Sc|> ⊆ hb.
Proof.
Admitted.

Lemma s_imm_consistentimplies_ocaml_consistent (WF: Wf G) sc
      (IPC : imm_s.imm_psc_consistent G sc) :
  ocaml_consistent G.
Proof.
  cdes IPC. cdes IC.
  red. splits; auto.

  rewrite co_in_eco.
  2: rewrite fr_in_eco. 
  1,2: by arewrite (eco ⊆ eco^?); apply Cint.

Admitted.

End OCamlMM_TO_IMM_S.
