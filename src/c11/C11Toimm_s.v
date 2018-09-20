(******************************************************************************)
(** * C11 is weaker than IMM_S   *)
(******************************************************************************)

Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import AuxRel.

Require Import Events Execution Execution_eco.
Require Import imm_common imm_s_hb imm_s C11.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section C11_TO_IMM_S.

Variable G : execution.

Notation "'E'" := G.(acts_set).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).

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
Notation "'psc'" := G.(psc).

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
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

(******************************************************************************)
(** relations are contained in the corresponding ones **  *)
(******************************************************************************)

Lemma s_imm_consistentimplies_c11_consistent (WF: Wf G) sc : 
  imm_s.imm_consistent G sc -> c11_consistent G.
Proof.
  unfold imm_s.imm_consistent, c11_consistent; ins; desf; splits; ins.
  destruct Wf_sc.
  arewrite (psc ⊆ sc); [|by red; relsf]. 
  unfold C11.psc.
  rewrite wf_hbE, ?seqA; ins. 
  seq_rewrite <- !id_inter. 
  rewrite !inclusion_seq_eqv_l with (dom := E).
  unfolder; ins; desf.
  destruct (classic (x = y)) as [|NEQ]; desf.
    by destruct Cint with z0; unfolder;
      unfold imm_s_hb.hb in *; eauto using t_trans.
  eapply wf_sc_total in NEQ; desf; vauto.
  edestruct Csc; unfolder; eauto 10. 
Qed.

End C11_TO_IMM_S.