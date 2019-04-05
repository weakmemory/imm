From hahn Require Import Hahn.

Set Implicit Arguments.
Remove Hints plus_n_O.

Lemma step_dom A (r: relation A) d e 
  (E: r ⊆ (⦗d⦘ ∪ ⦗e⦘) ⨾ r ⨾ (⦗d⦘ ∪ ⦗e⦘))
  dd (DD: dd = ⦗d⦘ ⨾ r ⨾ ⦗d⦘)
  de (DE: de = ⦗d⦘ ⨾ r ⨾ ⦗e⦘)
  ed (ED: ed = ⦗e⦘ ⨾ r ⨾ ⦗d⦘)
  ee (EE: ee = ⦗e⦘ ⨾ r ⨾ ⦗e⦘) :
  r ⊆ dd ∪ de ∪ ed ∪ ee.
Proof.
rewrite E; subst; basic_solver 8.
Qed.

Lemma path_dom A (r: relation A) d e 
  (E1: r ⊆ (⦗d⦘ ∪ ⦗e⦘) ⨾ r ⨾ (⦗d⦘ ∪ ⦗e⦘))
  (E2: ⦗d⦘ ⨾ ⦗e⦘ ⊆ ∅₂)
  dd (DD: dd = ⦗d⦘ ⨾ r ⨾ ⦗d⦘)
  de (DE: de = ⦗d⦘ ⨾ r ⨾ ⦗e⦘)
  ed (ED: ed = ⦗e⦘ ⨾ r ⨾ ⦗d⦘)
  ee (EE: ee = ⦗e⦘ ⨾ r ⨾ ⦗e⦘) : 
   r⁺ ⊆ (dd⁺ ∪ (dd^* ⨾ de ⨾ ee^* ⨾ ed)⁺ ⨾ dd^* ) ∪
  (ee⁺ ∪ (ee^* ⨾ ed ⨾ dd^* ⨾ de)⁺ ⨾ ee^* ) ∪
  (ee^* ⨾ ed ⨾ dd^* ⨾ de)^* ⨾ ee^* ⨾ ed ⨾ dd^* ∪
  (dd^* ⨾ de ⨾ ee^* ⨾ ed)^* ⨾ dd^* ⨾ de ⨾ ee^*.
Proof. 
  apply inclusion_t_ind_right.
- rewrite step_dom with (r:=r) (d:=d) (e:=e) at 1; try eassumption.
repeat apply inclusion_union_l; rewrite ?seqA.
1,4: sin_rewrite !ct_end.
all: try (repeat (apply inclusion_union_r; constructor); basic_solver 14).
- rewrite step_dom with (r:=r) (d:=d) (e:=e) at 1; try eassumption.
relsf.
assert (E2': ⦗e⦘ ⨾ ⦗d⦘ ⊆ (fun _ _ : A => False)).
  by rewrite seq_eqvC in E2.

assert (X17: ed ⨾ ed ⊆ ∅₂).
  by rewrite ?DD, ?ED, ?DE, ?EE; generalize E2; basic_solver.
assert (X18: ed ⨾ ee ⊆ ∅₂).
  by rewrite ?DD, ?ED, ?DE, ?EE; generalize E2; basic_solver.
assert (X19: de ⨾ dd ⊆ ∅₂).
  by rewrite ?DD, ?ED, ?DE, ?EE; generalize E2; basic_solver.
assert (X20: de ⨾ de ⊆ ∅₂).
  by rewrite ?DD, ?ED, ?DE, ?EE; generalize E2; basic_solver.
assert (X1: dd ^* ⨾ ed ⊆ ed).
  by rewrite ?rtE; relsf; rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
    try sin_rewrite E2; try sin_rewrite E2'; relsf.
assert (X2: dd ^* ⨾ dd ⊆ dd^* ).
  by rewrite rt_end at 2; relsf.
assert (X3: dd ^* ⨾ ee ⊆ ee).
  by rewrite ?rtE; relsf; rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
    try sin_rewrite E2; try sin_rewrite E2'; relsf.
assert (X4: ee ^* ⨾ de ⊆ de).
  by rewrite ?rtE; relsf; rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
    try sin_rewrite E2; try sin_rewrite E2'; relsf.
assert (X5: ee ^* ⨾ ee ⊆ ee^* ).
  by rewrite rt_end at 2; relsf.
assert (X6: ee ^* ⨾ dd ⊆ dd).
  by rewrite ?rtE; relsf; rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
    try sin_rewrite E2; try sin_rewrite E2'; relsf.
assert (X7: dd ⁺ ⨾ dd ⊆ dd⁺).
  by rewrite ct_end at 2; rewrite inclusion_t_rt.
assert (X8: dd ⁺ ⨾ ed ⊆ ∅₂).
  by rewrite ?rtE; relsf; rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
    try sin_rewrite E2; try sin_rewrite E2'; relsf.
assert (X9: dd ⁺ ⨾ ee ⊆ ∅₂).
  by rewrite ?rtE; relsf; rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
    try sin_rewrite E2; try sin_rewrite E2'; relsf.
assert (X10: (dd ^* ⨾ de ⨾ ee ^* ⨾ ed) ⁺ ⨾ ed ⊆ ∅₂).
  by rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
    try sin_rewrite E2; try sin_rewrite E2'; relsf.
assert (X11: (dd ^* ⨾ de ⨾ ee ^* ⨾ ed) ⁺ ⨾ ee ⊆ ∅₂).
   by rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA;
    try sin_rewrite E2; try sin_rewrite E2'; relsf.
assert (X12: ee ⁺ ⨾ dd ⊆ ∅₂).
  by rewrite ?rtE; relsf; rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
    try sin_rewrite E2; try sin_rewrite E2'; relsf.
assert (X13: ee ⁺ ⨾ de ⊆ ∅₂).
  by rewrite ?rtE; relsf; rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
    try sin_rewrite E2; try sin_rewrite E2'; relsf.
assert (X14: ee ⁺ ⨾ ee ⊆ ee⁺).
  by rewrite ct_end at 2; rewrite inclusion_t_rt.
assert (X15: (ee ^* ⨾ ed ⨾ dd ^* ⨾ de) ⁺ ⨾ dd ⊆ ∅₂).
  by rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
    try sin_rewrite E2; try sin_rewrite E2'; relsf.
assert (X16: (ee ^* ⨾ ed ⨾ dd ^* ⨾ de) ⁺ ⨾ de ⊆ ∅₂).
  by rewrite ct_end, ?seqA, ?DD, ?ED, ?DE, ?EE, ?seqA; 
    try sin_rewrite E2; try sin_rewrite E2'; relsf.

repeat apply inclusion_union_l; rewrite ?seqA.
all: rewrite ?X1, ?X2, ?X3, ?X4, ?X5, ?X6, ?X7, ?X8, ?X9, ?X10,
     ?X11, ?X12, ?X13, ?X14, ?X15, ?X16, ?X17, ?X18, ?X19, ?X20.
all: rels.
all: try (repeat (apply inclusion_union_r; constructor); basic_solver 5).
all: try (repeat (apply inclusion_union_r; constructor); basic_solver 20).
Qed.

Lemma path_dom_same A (r: relation A) d e 
  (E1: r ⊆ (⦗d⦘ ∪ ⦗e⦘) ⨾ r ⨾ (⦗d⦘ ∪ ⦗e⦘))
  (E2: ⦗d⦘ ⨾ ⦗e⦘ ⊆ ∅₂)
  dd (DD: dd = ⦗d⦘ ⨾ r ⨾ ⦗d⦘)
  de (DE: de = ⦗d⦘ ⨾ r ⨾ ⦗e⦘)
  ed (ED: ed = ⦗e⦘ ⨾ r ⨾ ⦗d⦘)
  ee (EE: ee = ⦗e⦘ ⨾ r ⨾ ⦗e⦘) : 
  ⦗d⦘ ⨾ r⁺ ⨾ ⦗d⦘ ⊆ dd⁺ ∪ (dd^* ⨾ de ⨾ ee^* ⨾ ed)⁺ ⨾ dd^*.
Proof.
rewrite path_dom; try edone.
relsf; repeat apply inclusion_union_l; rewrite ?seqA.
all: try by rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r; relsf.
- by rewrite ct_begin, EE, ?seqA; sin_rewrite E2; relsf.
- rewrite ct_begin at 1; rewrite EE at 1; rewrite ED at 1;
  rewrite rtE at 1; relsf.
  rewrite ?seqA. 
  repeat apply inclusion_union_l; rewrite ?seqA.
  by sin_rewrite E2; relsf.
  by rewrite ct_begin, EE, ?seqA; sin_rewrite E2; relsf.
- rewrite rtE at 1; relsf.
  rewrite rtE at 1; relsf.
  repeat apply inclusion_union_l; rewrite ?seqA.
  by rewrite ED, ?seqA; sin_rewrite E2; relsf.
  by rewrite ct_begin, EE, ?seqA; sin_rewrite E2; relsf.
  rewrite ct_begin at 1; rewrite ?seqA.
  rewrite rtE at 1; relsf.
  rewrite ED, ?seqA; sin_rewrite E2; relsf.
  by rewrite ct_begin, EE, ?seqA; sin_rewrite E2; relsf.
- rewrite ?seqA.
  arewrite (⦗d⦘ ⨾ (dd ^* ⨾ de ⨾ ee ^* ⨾ ed) ^* ⨾ dd ^* ⊆ fun _ _ => True).
  rewrite rtE at 1; relsf.
  rewrite DE, ?seqA.
  arewrite (⦗e⦘ ⨾ ⦗d⦘ ⊆ (fun _ _ : A => False)).
    by rewrite seq_eqvC in E2.
  relsf.
  rewrite ct_end at 1; rewrite ?seqA.
  rewrite EE, ?seqA.
  arewrite (⦗e⦘ ⨾ ⦗d⦘ ⊆ (fun _ _ : A => False)).
    by rewrite seq_eqvC in E2.
  by relsf.
Qed.

Lemma irr_dom A (r: relation A) d e
  (E1: r ⊆ (⦗d⦘ ∪ ⦗e⦘) ⨾ r ⨾ (⦗d⦘ ∪ ⦗e⦘))
  (E2: ⦗d⦘ ⨾ ⦗e⦘ ⊆ ∅₂)
  (IRRd: irreflexive (⦗d⦘ ⨾ r ⨾ ⦗d⦘)) 
  (IRRe: irreflexive (⦗e⦘ ⨾ r ⨾ ⦗e⦘)) :
  irreflexive r.
Proof.
  rewrite step_dom; try edone.
  repeat rewrite irreflexive_union; splits; try done; 
  generalize E2; basic_solver 8.
Qed.


Lemma acyc_dom A (r: relation A) d e
  (E1: r ⊆ (⦗d⦘ ∪ ⦗e⦘) ⨾ r ⨾ (⦗d⦘ ∪ ⦗e⦘))
  (E2: ⦗d⦘ ⨾ ⦗e⦘ ⊆ ∅₂)
  dd (DD: dd = ⦗d⦘ ⨾ r ⨾ ⦗d⦘)
  de (DE: de = ⦗d⦘ ⨾ r ⨾ ⦗e⦘)
  ed (ED: ed = ⦗e⦘ ⨾ r ⨾ ⦗d⦘)
  ee (EE: ee = ⦗e⦘ ⨾ r ⨾ ⦗e⦘) 
  (ACYCd: acyclic dd) 
  (ACYCe: acyclic ee) 
  (ACYCed: acyclic (ed ⨾ dd^* ⨾ de ⨾ ee^*)) :
  acyclic r.
Proof.
red.
eapply irr_dom; try edone.
- arewrite (⦗d⦘ ∪ ⦗e⦘ ≡ ⦗fun x => d x \/ e x⦘).
    by basic_solver.
  apply domab_helper; split.
  apply ct_doma; eapply domab_helper with (d':= fun x => d x \/ e x).
  rewrite E1 at 1; basic_solver.
  apply ct_domb; eapply domab_helper with (d := fun x => d x \/ e x).
  rewrite E1 at 1; basic_solver.
- sin_rewrite path_dom_same; try edone.
  repeat rewrite irreflexive_union; splits; try done.
  rewrite irreflexive_seqC.
  arewrite( dd^* ⨾ (dd ^* ⨾ de ⨾ ee ^* ⨾ ed) ⁺ ⊆ (dd ^* ⨾ de ⨾ ee ^* ⨾ ed) ⁺).
    by rewrite ct_begin; rewrite !seqA; rels.
  assert (acyclic (dd ^* ⨾ de ⨾ ee ^* ⨾ ed)); try done. (*?*)
  rewrite acyclic_seqC; rewrite !seqA. 
  rewrite acyclic_seqC; rewrite !seqA. 
  rewrite acyclic_seqC; rewrite !seqA. 
  done.
- rewrite unionC in E1.
  sin_rewrite path_dom_same; try edone; try by rewrite seq_eqvC.
  repeat rewrite irreflexive_union; splits; try done.
  rewrite irreflexive_seqC.
  arewrite( ee^* ⨾ (ee ^* ⨾ ed ⨾ dd ^* ⨾ de) ⁺  ⊆ (ee ^* ⨾ ed ⨾ dd ^* ⨾ de) ⁺).
    by rewrite ct_begin; rewrite !seqA; rels.
  assert (acyclic(ee ^* ⨾ ed ⨾ dd ^* ⨾ de)); try done. (*?*)
  rewrite acyclic_seqC; rewrite !seqA. 
  done.
Qed.