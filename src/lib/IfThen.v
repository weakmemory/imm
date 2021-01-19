From hahn Require Import Hahn.
Require Import Setoid.

Set Implicit Arguments.

(******************************************************************************)
(** ** ifthenelse  *)
(******************************************************************************)

Definition ifthenelse T K L (c : {K} + {L}) (x y : T) :=
  if c then x else y.

Definition ifthenelse_b T (c : bool) (x y : T) :=
  if c then x else y.

Add Parametric Morphism {A} (K : Prop) (L : Prop) (c : {K} + {L}) :
  (@ifthenelse (A -> Prop) K L c) with signature
    set_equiv ==>
    set_equiv ==>
    set_equiv as ifthenelse_more.
Proof using. intros; unfold ifthenelse; desf. Qed.

Add Parametric Morphism {A} (c : bool) :
  (@ifthenelse_b (A -> Prop) c) with signature
    set_equiv ==>
    set_equiv ==>
    set_equiv as ifthenelse_b_more.
Proof using. intros; unfold ifthenelse_b; desf. Qed.

Lemma ite_alt {A} K L (c : {K} + {L}) (x y : A -> Prop) :
  (if c then x else y) ≡₁ ifthenelse c x y.
Proof using. rels. Qed.

Lemma iteb_alt {A} (c : bool) (x y : A -> Prop) :
  (if c then x else y) ≡₁ ifthenelse_b c x y.
Proof using. rels. Qed.

Lemma ite_union_t {A} K L (c : {K} + {L}) (x y z : A -> Prop) :
  ifthenelse c (x ∪₁ y) z ≡₁ ifthenelse c x z ∪₁ ifthenelse c y z.
Proof using. by rewrite <- !ite_alt; destruct c; [|rewrite set_unionK]. Qed.
