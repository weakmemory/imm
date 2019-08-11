(******************************************************************************)
(** * Definition of correspondence between IMM labels and Promise's transition labels*)
(******************************************************************************)

Require Import List Events.
From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising Require Import Event.

Set Implicit Arguments.
 
Definition rmod (mod : mode) : Ordering.t :=
  match mod with
  | Opln => Ordering.plain
  | Orel
  | Orlx => Ordering.relaxed
  | Oacq
  | Oacqrel
  | Osc => Ordering.acqrel
  end.

Definition wmod (mod : mode) : Ordering.t :=
  match mod with
  | Opln => Ordering.plain
  | Oacq
  | Orlx => Ordering.relaxed
  | Orel
  | Oacqrel
  | Osc => Ordering.acqrel
  end.

Definition fmod (mod : mode) (ordr ordw : Ordering.t) :=
  match mod with
  | Opln | Orlx => ordr = Ordering.relaxed /\ ordw = Ordering.relaxed 
  | Oacq => ordr = Ordering.acqrel /\ ordw = Ordering.relaxed
  | Orel => ordr = Ordering.relaxed /\ ordw = Ordering.acqrel
  | Oacqrel => ordr = Ordering.acqrel /\ ordw = Ordering.acqrel
  | Osc => ordr = Ordering.seqcst /\ ordw = Ordering.seqcst
  end.
  

Definition lab_imm_promise (lbls : list label) (ev : ProgramEvent.t) :=
  match lbls, ev with
  | nil, ProgramEvent.silent => True
  | Aload _ o l v :: nil, ProgramEvent.read l' v' o' =>
    ⟪ SAME_LOC : l = l' ⟫ /\
    ⟪ SAME_VAL : v = v' ⟫ /\
    ⟪ SAME_MOD : o' = rmod o ⟫
  | Astore x o l v :: nil, ProgramEvent.write l' v' o' =>
    ⟪ SAME_LOC : l = l' ⟫ /\
    ⟪ SAME_VAL : v = v' ⟫ /\
    ⟪ SAME_MOD : o' = wmod o ⟫

  | Astore x o l v :: Aload _ o' l' v' :: nil,
    ProgramEvent.update l'' valr valw ordr ordw =>
    ⟪ SAME_LOC : l = l' /\ l' = l'' ⟫ /\
    ⟪ SAME_VAL : v = valw /\ v' = valr ⟫ /\
    ⟪ SAME_MOD : ordw = wmod o /\
                  ordr = rmod o' ⟫

  | Afence o :: nil, ProgramEvent.fence ordr ordw =>
    ⟪ SAME_MOD : fmod o ordr ordw ⟫
  | _, _ => False
  end.

Definition same_g_events (lab : actid -> label) (l : list actid) := lab_imm_promise (map lab l).
