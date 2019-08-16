From hahn Require Import Hahn.
Require Import PromisingLib.
From Promising Require Import Event.
Require Import Prog.
Require Import ProgToExecution.
Require Import Events.
Require Import Event_imm_promise.

Set Implicit Arguments.
Remove Hints plus_n_O.

Definition lts_step (tid : thread_id) (pe : ProgramEvent.t) (s1 s2 : state) : Prop :=
  exists (labels : list label),
    ⟪ISTEP: istep tid labels s1 s2⟫ /\
    ⟪LABS : lab_imm_promise labels pe⟫.

Definition thread_lts (tid : thread_id) : Language.t ProgramEvent.t :=
  @Language.mk ProgramEvent.t
    (list Instr.t) state
    init
    is_terminal
    (lts_step tid).
