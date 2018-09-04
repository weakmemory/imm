From hahn Require Import Hahn.
From promising Require Import Event Language Cell Memory Configuration Thread Basic.
Require Import Prog ProgToExecution.
Require Import Events Execution Event_ph_promise.

Set Implicit Arguments.
Remove Hints plus_n_O.

Definition lts_step (tid : thread_id) (pe : Event.ProgramEvent.t) (s1 s2 : state) : Prop :=
  exists (labels : list label),
    ⟪ISTEP: istep tid labels s1 s2⟫ /\
    ⟪LABS : lab_ph_promise labels pe⟫.

Lemma istep_nil_eq_silent thread :
  istep thread nil ≡
  lts_step thread ProgramEvent.silent.
Proof.
  unfold lts_step. unfold lab_ph_promise.
  split.
  { intros x y H. exists nil. by split. }
  intros x y H. desf.
Qed.

Definition thread_lts (tid : thread_id) : Language.t :=
  @Language.mk
    (list Instr.t) state
    init
    is_terminal
    (lts_step tid).

Definition init_threads (prog : Prog.t) : Threads.syntax :=
  IdentMap.mapi (fun tid (linstr : list Instr.t) => existT _ (thread_lts tid) linstr) prog.

Definition conf_step (PC PC' : Configuration.t) :=
  exists pe tid, Configuration.step pe tid PC PC'.

Definition final_memory_state (memory : Memory.t) (loc : location) : option value :=
  match Memory.get loc (Memory.max_ts loc memory) memory with
  | Some (_, msg) => Some msg.(Message.val)
  | None => None
  end.

Definition conf_init (prog : Prog.t) := Configuration.init (init_threads prog).

Definition promise_allows (prog : Prog.t) (final_memory : location -> value) :=
  exists PC,
    ⟪STEPS   : conf_step＊ (conf_init prog) PC⟫ /\
    ⟪FINAL   : Configuration.is_terminal PC⟫ /\
    ⟪OUTCOME : forall loc, final_memory_state PC.(Configuration.memory) loc =
                           Some (final_memory loc)⟫.