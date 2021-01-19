Require Import RelationClasses List Lia.
From hahn Require Import Hahn.
From PromisingLib Require Import Loc.
Require Import Events.
Require Import Execution.
Require Import Prog.
Export ListNotations.

Set Implicit Arguments.

Module RegFile.
  Definition t := RegFun.t value.

  Definition init := RegFun.init Const.zero.

  Definition eval_value (rf:t) (val:Value.t): value :=
    match val with
    | Value.reg r => RegFun.find r rf
    | Value.const c => c
    end.

  Definition eval_expr (rf:t) (rhs:Instr.expr): value :=
    match rhs with
    | Instr.expr_val val => eval_value rf val
    | Instr.expr_op1 op op1 => Op1.eval op (eval_value rf op1)
    | Instr.expr_op2 op op1 op2 => Op2.eval op (eval_value rf op1) (eval_value rf op2)
    end.

  Definition eval_lexpr (rf:t) (rhs:Instr.lexpr): Loc.t :=
    match rhs with
    | Instr.lexpr_loc loc => loc
    | Instr.lexpr_choice op loc1 loc2 =>
      if Const.eq_dec (eval_expr rf op) Const.zero
      then loc2
      else loc1
    end.

End RegFile.

Module DepsFile.
  Definition t := RegFun.t (actid -> Prop).
  Definition init : t := RegFun.init ∅.
  
  Definition val_deps (df:t) (val:Value.t): actid -> Prop :=
    match val with
    | Value.const _ => ∅
    | Value.reg   r => RegFun.find r df
    end.
  
  Definition expr_deps (df:t) (rhs:Instr.expr): actid -> Prop :=
    match rhs with
    | Instr.expr_val val => val_deps df val
    | Instr.expr_op1 op val => val_deps df val
    | Instr.expr_op2 op val1 val2 => (val_deps df val1) ∪₁ (val_deps df val2)
    end.
  
  Definition lexpr_deps (df:t) (lexpr:Instr.lexpr): actid -> Prop :=
    match lexpr with
    | Instr.lexpr_loc _ => ∅
    | Instr.lexpr_choice reg _ _ => val_deps df reg
    end.
End DepsFile.

Section State.

  Record state := {
    instrs:list Instr.t;
    pc : nat;
    G : execution;
    eindex : nat;
    regf: RegFile.t;
    depf: DepsFile.t;
    ectrl: actid -> Prop;
  }.

  Definition init_execution : execution :=
    {| acts := nil;
       lab := fun _ => Afence Orlx;
       rmw := ∅₂;
       data := ∅₂;
       addr := ∅₂;
       ctrl := ∅₂;
       rmw_dep := ∅₂;
       rf := ∅₂;
       co := ∅₂;
    |}.

  Definition init (instrs:list Instr.t) :=
    {| instrs := instrs;
       pc := 0;
       G := init_execution;
       eindex := 0;
       regf := RegFile.init;
       depf := DepsFile.init;
       ectrl := ∅;
     |}.

  Definition is_terminal s: Prop :=
    (pc s) >= (length (instrs s)).
  
  Definition add G tid index elab ddata daddr dctrl drmw_dep :=
    let e := ThreadEvent tid index in 
    {| acts := e :: (acts G);
       lab := upd (lab G) e elab;
       rmw := (rmw G);
       data := (data G) ∪ ddata × (eq e);
       addr := (addr G) ∪ daddr × (eq e);
       ctrl := (ctrl G) ∪ dctrl × (eq e);
       rmw_dep := (rmw_dep G) ∪ drmw_dep × (eq e);
       rf := ∅₂;
       co := ∅₂;
    |}.

  Definition add_rmw G tid index erlab ewlab ddata daddr dctrl drmw_dep :=
    let er:= ThreadEvent tid index in 
    let ew:= ThreadEvent tid (index + 1) in 
    let rw_edge := singl_rel er ew in
    {| acts := ew :: er :: (acts G);
       lab := upd (upd (lab G) er erlab) ew ewlab; 
       rmw := rw_edge ∪ (rmw G);
       data := (data G) ∪ ddata × (eq ew);
       addr := (addr G) ∪ daddr × (eq er ∪₁ eq ew);
       ctrl := (ctrl G) ∪ dctrl × (eq er ∪₁ eq ew);
       rmw_dep := (rmw_dep G) ∪ drmw_dep × (eq er);
       rf := ∅₂;
       co := ∅₂;
    |}.

  Inductive istep_ tid labels s1 s2 instr : Prop :=
  | assign reg expr
      (LABELS : labels = nil)
      (II : instr = Instr.assign reg expr)
      (UPC : (pc s2) = (pc s1) + 1)
      (UG : (G s2) = (G s1))
      (UINDEX : (eindex s2) = (eindex s1))
      (UREGS : (regf s2) = RegFun.add reg (RegFile.eval_expr (regf s1) expr) (regf s1))
      (UDEPS : (depf s2) = RegFun.add reg (DepsFile.expr_deps (depf s1) expr) (depf s1))
      (UECTRL : (ectrl s2) = (ectrl s1))
  | if_ expr shift
      (LABELS : labels = nil)
      (II : instr = Instr.ifgoto expr shift)
      (UPC   : if Const.eq_dec (RegFile.eval_expr (regf s1) expr) 0
               then (pc s2) = (pc s1) + 1
               else (pc s2) = shift)
      (UG    : (G s2) = (G s1))
      (UINDEX : (eindex s2) = (eindex s1))
      (UREGS : (regf s2) = (regf s1))
      (UDEPS : (depf s2) = (depf s1))
      (UECTRL : (ectrl s2) = (DepsFile.expr_deps (depf s1) expr) ∪₁ (ectrl s1))
  | load ord reg lexpr val l
      (L: l = RegFile.eval_lexpr (regf s1) lexpr)
      (II : instr = Instr.load ord reg lexpr)
      (LABELS : labels = [Aload false ord (RegFile.eval_lexpr (regf s1) lexpr) val])
      (UPC   : (pc s2) = (pc s1) + 1)
      (UG    : (G s2) =
                 add (G s1) tid (eindex s1) (Aload false ord (RegFile.eval_lexpr (regf s1) lexpr) val) ∅
                     (DepsFile.lexpr_deps (depf s1) lexpr) (ectrl s1) ∅)
      (UINDEX : (eindex s2) = (eindex s1) + 1)
      (UREGS : (regf s2) = RegFun.add reg val (regf s1))
      (UDEPS : (depf s2) = RegFun.add reg (eq (ThreadEvent tid (eindex s1))) (depf s1))
      (UECTRL : (ectrl s2) = (ectrl s1))
  | store ord lexpr expr l v x
      (L: l = RegFile.eval_lexpr (regf s1) lexpr)
      (V: v = RegFile.eval_expr  (regf s1)  expr)
      (X: x = Xpln)
      (LABELS : labels = [Astore x ord l v])
      (II : instr = Instr.store ord lexpr expr)
      (UPC   : (pc s2) = (pc s1) + 1)
      (UG    : (G s2) =
                 add (G s1) tid (eindex s1) (Astore x ord l v)
                     (DepsFile.expr_deps  (depf s1)  expr)
                     (DepsFile.lexpr_deps (depf s1) lexpr) (ectrl s1) ∅)
      (UINDEX : (eindex s2) = (eindex s1) + 1)
      (UREGS : (regf s2) = (regf s1))
      (UDEPS : (depf s2) = (depf s1))
      (UECTRL : (ectrl s2) = (ectrl s1))
  | fence ord 
      (LABELS : labels = [Afence ord])
      (II : instr = Instr.fence ord)
      (UPC   : (pc s2) = (pc s1) + 1)
      (UG    : (G s2) = add (G s1) tid (eindex s1) (Afence ord) ∅ ∅ (ectrl s1) ∅)
      (UINDEX : (eindex s2) = (eindex s1) + 1)
      (UREGS : (regf s2) = (regf s1))
      (UDEPS : (depf s2) = (depf s1))
      (UECTRL : (ectrl s2) = (ectrl s1))
  | cas_un expr_old expr_new rexmod xmod ordr ordw reg lexpr val l
      (L: l = RegFile.eval_lexpr (regf s1) lexpr)
      (NEXPECTED : val <> RegFile.eval_expr (regf s1) expr_old)
      (LABELS : labels = [Aload rexmod ordr l val])
      (II : instr =
            Instr.update (Instr.cas expr_old expr_new) rexmod xmod ordr ordw reg lexpr)
      (UPC   : (pc s2) = (pc s1) + 1)
      (UG    : (G s2) =
                 add (G s1) tid (eindex s1) (Aload rexmod ordr l val) ∅
                     (DepsFile.lexpr_deps (depf s1) lexpr) (ectrl s1)
                     (DepsFile.expr_deps (depf s1) expr_old))
      (UINDEX : (eindex s2) = (eindex s1) + 1)
      (UREGS : (regf s2) = RegFun.add reg val (regf s1))
      (UDEPS : (depf s2) = RegFun.add reg (eq (ThreadEvent tid (eindex s1))) (depf s1))
      (UECTRL : (ectrl s2) = (ectrl s1))
  | cas_suc expr_old expr_new rexmod xmod ordr ordw reg lexpr l expected new_value
      (L: l = RegFile.eval_lexpr (regf s1) lexpr)
      (EXPECTED: expected = RegFile.eval_expr (regf s1) expr_old)
      (NEW: new_value = RegFile.eval_expr (regf s1) expr_new)
      (LABELS : labels = [Astore xmod ordw l new_value; Aload rexmod ordr l expected])
      (II : instr =
            Instr.update (Instr.cas expr_old expr_new) rexmod xmod ordr ordw reg lexpr)
      (UPC   : (pc s2) = (pc s1) + 1)
      (UG    : (G s2) =
                 add_rmw (G s1)
                     tid (eindex s1)
                     (Aload rexmod ordr l expected) (Astore xmod ordw l new_value)
                     (DepsFile.expr_deps (depf s1) expr_new)
                     (DepsFile.lexpr_deps (depf s1) lexpr) (ectrl s1)
                     (DepsFile.expr_deps (depf s1) expr_old))
      (UINDEX : (eindex s2) = (eindex s1) + 2)
      (UREGS : (regf s2) = RegFun.add reg expected (regf s1))
      (UDEPS : (depf s2) = RegFun.add reg (eq (ThreadEvent tid (eindex s1))) (depf s1))
      (UECTRL : (ectrl s2) = (ectrl s1))
  | inc expr_add rexmod xmod ordr ordw reg lexpr val l nval
      (L: l = RegFile.eval_lexpr (regf s1) lexpr)
      (NVAL: nval = val + RegFile.eval_expr (regf s1) expr_add)
      (LABELS : labels = [Astore xmod ordw l nval; Aload rexmod ordr l val])
      (II : instr =
            Instr.update (Instr.fetch_add expr_add) rexmod xmod ordr ordw reg lexpr)
      (UPC   : (pc s2) = (pc s1) + 1)
      (UG    : (G s2) =
                 add_rmw (G s1) tid (eindex s1)
                     (Aload rexmod ordr l val)
                     (Astore xmod ordw l nval)
                     ((eq (ThreadEvent tid (eindex s1))) ∪₁ (DepsFile.expr_deps (depf s1) expr_add))
                     (DepsFile.lexpr_deps (depf s1) lexpr) (ectrl s1)
                     ∅)
      (UINDEX : (eindex s2) = (eindex s1) + 2)
      (UREGS : (regf s2) = RegFun.add reg val (regf s1))
      (UDEPS : (depf s2) = RegFun.add reg (eq (ThreadEvent tid (eindex s1))) (depf s1))
      (UECTRL : (ectrl s2) = (ectrl s1))
  | exchange expr_new rexmod xmod ordr ordw reg lexpr val l nval
      (L: l = RegFile.eval_lexpr (regf s1) lexpr)
      (NVAL: nval = RegFile.eval_expr (regf s1) expr_new)
      (LABELS : labels = [Astore xmod ordw l nval; Aload rexmod ordr l val])
      (II : instr =
            Instr.update (Instr.exchange expr_new) rexmod xmod ordr ordw reg lexpr)
      (UPC   : (pc s2) = (pc s1) + 1)
      (UG    : (G s2) =
                 add_rmw (G s1) tid (eindex s1)
                     (Aload rexmod ordr l val)
                     (Astore xmod ordw l nval)
                     (DepsFile.expr_deps (depf s1) expr_new)
                     (DepsFile.lexpr_deps (depf s1) lexpr) (ectrl s1)
                     ∅)
      (UINDEX : (eindex s2) = (eindex s1) + 2)
      (UREGS : (regf s2) = RegFun.add reg val (regf s1))
      (UDEPS : (depf s2) = RegFun.add reg (eq (ThreadEvent tid (eindex s1))) (depf s1))
      (UECTRL : (ectrl s2) = (ectrl s1)).      

  Definition istep (tid : thread_id) (labels : list label) s1 s2 :=
    ⟪ INSTRS : (instrs s1) = (instrs s2) ⟫ /\
    ⟪ ISTEP: exists instr, 
               Some instr = List.nth_error (instrs s1) (pc s1) /\
               istep_ tid labels s1 s2 instr ⟫.

  Definition step (tid : thread_id) s1 s2 :=
    exists lbls, istep tid lbls s1 s2.
  
  Definition thread_execution
             (tid : thread_id) (insts : list Instr.t) (pe : execution) :=
    exists s,
      ⟪ STEPS : (step tid)＊ (init insts) s ⟫ /\
      ⟪ TERMINAL : is_terminal s ⟫ /\
      ⟪ PEQ : (G s) = pe ⟫.

  Lemma preserve_event (tid : thread_id)
        s s' (STEPS : (step tid)＊ s s')
        e (INE : (acts_set (G s)) e):
    (acts_set (G s')) e.
  Proof using.
    apply clos_rt_rt1n in STEPS.
    induction STEPS; [done|]; intros.
    apply IHSTEPS.
    destruct H as [lbls STEP].
    red in STEP; desf.
    destruct ISTEP, ISTEP0; desf; rewrite UG.
    all: unfold add, add_rmw, acts_set in *; simpls; vauto.
  Qed.
  
  Definition thread_wf tid s :=
      forall e, (acts_set (G s)) e ->
                exists index,
                ⟪ EE : e = ThreadEvent tid index ⟫ /\
                ⟪ LT : index < (eindex s) ⟫.

  Lemma thread_wf_steps (tid : thread_id)
        s  (WF : thread_wf tid s)
        s' (STEPS : (step tid)＊ s s'):
    thread_wf tid s'.
  Proof using.
    apply clos_rt_rt1n in STEPS.
    induction STEPS; [done|]; intros.
    apply IHSTEPS.
    destruct H as [lbls STEP].
    red; unnw; intros e' INY.
    red in WF; unnw.
    red in STEP; desf.
    destruct ISTEP, ISTEP0; desf; rewrite UG, UINDEX in *; auto.
    all: unfold add, add_rmw, acts_set in *; simpls; vauto.
    all: try (destruct INY as [EIN|INX]; [|apply WF in INX; desf];
      eexists; split; eauto; lia).
    all: destruct INY as [EIN|[EIN|INX]]; [ | | apply WF in INX; desf];
      eexists; split; eauto; lia.
  Qed.

  Lemma same_lab (tid : thread_id) s s'
        (WF : thread_wf tid s) (STEPS : (step tid)＊ s s')
        e (INE : (acts_set (G s)) e):
    (lab (G s')) e = (lab (G s)) e.
  Proof using.
    apply clos_rt_rt1n in STEPS.
    induction STEPS; [done|]; intros.
    assert (thread_wf tid y) as YWF.
    { eapply thread_wf_steps; eauto.
        by apply rt_step; eauto. }
    assert (acts_set (G y) e) as INY.
    { eapply preserve_event; eauto.
        by apply rt_step; eauto. }
    rewrite IHSTEPS; auto.
    destruct H as [lbls STEP].
    assert (e <> (ThreadEvent tid (eindex x))) as NEIN1.
    { red in WF; unnw.
      destruct (WF e); desf.
      intros H; inv H.
      lia. }
    assert (e <> (ThreadEvent tid (eindex x + 1))) as NEIN2.
    { red in WF; unnw.
      destruct (WF e); desf.
      intros H; inv H.
      lia. }
    red in STEP; desf.
    destruct ISTEP, ISTEP0; desf; rewrite UG; auto.
    all: unfold add, add_rmw in *; simpls; vauto.
    all: unfold upd; desf.
  Qed.

End State.
