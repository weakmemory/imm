Require Import RelationClasses List Omega.
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
    s.(pc) >= s.(instrs).(length).
  
  Definition add G tid index elab ddata daddr dctrl drmw_dep :=
    let e := ThreadEvent tid index in 
    {| acts := e :: G.(acts);
       lab := upd G.(lab) e elab;
       rmw := G.(rmw);
       data := G.(data) ∪ ddata × (eq e);
       addr := G.(addr) ∪ daddr × (eq e);
       ctrl := G.(ctrl) ∪ dctrl × (eq e);
       rmw_dep := G.(rmw_dep) ∪ drmw_dep × (eq e);
       rf := ∅₂;
       co := ∅₂;
    |}.

  Definition add_rmw G tid index erlab ewlab ddata daddr dctrl drmw_dep :=
    let er:= ThreadEvent tid index in 
    let ew:= ThreadEvent tid (index + 1) in 
    let rw_edge := singl_rel er ew in
    {| acts := ew :: er :: G.(acts);
       lab := upd (upd G.(lab) er erlab) ew ewlab; 
       rmw := rw_edge ∪ G.(rmw);
       data := G.(data) ∪ ddata × (eq ew);
       addr := G.(addr) ∪ daddr × (eq er ∪₁ eq ew);
       ctrl := G.(ctrl) ∪ dctrl × (eq er ∪₁ eq ew);
       rmw_dep := G.(rmw_dep) ∪ drmw_dep × (eq er);
       rf := ∅₂;
       co := ∅₂;
    |}.

  Inductive istep_ tid labels s1 s2 instr : Prop :=
  | assign reg expr
      (LABELS : labels = nil)
      (II : instr = Instr.assign reg expr)
      (UPC : s2.(pc) = s1.(pc) + 1)
      (UG : s2.(G) = s1.(G))
      (UINDEX : s2.(eindex) = s1.(eindex))
      (UREGS : s2.(regf) = RegFun.add reg (RegFile.eval_expr s1.(regf) expr) s1.(regf))
      (UDEPS : s2.(depf) = RegFun.add reg (DepsFile.expr_deps s1.(depf) expr) s1.(depf))
      (UECTRL : s2.(ectrl) = s1.(ectrl))
  | if_ expr shift
      (LABELS : labels = nil)
      (II : instr = Instr.ifgoto expr shift)
      (UPC   : if Const.eq_dec (RegFile.eval_expr s1.(regf) expr) 0
               then s2.(pc) = s1.(pc) + 1
               else s2.(pc) = shift)
      (UG    : s2.(G) = s1.(G))
      (UINDEX : s2.(eindex) = s1.(eindex))
      (UREGS : s2.(regf) = s1.(regf))
      (UDEPS : s2.(depf) = s1.(depf))
      (UECTRL : s2.(ectrl) = (DepsFile.expr_deps s1.(depf) expr) ∪₁ s1.(ectrl))
  | load ord reg lexpr val l
      (L: l = RegFile.eval_lexpr s1.(regf) lexpr)
      (II : instr = Instr.load ord reg lexpr)
      (LABELS : labels = [Aload false ord (RegFile.eval_lexpr s1.(regf) lexpr) val])
      (UPC   : s2.(pc) = s1.(pc) + 1)
      (UG    : s2.(G) =
                 add s1.(G) tid s1.(eindex) (Aload false ord (RegFile.eval_lexpr s1.(regf) lexpr) val) ∅
                     (DepsFile.lexpr_deps s1.(depf) lexpr) s1.(ectrl) ∅)
      (UINDEX : s2.(eindex) = s1.(eindex) + 1)
      (UREGS : s2.(regf) = RegFun.add reg val s1.(regf))
      (UDEPS : s2.(depf) = RegFun.add reg (eq (ThreadEvent tid s1.(eindex))) s1.(depf))
      (UECTRL : s2.(ectrl) = s1.(ectrl))
  | store ord lexpr expr l v x
      (L: l = RegFile.eval_lexpr s1.(regf) lexpr)
      (V: v = RegFile.eval_expr  s1.(regf)  expr)
      (X: x = Xpln)
      (LABELS : labels = [Astore x ord l v])
      (II : instr = Instr.store ord lexpr expr)
      (UPC   : s2.(pc) = s1.(pc) + 1)
      (UG    : s2.(G) =
                 add s1.(G) tid s1.(eindex) (Astore x ord l v)
                     (DepsFile.expr_deps  s1.(depf)  expr)
                     (DepsFile.lexpr_deps s1.(depf) lexpr) s1.(ectrl) ∅)
      (UINDEX : s2.(eindex) = s1.(eindex) + 1)
      (UREGS : s2.(regf) = s1.(regf))
      (UDEPS : s2.(depf) = s1.(depf))
      (UECTRL : s2.(ectrl) = s1.(ectrl))
  | fence ord 
      (LABELS : labels = [Afence ord])
      (II : instr = Instr.fence ord)
      (UPC   : s2.(pc) = s1.(pc) + 1)
      (UG    : s2.(G) = add s1.(G) tid s1.(eindex) (Afence ord) ∅ ∅ s1.(ectrl) ∅)
      (UINDEX : s2.(eindex) = s1.(eindex) + 1)
      (UREGS : s2.(regf) = s1.(regf))
      (UDEPS : s2.(depf) = s1.(depf))
      (UECTRL : s2.(ectrl) = s1.(ectrl))
  | cas_un expr_old expr_new rexmod xmod ordr ordw reg lexpr val l
      (L: l = RegFile.eval_lexpr s1.(regf) lexpr)
      (NEXPECTED : val <> RegFile.eval_expr s1.(regf) expr_old)
      (LABELS : labels = [Aload rexmod ordr l val])
      (II : instr =
            Instr.update (Instr.cas expr_old expr_new) rexmod xmod ordr ordw reg lexpr)
      (UPC   : s2.(pc) = s1.(pc) + 1)
      (UG    : s2.(G) =
                 add s1.(G) tid s1.(eindex) (Aload rexmod ordr l val) ∅
                     (DepsFile.lexpr_deps s1.(depf) lexpr) s1.(ectrl)
                     (DepsFile.expr_deps s1.(depf) expr_old))
      (UINDEX : s2.(eindex) = s1.(eindex) + 1)
      (UREGS : s2.(regf) = RegFun.add reg val s1.(regf))
      (UDEPS : s2.(depf) = RegFun.add reg (eq (ThreadEvent tid s1.(eindex))) s1.(depf))
      (UECTRL : s2.(ectrl) = s1.(ectrl))
  | cas_suc expr_old expr_new rexmod xmod ordr ordw reg lexpr l expected new_value
      (L: l = RegFile.eval_lexpr s1.(regf) lexpr)
      (EXPECTED: expected = RegFile.eval_expr s1.(regf) expr_old)
      (NEW: new_value = RegFile.eval_expr s1.(regf) expr_new)
      (LABELS : labels = [Astore xmod ordw l new_value; Aload rexmod ordr l expected])
      (II : instr =
            Instr.update (Instr.cas expr_old expr_new) rexmod xmod ordr ordw reg lexpr)
      (UPC   : s2.(pc) = s1.(pc) + 1)
      (UG    : s2.(G) =
                 add_rmw s1.(G)
                     tid s1.(eindex)
                     (Aload rexmod ordr l expected) (Astore xmod ordw l new_value)
                     (DepsFile.expr_deps s1.(depf) expr_new)
                     (DepsFile.lexpr_deps s1.(depf) lexpr) s1.(ectrl)
                     (DepsFile.expr_deps s1.(depf) expr_old))
      (UINDEX : s2.(eindex) = s1.(eindex) + 2)
      (UREGS : s2.(regf) = RegFun.add reg expected s1.(regf))
      (UDEPS : s2.(depf) = RegFun.add reg (eq (ThreadEvent tid s1.(eindex))) s1.(depf))
      (UECTRL : s2.(ectrl) = s1.(ectrl))
  | inc expr_add rexmod xmod ordr ordw reg lexpr val l nval
      (L: l = RegFile.eval_lexpr s1.(regf) lexpr)
      (NVAL: nval = val + RegFile.eval_expr s1.(regf) expr_add)
      (LABELS : labels = [Astore xmod ordw l nval; Aload rexmod ordr l val])
      (II : instr =
            Instr.update (Instr.fetch_add expr_add) rexmod xmod ordr ordw reg lexpr)
      (UPC   : s2.(pc) = s1.(pc) + 1)
      (UG    : s2.(G) =
                 add_rmw s1.(G) tid s1.(eindex)
                     (Aload rexmod ordr l val)
                     (Astore xmod ordw l nval)
                     ((eq (ThreadEvent tid s1.(eindex))) ∪₁ (DepsFile.expr_deps s1.(depf) expr_add))
                     (DepsFile.lexpr_deps s1.(depf) lexpr) s1.(ectrl)
                     ∅)
      (UINDEX : s2.(eindex) = s1.(eindex) + 2)
      (UREGS : s2.(regf) = RegFun.add reg val s1.(regf))
      (UDEPS : s2.(depf) = RegFun.add reg (eq (ThreadEvent tid s1.(eindex))) s1.(depf))
      (UECTRL : s2.(ectrl) = s1.(ectrl))
  | exchange expr_new rexmod xmod ordr ordw reg lexpr val l nval
      (L: l = RegFile.eval_lexpr s1.(regf) lexpr)
      (NVAL: nval = RegFile.eval_expr s1.(regf) expr_new)
      (LABELS : labels = [Astore xmod ordw l nval; Aload rexmod ordr l val])
      (II : instr =
            Instr.update (Instr.exchange expr_new) rexmod xmod ordr ordw reg lexpr)
      (UPC   : s2.(pc) = s1.(pc) + 1)
      (UG    : s2.(G) =
                 add_rmw s1.(G) tid s1.(eindex)
                     (Aload rexmod ordr l val)
                     (Astore xmod ordw l nval)
                     (DepsFile.expr_deps s1.(depf) expr_new)
                     (DepsFile.lexpr_deps s1.(depf) lexpr) s1.(ectrl)
                     ∅)
      (UINDEX : s2.(eindex) = s1.(eindex) + 2)
      (UREGS : s2.(regf) = RegFun.add reg val s1.(regf))
      (UDEPS : s2.(depf) = RegFun.add reg (eq (ThreadEvent tid s1.(eindex))) s1.(depf))
      (UECTRL : s2.(ectrl) = s1.(ectrl)).      

  Definition istep (tid : thread_id) (labels : list label) s1 s2 :=
    ⟪ INSTRS : s1.(instrs) = s2.(instrs) ⟫ /\
    ⟪ ISTEP: exists instr, 
               Some instr = List.nth_error s1.(instrs) s1.(pc) /\
               istep_ tid labels s1 s2 instr ⟫.

  Definition step (tid : thread_id) s1 s2 :=
    exists lbls, istep tid lbls s1 s2.
  
  Definition thread_execution
             (tid : thread_id) (insts : list Instr.t) (pe : execution) :=
    exists s,
      ⟪ STEPS : (step tid)＊ (init insts) s ⟫ /\
      ⟪ TERMINAL : is_terminal s ⟫ /\
      ⟪ PEQ : s.(G) = pe ⟫.

  Lemma preserve_event (tid : thread_id)
        s s' (STEPS : (step tid)＊ s s')
        e (INE : s.(G).(acts_set) e):
    s'.(G).(acts_set) e.
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
      forall e, s.(G).(acts_set) e ->
                exists index,
                ⟪ EE : e = ThreadEvent tid index ⟫ /\
                ⟪ LT : index < s.(eindex) ⟫.

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
      eexists; split; eauto; omega).
    all: destruct INY as [EIN|[EIN|INX]]; [ | | apply WF in INX; desf];
      eexists; split; eauto; omega.
  Qed.

  Lemma same_lab (tid : thread_id) s s'
        (WF : thread_wf tid s) (STEPS : (step tid)＊ s s')
        e (INE : s.(G).(acts_set) e):
    s'.(G).(lab) e = s.(G).(lab) e.
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
      omega. }
    assert (e <> (ThreadEvent tid (eindex x + 1))) as NEIN2.
    { red in WF; unnw.
      destruct (WF e); desf.
      intros H; inv H.
      omega. }
    red in STEP; desf.
    destruct ISTEP, ISTEP0; desf; rewrite UG; auto.
    all: unfold add, add_rmw in *; simpls; vauto.
    all: unfold upd; desf.
  Qed.

End State.
