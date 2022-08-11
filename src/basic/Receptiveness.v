Require Import ClassicalDescription Lia.

From hahn Require Import Hahn.
Require Import Events.
Require Import Execution.
Require Import Prog.
Require Import ProgToExecution.
Require Import ProgToExecutionProperties.
Require Import RMWinstrProps.

Set Implicit Arguments.

(******************************************************************************)
(** **  *)
(******************************************************************************)

Lemma ectrl_ctrl_step (tid : thread_id) 
         s s' (STEP : step tid s s')
         MOD (ECTRL: exists a, (MOD ∩₁ ectrl s') a)
        (NCTRL: MOD ∩₁ dom_rel ((ctrl (G s'))) ⊆₁ ∅) :
         (G s) = (G s').
Proof using.
destruct STEP; desc.
red in H; desc.
destruct ISTEP0; try done.
all: exfalso; eapply NCTRL.
all: revert ECTRL;  unfolder; splits; try edone.
all: desc; eauto; exists (ThreadEvent tid (eindex s)).
all: rewrite UG; unfold add; ins; rewrite <- UECTRL; basic_solver.
Qed.


Lemma TWF_helper tid s1 (TWF : thread_wf tid s1): 
~ acts_set (G s1) (ThreadEvent tid ((eindex s1))).
Proof using.
red in TWF.
intro.
specialize (TWF (ThreadEvent tid (eindex s1)) H); desf.
lia.
Qed.

Lemma TWF_helper_rmw tid s1 (TWF : thread_wf tid s1): 
~ acts_set (G s1) (ThreadEvent tid ((eindex s1) + 1)).
Proof using.
red in TWF.
intro.
specialize (TWF (ThreadEvent tid (eindex s1 +1)) H); desf.
lia.
Qed.


Lemma acts_increasing (tid : thread_id) s s' (STEP : step tid s s') :
  (acts_set (G s)) ⊆₁ (acts_set (G s')).
Proof using.
destruct STEP; desc.
red in H; desc.
destruct ISTEP0.
all: rewrite UG; try done.
all: unfold add, add_rmw, acts_set; ins.
all: unfolder; ins; desc; eauto.
Qed.

Lemma is_r_ex_increasing (tid : thread_id) s s' (STEP : step tid s s') (TWF : thread_wf tid s):
  (acts_set (G s)) ∩₁ R_ex (lab (G s)) ⊆₁ R_ex (lab (G s')).
Proof using.
destruct STEP; desc.
red in H; desc.
destruct ISTEP0.
all: rewrite UG; try done.
all: unfold add, add_rmw, R_ex; ins.
all: unfolder; ins; desc; eauto.
all: rewrite !updo; try done.
all: try by (intro; subst; eapply TWF_helper; edone).
all: try by (intro; subst; eapply TWF_helper_rmw; edone).
Qed.

Lemma is_r_increasing (tid : thread_id) s s' (STEP : step tid s s') (TWF : thread_wf tid s):
  (acts_set (G s)) ∩₁ is_r (lab (G s)) ⊆₁ is_r (lab (G s')).
Proof using.
destruct STEP; desc.
red in H; desc.
destruct ISTEP0.
all: rewrite UG; try done.
all: unfold add, add_rmw, is_r; ins.
all: unfolder; ins; desc; eauto.
all: rewrite !updo; try done.
all: try by (intro; subst; eapply TWF_helper; edone).
all: try by (intro; subst; eapply TWF_helper_rmw; edone).
Qed.


Lemma is_w_increasing (tid : thread_id) s s' (STEP : step tid s s') (TWF : thread_wf tid s):
  (acts_set (G s)) ∩₁ is_w (lab (G s)) ⊆₁ is_w (lab (G s')).
Proof using.
destruct STEP; desc.
red in H; desc.
destruct ISTEP0.
all: rewrite UG; try done.
all: unfold add, add_rmw, is_w; ins.
all: unfolder; ins; desc; eauto.
all: rewrite !updo; try done.
all: try by (intro; subst; eapply TWF_helper; edone).
all: try by (intro; subst; eapply TWF_helper_rmw; edone).
Qed.

(******************************************************************************)
(** **  *)
(******************************************************************************)

Lemma regf_expr_helper regf regf' depf MOD expr
  (REGF : forall reg, RegFun.find reg regf = RegFun.find reg regf' \/ 
           (exists a, RegFun.find reg depf a /\ MOD a))
  (NDEP: forall a (IN: MOD a), ~ DepsFile.expr_deps depf expr a):
  RegFile.eval_expr regf expr = RegFile.eval_expr regf' expr.
Proof using.
unfold DepsFile.expr_deps, DepsFile.val_deps in NDEP.
unfold RegFile.eval_expr, RegFile.eval_value.
destruct expr.
- destruct val; [by vauto| specialize (REGF reg); desf].
  exfalso; eapply NDEP; edone.
- destruct op0; [by vauto| specialize (REGF reg); desf].
  rewrite REGF; auto.
  exfalso; eapply NDEP; edone.
- destruct op1, op2.
* by vauto.
* specialize (REGF reg); desf; [rewrite REGF|]; eauto.
  exfalso; eapply NDEP; [edone| basic_solver].
* specialize (REGF reg); desf; [rewrite REGF|]; eauto. 
  exfalso; eapply NDEP; [edone| basic_solver].
* generalize (REGF reg0); intro REGF0. 
  specialize (REGF reg).
  desf.
  by rewrite REGF, REGF0; auto.
  all: exfalso; eapply NDEP; [edone| basic_solver].
Qed.

Lemma regf_lexpr_helper regf regf' depf MOD expr
  (REGF : forall reg, RegFun.find reg regf = RegFun.find reg regf' \/ 
            (exists a, RegFun.find reg depf a /\ MOD a))
  (NDEP: forall a (IN: MOD a), ~ DepsFile.lexpr_deps depf expr a):
  RegFile.eval_lexpr regf expr = RegFile.eval_lexpr regf' expr.
Proof using.
unfold DepsFile.lexpr_deps in NDEP.
unfold RegFile.eval_lexpr.
desf; exfalso; apply n; erewrite regf_expr_helper; eauto.
ins; specialize (REGF reg); desf; eauto.
Qed.

(******************************************************************************)
(** **  *)
(******************************************************************************)

Definition sim_execution G G' MOD :=
      ⟪ ACTS : (acts_set G) = (acts_set G') ⟫ /\
      ⟪ TS: threads_set G ≡₁ threads_set G'⟫ /\
      ⟪ SAME : same_lab_u2v (lab G') (lab G) ⟫ /\
      ⟪ OLD_VAL : forall a (NIN: ~ MOD a), val ((lab G')) a = val ((lab G)) a ⟫ /\
      ⟪ RMW  : (rmw G)  ≡ (rmw G')  ⟫ /\
      ⟪ DATA : (data G) ≡ (data G') ⟫ /\
      ⟪ ADDR : (addr G) ≡ (addr G') ⟫ /\
      ⟪ CTRL : (ctrl G) ≡ (ctrl G') ⟫ /\
      ⟪ FRMW : (rmw_dep G) ≡ (rmw_dep G') ⟫ /\
      ⟪ RRF : (rf G) ≡ (rf G') ⟫ /\
      ⟪ RCO : (co G) ≡ (co G') ⟫.

Definition sim_state s s' MOD (new_rfi : relation actid) new_val := 
      ⟪ INSTRS  : (instrs s) = (instrs s') ⟫ /\
      ⟪ PC  : (pc s) = (pc s') ⟫ /\
      ⟪ EXEC : sim_execution (G s) (G s') MOD ⟫ /\
      ⟪ EINDEX  : (eindex s) = (eindex s') ⟫ /\
      ⟪ REGF  : forall reg, RegFun.find reg (regf s) = RegFun.find reg (regf s') \/ 
exists a, (RegFun.find reg (depf s)) a /\ MOD a ⟫ /\
      ⟪ DEPF  : (depf s) = (depf s') ⟫ /\
      ⟪ ECTRL  : (ectrl s) = (ectrl s') ⟫ /\
      ⟪ NEW_VAL1 : forall r w (RF: new_rfi w r) (INr: (acts_set (G s')) r) 
(INw: (acts_set (G s')) w) (READ: is_r (lab (G s')) r) (WRITE: is_w (lab (G s')) w) (IN_MOD: MOD r), 
                     val ((lab (G s'))) r = val ((lab (G s'))) w ⟫ /\
      ⟪ NEW_VAL2 : forall r (READ: is_r (lab (G s')) r) (IN_MOD: MOD r) 
                     (IN: (acts_set (G s')) r) (NIN_NEW_RF: ~ (codom_rel new_rfi) r), 
                     val ((lab (G s'))) r = Some (new_val r) ⟫.

Lemma sim_execution_same_r G G' MOD (EXEC: sim_execution G G' MOD) :
is_r (lab G') ≡₁ is_r (lab G).
Proof using.
red in EXEC; desf.
eby erewrite same_lab_u2v_is_r.
Qed.

Lemma sim_execution_same_w G G' MOD (EXEC: sim_execution G G' MOD) :
is_w (lab G') ≡₁ is_w (lab G).
Proof using.
red in EXEC; desf.
eby erewrite same_lab_u2v_is_w.
Qed.

Lemma sim_execution_same_acts G G' MOD (EXEC: sim_execution G G' MOD) :
acts_set G ≡₁ acts_set G'.
Proof using.
red in EXEC; desf. by rewrite ACTS.
Qed.

(******************************************************************************)
(** **  *)
(******************************************************************************)

Lemma receptiveness_sim_assign (tid : thread_id)
  s1 s2 (INSTRS0 : instrs s1 = instrs s2)
  (reg : Reg.t) (expr : Instr.expr)
  (ISTEP : Some (Instr.assign reg expr) = nth_error (instrs s1) (pc s1))
  (UPC : pc s2 = pc s1 + 1) (UG : G s2 = G s1)
  (UINDEX : eindex s2 = eindex s1)
  (UREGS : regf s2 = RegFun.add reg (RegFile.eval_expr (regf s1) expr) (regf s1))
  (UDEPS : depf s2 = RegFun.add reg (DepsFile.expr_deps (depf s1) expr) (depf s1))
  (UECTRL : ectrl s2 = ectrl s1)
  MOD (new_rfi : relation actid) new_val
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof using.
red in SIM; desc.
cut (exists instrs pc G_ eindex regf depf ectrl, 
  step tid s1' {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |} /\ 
  (sim_state s2 {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |}
  MOD new_rfi new_val)).
by ins; desc; eauto.
do 7 eexists; splits; red; splits.
  * eexists; red; splits; [by ins; eauto|].
    eby eexists; splits; [ rewrite <- INSTRS, <- PC| eapply assign; reflexivity].
  * ins; congruence.
  * ins; congruence.
  * ins; congruence.
  * ins; congruence.
  * ins; rewrite UREGS, UDEPS.
    unfold RegFun.add, RegFun.find in *; desf.
    destruct (classic ((exists a : actid, DepsFile.expr_deps (depf s1) expr a /\ MOD a))) as [A|A].
    by auto.
    by left; apply (regf_expr_helper (regf s1) (regf s1') (depf s1) MOD expr REGF); eauto.
  * ins; congruence.
  * ins; congruence.
  * by ins; apply NEW_VAL1; try done; rewrite <- UG.
  * by ins; apply NEW_VAL2; try done; rewrite <- UG.
Qed.

Lemma receptiveness_sim_if_else (tid : thread_id)
  s1 s2 (INSTRS0 : instrs s1 = instrs s2)
  (expr : Instr.expr) (shift : nat)
  (e : RegFile.eval_expr (regf s1) expr = 0)
  (ISTEP : Some (Instr.ifgoto expr shift) = nth_error (instrs s1) (pc s1))
  (UPC : pc s2 = pc s1 + 1) (UG : G s2 = G s1)
  (UINDEX : eindex s2 = eindex s1)
  (UREGS : regf s2 = regf s1)
  (UDEPS : depf s2 = depf s1)
  (UECTRL : ectrl s2 = DepsFile.expr_deps (depf s1) expr ∪₁ ectrl s1)
  MOD (new_rfi : relation actid) new_val
  (NCTRL : MOD ∩₁ ectrl s2 ⊆₁ ∅)
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof using.
red in SIM; desc.
cut (exists instrs pc G_ eindex regf depf ectrl, 
  step tid s1' {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |} /\ 
  (sim_state s2 {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |}
  MOD new_rfi new_val)).
by ins; desc; eauto.
eexists.
  exists (if Const.eq_dec (RegFile.eval_expr (regf s1') expr) 0
        then pc s1' + 1 else shift).
  do 5 eexists; splits; red; splits.
  * eexists; red; splits; [by ins; eauto|].
    eexists; splits; [eby rewrite <- INSTRS, <- PC|].
    eapply if_; try reflexivity; ins; desf.
  * ins; congruence.
  * ins.
    erewrite <- regf_expr_helper with (regf:= regf s1).
    desf; congruence.
    eauto.
    ins; intro; eapply NCTRL; rewrite UECTRL; basic_solver.
  * ins; congruence.
  * ins; congruence.
  * ins; rewrite UREGS, UDEPS; eauto.
  * ins; congruence.
  * ins; congruence.
  * by ins; apply NEW_VAL1; try done; rewrite <- UG.
  * by ins; apply NEW_VAL2; try done; rewrite <- UG.
Qed.

Lemma receptiveness_sim_if_then (tid : thread_id)
  s1 s2 (INSTRS0 : instrs s1 = instrs s2)
  (expr : Instr.expr) (shift : nat)
  (n : RegFile.eval_expr (regf s1) expr <> 0)
  (ISTEP : Some (Instr.ifgoto expr shift) = nth_error (instrs s1) (pc s1))
  (UPC : pc s2 = shift) (UG : G s2 = G s1)
  (UINDEX : eindex s2 = eindex s1)
  (UREGS : regf s2 = regf s1)
  (UDEPS : depf s2 = depf s1)
  (UECTRL : ectrl s2 = DepsFile.expr_deps (depf s1) expr ∪₁ ectrl s1)
  MOD (new_rfi : relation actid) new_val
  (NCTRL : MOD ∩₁ ectrl s2 ⊆₁ ∅)
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof using.
red in SIM; desc.
cut (exists instrs pc G_ eindex regf depf ectrl, 
  step tid s1' {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |} /\ 
  (sim_state s2 {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |}
  MOD new_rfi new_val)).
by ins; desc; eauto.
 eexists.
  exists (if Const.eq_dec (RegFile.eval_expr (regf s1') expr) 0
        then pc s1' + 1 else shift).
  do 5 eexists; splits; red; splits.
  * eexists; red; splits; [by ins; eauto|].
    eexists; splits; [eby rewrite <- INSTRS, <- PC|].
    eapply if_; try reflexivity; ins; desf.
  * ins; congruence.
  * ins.
    erewrite <- regf_expr_helper with (regf:= regf s1).
    desf; congruence.
    eauto.
    ins; intro; eapply NCTRL; rewrite UECTRL; basic_solver.
  * ins; congruence.
  * ins; congruence.
  * ins; rewrite UREGS, UDEPS; eauto.
  * ins; congruence.
  * ins; congruence.
  * by ins; apply NEW_VAL1; try done; rewrite <- UG.
  * by ins; apply NEW_VAL2; try done; rewrite <- UG.
Qed.

Definition new_rfi_ex (new_rfi :relation actid) :=
new_rfi ∪ ⦗ set_compl (codom_rel new_rfi) ⦘.

Lemma new_rfi_unique (new_rfi : relation actid)
      (new_rfif : functional new_rfi⁻¹):
forall r, exists ! w, (new_rfi_ex new_rfi)⁻¹  r w.
Proof using.
ins.
destruct (classic ((codom_rel new_rfi) r)) as [X|X].
- unfolder in X; desf.
exists x; red; splits.
unfold new_rfi_ex; basic_solver 12.
unfold new_rfi_ex; unfolder; ins; desf.
eapply new_rfif; basic_solver.
exfalso; eauto.
- exists r; red; splits.
unfold new_rfi_ex; basic_solver 12.
unfold new_rfi_ex; unfolder; ins; desf.
unfolder in X; exfalso; eauto.
Qed.

Definition new_write new_rfi new_rfif := 
  unique_choice (new_rfi_ex new_rfi)⁻¹ (@new_rfi_unique new_rfi new_rfif).

Definition get_val (v: option value) := 
  match v with | Some v => v | _ => 0 end.

Lemma RFI_index_helper tid s new_rfi (TWF : thread_wf tid s)
   (RFI_INDEX : new_rfi ⊆ ext_sb)
   w r (RFI: new_rfi w r) 
  (IN: ThreadEvent tid (eindex s) = r \/ (acts_set (G s)) r) :
   w <> ThreadEvent tid ((eindex s)).
Proof using.
intro; subst; desf.
apply RFI_INDEX in RFI.
eby eapply ext_sb_irr.
specialize (TWF r IN); desf.
apply RFI_INDEX in RFI.
unfold sb, ext_sb in RFI; unfolder in RFI; desf; lia.
Qed.

Lemma receptiveness_sim_load (tid : thread_id)
  s1 s2 (INSTRS0 : instrs s1 = instrs s2)
  (ord : mode) (reg : Reg.t)
  (lexpr : Instr.lexpr) (ISTEP : Some (Instr.load ord reg lexpr) = nth_error (instrs s1) (pc s1))
  (val_ : value) (UPC : pc s2 = pc s1 + 1)
  (UG : G s2 =
     add (G s1) tid (eindex s1)
       (Aload false ord (RegFile.eval_lexpr (regf s1) lexpr) val_) 
       ∅ (DepsFile.lexpr_deps (depf s1) lexpr) (ectrl s1) 
       ∅)
  (UINDEX : eindex s2 = eindex s1 + 1)
  (UREGS : regf s2 = RegFun.add reg val_ (regf s1))
  (UDEPS : depf s2 = RegFun.add reg (eq (ThreadEvent tid (eindex s1))) (depf s1))
  (UECTRL : ectrl s2 = ectrl s1)
  MOD (new_rfi : relation actid) new_val
  (NADDR : MOD ∩₁ dom_rel ((addr (G s2))) ⊆₁ ∅)
  (RFI_INDEX : new_rfi ⊆ ext_sb)
  (TWF : thread_wf tid s1)
  (new_rfif : functional new_rfi⁻¹)
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof using.
generalize (@new_write new_rfi new_rfif); intro F; destruct F as [new_w F].
red in SIM; desc.

assert (SAME_LOC: RegFile.eval_lexpr (regf s1) lexpr = RegFile.eval_lexpr (regf s1') lexpr).
{ ins; eapply regf_lexpr_helper; eauto.
ins; intro; eapply NADDR; unfolder; splits; eauto.
exists (ThreadEvent tid (eindex s1)).
rewrite UG; unfold add; basic_solver. } 

cut (exists instrs pc G_ eindex regf depf ectrl, 
  step tid s1' {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |} /\ 
  (sim_state s2 {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |}
  MOD new_rfi new_val)).
by ins; desc; eauto.

do 7 eexists; splits; red; splits.
  * eexists; red; splits; [by ins; eauto|].
    eexists; splits; [eby rewrite <- INSTRS, <- PC |].
    eapply load with (val := 
      if excluded_middle_informative (MOD (ThreadEvent tid (eindex s1'))) 
      then if excluded_middle_informative ((codom_rel new_rfi) (ThreadEvent tid (eindex s1'))) 
           then (get_val (val (lab (G s1')) (new_w (ThreadEvent tid (eindex s1')))))
           else (new_val (ThreadEvent tid (eindex s1')))
      else val_);
    reflexivity.
  * ins; congruence.
  * ins; congruence.
  * ins.
    destruct (G s2) as [acts2 lab2 rmw2 data2 addr2 ctrl2 rf2 co2].
    inversion UG; subst; clear UG.
    red in EXEC; desc.
    red; splits; ins.
    + by rewrite EINDEX, ACTS.
    + by rewrite TS. 
    + rewrite EINDEX.
      unfold same_lab_u2v in *; intro e.
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1'))).
      { by subst; rewrite !upds. }
      ins. rewrite !updo; auto.
    + rewrite EINDEX.
      destruct (eq_dec_actid a (ThreadEvent tid (eindex s1'))).
      by desf; unfold val; rewrite !upds.
      unfold val; rewrite !updo; [|intro; desf|intro; desf].
      by apply OLD_VAL in NIN; unfold val in NIN; rewrite NIN.
    + by rewrite DATA, EINDEX.
    + by rewrite ADDR, EINDEX, DEPF.
    + by rewrite CTRL, EINDEX, ECTRL.
    + by rewrite FRMW, EINDEX.
  * ins; congruence.
  * ins; rewrite UREGS, UDEPS.
    unfold RegFun.add, RegFun.find in *; desf; eauto.
  * eby ins; rewrite <- DEPF, <- EINDEX.
  * ins; congruence.
  * simpl; ins.
     unfold add, acts_set in INw; ins.
    destruct (eq_dec_actid w (ThreadEvent tid (eindex s1'))); subst.
    + exfalso; eapply RFI_index_helper.
      edone.
      eapply RFI_INDEX.
      edone.
      unfold add, acts_set in INr; ins.
      rewrite EINDEX; destruct INr; [eauto|].
      right; eapply sim_execution_same_acts; eauto.
      by rewrite EINDEX.
    + destruct INw as [X|INw]; [desf|].
      destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
      -- unfold val in *; rewrite !upds.
         rewrite !updo; try done.
         destruct (excluded_middle_informative (MOD (ThreadEvent tid (eindex s1')))); [|desf].
         destruct (excluded_middle_informative (codom_rel new_rfi (ThreadEvent tid (eindex s1')))).
         2: by exfalso; apply n0; basic_solver 12.
         assert (w = new_w (ThreadEvent tid (eindex s1'))).
         { assert (U: exists ! w1 : actid, (new_rfi_ex new_rfi)⁻¹ (ThreadEvent tid (eindex s1')) w1).
           apply new_rfi_unique, new_rfif.
           eapply unique_existence with 
           (P:= fun x => (@new_rfi_ex new_rfi)⁻¹ (ThreadEvent tid (eindex s1')) x) in U; desc.
           eapply U0.
           unfold new_rfi_ex.
           basic_solver.
           apply F. }
         unfold is_w in WRITE; rewrite updo in WRITE; desf.
      -- unfold val in *; rewrite !updo; try done.
         eapply NEW_VAL1; try edone.
         { unfolder in INr. desf. }
         { by unfold is_r in *; rewrite updo in READ. }
           by unfold is_w in *; rewrite updo in WRITE.
  * simpl; ins.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    + destruct (excluded_middle_informative (MOD (ThreadEvent tid (eindex s1')))); [subst|desf].
      destruct (excluded_middle_informative (codom_rel new_rfi (ThreadEvent tid (eindex s1')))); [desf|].
      by unfold val in *; rewrite !upds.
    + unfold val in *; rewrite !updo; try done.
      apply NEW_VAL2; try done.
      { by unfold is_r in *; rewrite updo in READ. }
        by unfolder in IN; unfold add in IN; ins; desf.
Qed.

Lemma receptiveness_sim_store (tid : thread_id)
  s1 s2 (INSTRS0 : instrs s1 = instrs s2)
  (ord : mode) (reg : Reg.t)
  (lexpr : Instr.lexpr) (expr : Instr.expr)
  (ISTEP : Some (Instr.store ord lexpr expr) = nth_error (instrs s1) (pc s1))
  (UPC : pc s2 = pc s1 + 1)
  (UG : G s2 = add (G s1) tid (eindex s1)
         (Astore Xpln ord (RegFile.eval_lexpr (regf s1) lexpr) (RegFile.eval_expr (regf s1) expr)) 
         (DepsFile.expr_deps (depf s1) expr) (DepsFile.lexpr_deps (depf s1) lexpr) (ectrl s1) ∅) 
  (UINDEX : eindex s2 = eindex s1 + 1)
  (UREGS : regf s2 = regf s1)
  (UDEPS : depf s2 = depf s1)
  (UECTRL : ectrl s2 = ectrl s1)
  MOD (new_rfi : relation actid) new_val
  (NADDR : MOD ∩₁ dom_rel ((addr (G s2))) ⊆₁ ∅)
  (NDATA: ⦗MOD⦘ ⨾ (data (G s2)) ⨾ ⦗set_compl MOD⦘ ⊆ ∅₂)
   (RFI_INDEX : new_rfi ⊆ ext_sb)
  (TWF : thread_wf tid s1)
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof using.
red in SIM; desc.

assert (SAME_LOC: RegFile.eval_lexpr (regf s1) lexpr = RegFile.eval_lexpr (regf s1') lexpr).
{ ins; eapply regf_lexpr_helper; eauto.
ins; intro; eapply NADDR; unfolder; splits; eauto.
exists (ThreadEvent tid (eindex s1)).
rewrite UG; unfold add; basic_solver. } 

cut (exists instrs pc G_ eindex regf depf ectrl, 
  step tid s1' {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |} /\ 
  (sim_state s2 {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |}
  MOD new_rfi new_val)).
by ins; desc; eauto.

 do 7 eexists; splits; red; splits.
  * eexists; red; splits; [by ins; eauto|].
    eexists; splits; [eby rewrite <- INSTRS, <- PC |].
    eapply store; reflexivity.
  * ins; congruence.
  * ins; congruence.
  * ins.
    destruct (G s2) as [acts2 lab2 rmw2 data2 addr2 ctrl2 rf2 co2].
    inversion UG; subst; clear UG.
    red in EXEC; desc.
    red; splits; ins.
    + by rewrite EINDEX, ACTS.
    + by rewrite TS. 
    + rewrite EINDEX.
      unfold same_lab_u2v in *; intro e.
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1'))).
      { by subst; rewrite !upds. }
      rewrite !updo; auto.
    + rewrite EINDEX.
      destruct (eq_dec_actid a (ThreadEvent tid (eindex s1'))); subst.
      -- desf; unfold val; rewrite !upds.
         erewrite regf_expr_helper; try edone.
         intro reg0; specialize (REGF reg0); desf; eauto.
         ins; intro DEPS; eapply NDATA; unfolder; splits; eauto.
         by rewrite EINDEX.
      -- unfold val;  rewrite !updo; try done.
         by apply OLD_VAL in NIN; unfold val in NIN; rewrite NIN.
    + by rewrite DATA, EINDEX, DEPF.
    + by rewrite ADDR, EINDEX, DEPF.
    + by rewrite CTRL, EINDEX, ECTRL.
    + by rewrite FRMW, EINDEX.
  * ins; congruence.
  * ins; rewrite UREGS, UDEPS.
    unfold RegFun.add, RegFun.find in *; desf; eauto.
  * by ins; rewrite <- DEPF, <- UDEPS.
  * ins; congruence.
  * simpl; ins.
    unfold add, acts_set in INw; ins.
    destruct (eq_dec_actid w (ThreadEvent tid (eindex s1'))); subst.
    + exfalso; eapply RFI_index_helper.
      edone.
      eapply RFI_INDEX.
      edone.
      unfold add, acts_set in INr; ins.
      rewrite EINDEX; destruct INr; [eauto|].
      right; eapply sim_execution_same_acts; eauto.
      by rewrite EINDEX.
    + destruct INw as [X|INw]; [desf|].
      destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
      by unfold is_r in *; rewrite !upds in READ; desf.
      unfold val in *; rewrite !updo; try done.
      eapply NEW_VAL1; try edone.
      { unfolder in INr; desf. }
      { by unfold is_r in *; rewrite updo in READ. }
        by unfold is_w in *; rewrite updo in WRITE.
  * simpl; ins.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    by unfold is_r in *; rewrite upds in READ; desf.
    unfold val; rewrite updo; try done.
    apply NEW_VAL2; try done.
    unfold is_r in *; rewrite updo in READ; try done.
    unfolder in IN. desf.
Qed.

Lemma receptiveness_sim_fence (tid : thread_id)
  s1 s2 (INSTRS0 : instrs s1 = instrs s2)
  (ord : mode) 
  (ISTEP : Some (Instr.fence ord) = nth_error (instrs s1) (pc s1))
  (UPC : pc s2 = pc s1 + 1)
  (UG : G s2 = add (G s1) tid (eindex s1) (Afence ord) ∅ ∅ (ectrl s1) ∅)
  (UINDEX : eindex s2 = eindex s1 + 1)
  (UREGS : regf s2 = regf s1)
  (UDEPS : depf s2 = depf s1)
  (UECTRL : ectrl s2 = ectrl s1)
  MOD (new_rfi : relation actid) new_val
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof using.
red in SIM; desc.

cut (exists instrs pc G_ eindex regf depf ectrl, 
  step tid s1' {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |} /\ 
  (sim_state s2 {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |}
  MOD new_rfi new_val)).
by ins; desc; eauto.

do 7 eexists; splits; red; splits.
  * eexists; red; splits; [by ins; eauto|].
    eexists; splits; [eby rewrite <- INSTRS, <- PC |].
    eapply fence; reflexivity.
  * ins; congruence.
  * ins; congruence.
  * ins.
    destruct (G s2) as [acts2 lab2 rmw2 data2 addr2 ctrl2 rf2 co2].
    inversion UG; subst; clear UG.
    red in EXEC; desc.
    red; splits; ins.
    + by rewrite EINDEX, ACTS.
    + by rewrite TS. 
    + rewrite EINDEX.
      unfold same_lab_u2v in *; intro e.
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1'))).
      { by subst; rewrite !upds. }
      rewrite !updo; auto.
    + rewrite EINDEX.
      destruct (eq_dec_actid a (ThreadEvent tid (eindex s1'))).
      by desf; unfold val; rewrite !upds.
      unfold val; rewrite !updo; [|intro; desf|intro; desf].
      by apply OLD_VAL in NIN; unfold val in NIN; rewrite NIN.
    + by rewrite DATA, EINDEX.
    + by rewrite ADDR, EINDEX.
    + by rewrite CTRL, EINDEX, ECTRL.
    + by rewrite FRMW, EINDEX.
  * ins; congruence.
  * ins; rewrite UREGS, UDEPS.
    unfold RegFun.add, RegFun.find in *; desf; eauto.
  * by ins; rewrite <- DEPF, <- UDEPS.
  * ins; congruence.
  * ins.
    destruct (eq_dec_actid w (ThreadEvent tid (eindex s1'))); subst.
    by unfold is_w in WRITE; rewrite upds in WRITE; desf.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    by unfold is_r in READ; rewrite upds in READ; desf.
    unfold val; rewrite !updo; try done.
    eapply NEW_VAL1; try edone.
    { unfolder in INr; desf. }
    { unfolder in INw; desf. }
    { unfold is_r in *; rewrite updo in READ; try edone. }
    unfold is_w in *; rewrite updo in WRITE; try edone.
  * simpl; ins.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    by unfold is_r in *; rewrite upds in READ; desf.
    unfold val; rewrite updo; try done.
    apply NEW_VAL2; try done.
    unfold is_r in *; rewrite updo in READ; try done.
    unfolder in IN; desf.
Qed.

Lemma receptiveness_sim_cas_fail (tid : thread_id)
  s1 s2 (INSTRS0 : instrs s1 = instrs s2)
  (CASREX : cas_produces_R_ex_instrs (instrs s1))
  (expr_old expr_new : Instr.expr)
  rexmod
  xmod
  (ordr ordw : mode)
  (reg : Reg.t)
  (lexpr : Instr.lexpr)
  (ISTEP : Some (Instr.update (Instr.cas expr_old expr_new) rexmod xmod ordr ordw reg lexpr) =
           nth_error (instrs s1) (pc s1))
  (val_ : value)
  (NEXPECTED : val_ <> RegFile.eval_expr (regf s1) expr_old)
  (UPC : pc s2 = pc s1 + 1)
  (UG : G s2 =
        add (G s1) tid (eindex s1)
            (Aload rexmod ordr (RegFile.eval_lexpr (regf s1) lexpr) val_) 
            ∅ (DepsFile.lexpr_deps (depf s1) lexpr) (ectrl s1)
            (DepsFile.expr_deps (depf s1) expr_old))
  (UINDEX : eindex s2 = eindex s1 + 1)
  (UREGS : regf s2 = RegFun.add reg val_ (regf s1))
  (UDEPS : depf s2 = RegFun.add reg (eq (ThreadEvent tid (eindex s1))) (depf s1))
  (UECTRL : ectrl s2 = ectrl s1)
  MOD (new_rfi : relation actid) new_val
  (NFRMW: MOD ∩₁ dom_rel ((rmw_dep (G s2))) ⊆₁ ∅)
  (NADDR : MOD ∩₁ dom_rel ((addr (G s2))) ⊆₁ ∅)
  (NREX:  MOD ∩₁ (acts_set (G s2)) ∩₁ (R_ex (lab (G s2))) ⊆₁ ∅) 
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
  exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof using.
red in SIM; desc.
assert (rexmod = true); subst.
{ clear -ISTEP CASREX. red in CASREX.
  set (AA:=ISTEP).
  symmetry in AA. apply nth_error_In in AA.
  apply CASREX in AA. red in AA. desf. }

assert (SAME_LOC: RegFile.eval_lexpr (regf s1) lexpr = RegFile.eval_lexpr (regf s1') lexpr).
{ eapply regf_lexpr_helper; eauto.
ins; intro; eapply NADDR; unfolder; splits; eauto.
exists (ThreadEvent tid (eindex s1)).
rewrite UG; unfold add; basic_solver. } 

cut (exists instrs pc G_ eindex regf depf ectrl, 
  step tid s1' {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |} /\ 
  (sim_state s2 {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |}
  MOD new_rfi new_val)).
by ins; desc; eauto.

do 7 eexists; splits; red; splits.
  * eexists; red; splits; [by ins; eauto|].
    eexists; splits; [eby rewrite <- INSTRS, <- PC |].
    eapply cas_un with (val := val_); try reflexivity.
    erewrite <- regf_expr_helper with (regf := (regf s1)); try edone.
    ins; intro;  eapply NFRMW; rewrite UG; unfold add; ins; basic_solver.
  * ins; congruence.
  * ins; congruence.
  * ins.
    destruct (G s2) as [acts2 lab2 rmw2 data2 addr2 ctrl2 rf2 co2].
    inversion UG; subst; clear UG.
    red in EXEC; desc.
    red; splits; ins.
    + by rewrite EINDEX, ACTS.
    + by rewrite TS. 
    + rewrite EINDEX.
      unfold same_lab_u2v in *; intro e.
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1'))).
      { by subst; rewrite !upds; rewrite SAME_LOC. }
      rewrite !updo; auto.
    + rewrite EINDEX.
      destruct (eq_dec_actid a (ThreadEvent tid (eindex s1'))).
      rewrite SAME_LOC.
      by desf; unfold val; rewrite !upds.
      unfold val; rewrite !updo; [|intro; desf|intro; desf].
      by apply OLD_VAL in NIN; unfold val in NIN; rewrite NIN.
    + by rewrite DATA, EINDEX.
    + by rewrite ADDR, EINDEX, DEPF.
    + by rewrite CTRL, EINDEX, ECTRL.
    + by rewrite FRMW, EINDEX, DEPF.
  * ins; congruence.
  * ins; rewrite UREGS, UDEPS.
    unfold RegFun.add, RegFun.find in *; desf; eauto.
  * eby ins; rewrite <- DEPF, <- EINDEX.
  * ins; congruence.
  * ins.
    destruct (eq_dec_actid w (ThreadEvent tid (eindex s1'))); subst.
    by unfold is_w in WRITE; rewrite upds in WRITE; desf.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    + exfalso.
      eapply NREX; split; [eauto|].
      { rewrite UG; unfold add; ins. split; eauto.
        rewrite EINDEX; basic_solver. }
      rewrite UG; unfold add; unfold R_ex; ins.
        by rewrite EINDEX, upds.
    + unfold val; rewrite !updo; try done.
      eapply NEW_VAL1; try edone.
      { unfolder in INr. desf. }
      { unfolder in INw. desf. }
      { unfold is_r in *; rewrite updo in READ; try edone. }
      unfold is_w in *; rewrite updo in WRITE; try edone.
  * simpl; ins.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    + exfalso.
      eapply NREX; split; [eauto|].
      { rewrite UG; unfold add; ins. split; eauto.
        rewrite EINDEX; basic_solver. }
      rewrite UG; unfold add; unfold R_ex; ins.
      by rewrite EINDEX, upds.
    + unfold val; rewrite updo; try done.
      apply NEW_VAL2; try done.
      unfold is_r in *; rewrite updo in READ; try done.
      unfolder in IN. desf.
Qed.

Lemma receptiveness_sim_cas_suc (tid : thread_id)
  s1 s2 (INSTRS0 : instrs s1 = instrs s2)
  (CASREX : cas_produces_R_ex_instrs (instrs s1))
  (expr_old expr_new : Instr.expr)
  rexmod xmod
  (ordr ordw : mode)
  (reg : Reg.t)
  (lexpr : Instr.lexpr)
  (ISTEP : Some (Instr.update (Instr.cas expr_old expr_new) rexmod xmod ordr ordw reg lexpr) =
           nth_error (instrs s1) (pc s1))
  (UPC : pc s2 = pc s1 + 1)
  (UG : G s2 =
        add_rmw (G s1) tid (eindex s1)
                (Aload rexmod ordr (RegFile.eval_lexpr (regf s1) lexpr)
                       (RegFile.eval_expr (regf s1) expr_old))
                (Astore xmod ordw (RegFile.eval_lexpr (regf s1) lexpr)
                        (RegFile.eval_expr (regf s1) expr_new))
                (DepsFile.expr_deps (depf s1) expr_new)
                (DepsFile.lexpr_deps (depf s1) lexpr) (ectrl s1)
                (DepsFile.expr_deps (depf s1) expr_old))
  (UINDEX : eindex s2 = eindex s1 + 2)
  (UREGS : regf s2 = RegFun.add reg (RegFile.eval_expr (regf s1) expr_old) (regf s1))
  (UDEPS : depf s2 = RegFun.add reg (eq (ThreadEvent tid (eindex s1))) (depf s1))
  (UECTRL : ectrl s2 = ectrl s1)
  MOD (new_rfi : relation actid) new_val
  (NFRMW: MOD ∩₁ dom_rel ((rmw_dep (G s2))) ⊆₁ ∅)
  (NADDR : MOD ∩₁ dom_rel ((addr (G s2))) ⊆₁ ∅)
  (NREX:  MOD ∩₁ (acts_set (G s2)) ∩₁ (R_ex (lab (G s2))) ⊆₁ ∅) 
  (NDATA: ⦗MOD⦘ ⨾ (data (G s2)) ⨾ ⦗set_compl MOD⦘ ⊆ ∅₂)
  (RFI_INDEX : new_rfi ⊆ ext_sb)
  (TWF : thread_wf tid s1)
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
  exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof using.
red in SIM; desc.

assert (rexmod = true); subst.
{ clear -ISTEP CASREX. red in CASREX.
  set (AA:=ISTEP).
  symmetry in AA. apply nth_error_In in AA.
  apply CASREX in AA. red in AA. desf. }

assert (SAME_LOC: RegFile.eval_lexpr (regf s1) lexpr = RegFile.eval_lexpr (regf s1') lexpr).
{ ins; eapply regf_lexpr_helper; eauto.
ins; intro; eapply NADDR; unfolder; splits; eauto.
exists (ThreadEvent tid (eindex s1)).
rewrite UG; unfold add_rmw; basic_solver. } 

cut (exists instrs pc G_ eindex regf depf ectrl, 
  step tid s1' {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |} /\ 
  (sim_state s2 {| instrs := instrs; pc := pc; G := G_; eindex := eindex; regf := regf; depf := depf; ectrl := ectrl |}
  MOD new_rfi new_val)).
by ins; desc; eauto.

do 7 eexists; splits; red; splits.
  * eexists; red; splits; [by ins; eauto|].
    eexists; splits; [eby rewrite <- INSTRS, <- PC |].
    eapply cas_suc; try reflexivity.
  * ins; congruence.
  * ins; congruence.
  * ins.
    destruct (G s2) as [acts2 lab2 rmw2 data2 addr2 ctrl2 rf2 co2].
    inversion UG; subst; clear UG; ins.
    unfold acts_set, R_ex in NREX; ins.
    red in EXEC; desc.
    red; splits; ins.
    + by rewrite EINDEX, ACTS.
    + by rewrite TS. 
    + rewrite EINDEX.
      unfold same_lab_u2v in *; intro e.
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1' + 1))).
      by subst; rewrite !upds; rewrite SAME_LOC.
      rewrite updo; try done.
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1'))).
      by subst; rewrite !upds; rewrite updo; [| by desf]; rewrite upds; rewrite SAME_LOC.
      rewrite !updo; auto.
    + rewrite EINDEX.
      destruct (eq_dec_actid a (ThreadEvent tid (eindex s1' + 1))).
      -- subst; rewrite SAME_LOC.
         unfold val; rewrite !upds.
         erewrite regf_expr_helper; try edone.
         intro reg0; specialize (REGF reg0); desf; eauto.
         ins; intro DEPS; eapply NDATA; unfolder; splits; eauto.
         by rewrite EINDEX.
      -- unfold val; rewrite updo; [|done].
         destruct (eq_dec_actid a (ThreadEvent tid (eindex s1'))).
         ** subst; rewrite SAME_LOC.
            rewrite !upds.
            rewrite updo; [|intro; desf; lia].
            rewrite !upds.
            erewrite regf_expr_helper; try edone.
            intro reg0; specialize (REGF reg0); desf; eauto.
            ins; intro DEPS; eapply NFRMW; unfolder; splits; eauto.
         ** rewrite !updo; try done.
            by apply OLD_VAL in NIN; unfold val in NIN; rewrite NIN.
    + by rewrite RMW, EINDEX.
    + by rewrite DATA, EINDEX, DEPF.
    + by rewrite ADDR, EINDEX, DEPF.
    + by rewrite CTRL, EINDEX, ECTRL.
    + by rewrite FRMW, EINDEX, DEPF.
  * ins; congruence.
  * ins; rewrite UREGS, UDEPS.
    unfold RegFun.add, RegFun.find in *; desf; eauto.
    erewrite regf_expr_helper; eauto.
    ins; intro; eapply NFRMW.
    rewrite UG; ins; basic_solver.
  * eby ins; rewrite <- DEPF, <- EINDEX.
  * ins; congruence.
  * ins; unfold acts_set, is_r, is_w in INr, INw, READ, WRITE; ins.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'+1))); subst.
    by rewrite upds in READ; desf.
    destruct (eq_dec_actid w (ThreadEvent tid (eindex s1'))); subst.
    rewrite updo in WRITE; [| intro; desf; lia].
    by rewrite upds in WRITE; desf.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    + exfalso.
      eapply NREX; split; [eauto|].
      { rewrite UG; unfold add; ins. split; eauto.
        rewrite EINDEX; basic_solver. }
      rewrite UG; unfold add; unfold R_ex; ins.
      by rewrite updo; [| intro; desf; lia]; rewrite EINDEX, upds.
    + unfold val; rewrite updo; [|done].
      rewrite updo; [|done].
      destruct (eq_dec_actid w (ThreadEvent tid (eindex s1'+1))); subst.
      -- exfalso.
         apply RFI_INDEX in RF; unfold ext_sb in RF.
         destruct r; [eauto|]; desc.
         destruct INr as [[X|X]|INr]; try by desf.
         apply sim_execution_same_acts in EXEC.
         apply EXEC in INr.
         apply TWF in INr; desc.
         rewrite <- EINDEX in RF0.
         desf; lia.
      -- rewrite !updo; try done.
         eapply NEW_VAL1; try edone.
         { unfolder in INr; desf. }
         { unfolder in INw; desf. }
         { by rewrite !updo in READ; try edone. }
           by rewrite !updo in WRITE; try edone.
  * simpl; ins.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'+1))); subst.
    by unfold is_r in READ; rewrite upds in READ; desf.
    unfold val; rewrite updo; [|done].
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    + exfalso.
      eapply NREX; split; [eauto|].
      { rewrite UG; unfold add; unfold acts_set; ins. split; eauto.
        rewrite EINDEX; basic_solver. }
      rewrite UG; unfold add; unfold R_ex; ins.
      by rewrite updo; [| intro; desf; lia]; rewrite EINDEX, upds.
    + unfold val; rewrite updo; try done.
      apply NEW_VAL2; try done.
      unfold is_r in *; rewrite !updo in READ; try done.
      unfolder in IN; desf.
Qed.

Lemma receptiveness_sim_inc (tid : thread_id)
      s1 s2 (INSTRS0 : instrs s1 = instrs s2)
      (expr_add : Instr.expr)
      rexmod xmod
      (ordr ordw : mode)
      (reg : Reg.t)
      (lexpr : Instr.lexpr)
      (ISTEP : Some (Instr.update
                       (Instr.fetch_add expr_add) rexmod xmod ordr ordw reg lexpr) =
               nth_error (instrs s1) (pc s1))
      (val_ : nat)
      (UPC : pc s2 = pc s1 + 1)
      (UG : G s2 =
            add_rmw (G s1) tid (eindex s1)
                    (Aload rexmod ordr
                           (RegFile.eval_lexpr (regf s1) lexpr) val_)
                    (Astore xmod ordw (RegFile.eval_lexpr (regf s1) lexpr)
                            (val_ + RegFile.eval_expr (regf s1) expr_add))
                    ((eq (ThreadEvent tid (eindex s1))) ∪₁
                     (DepsFile.expr_deps (depf s1) expr_add))
                    (DepsFile.lexpr_deps (depf s1) lexpr)
                    (ectrl s1) ∅)
      (UINDEX : eindex s2 = eindex s1 + 2)
      (UREGS : regf s2 = RegFun.add reg val_ (regf s1))
      (UDEPS : depf s2 = RegFun.add reg (eq (ThreadEvent tid (eindex s1))) (depf s1))
      (UECTRL : ectrl s2 = ectrl s1)
      MOD (new_rfi : relation actid) new_val
      (NFRMW: MOD ∩₁ dom_rel ((rmw_dep (G s2))) ⊆₁ ∅)
      (NADDR : MOD ∩₁ dom_rel ((addr (G s2))) ⊆₁ ∅)
      (NREX:  MOD ∩₁ (acts_set (G s2)) ∩₁ (R_ex (lab (G s2))) ⊆₁ ∅) 
      (NDATA: ⦗MOD⦘ ⨾ (data (G s2)) ⨾ ⦗set_compl MOD⦘ ⊆ ∅₂)
      (TWF : thread_wf tid s1)
      (RFI_INDEX : new_rfi ⊆ ext_sb)
      (new_rfif : functional new_rfi⁻¹)
      s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof using.
  generalize (@new_write new_rfi new_rfif); intro F; destruct F as [new_w F].
  red in SIM; desc.
  assert (SAME_LOC : RegFile.eval_lexpr (regf s1) lexpr =
                     RegFile.eval_lexpr (regf s1') lexpr).
  { ins; eapply regf_lexpr_helper; eauto.
    ins; intro; eapply NADDR; unfolder; splits; eauto.
    exists (ThreadEvent tid (eindex s1)).
    rewrite UG; unfold add_rmw; basic_solver. } 

  cut (exists instrs pc G_ eindex regf depf ectrl, 
          step tid s1' (Build_state instrs pc G_ eindex regf depf ectrl) /\ 
          (sim_state s2 (Build_state instrs pc G_ eindex regf depf ectrl)
                     MOD new_rfi new_val)).
  { ins; desc; eauto. }
  do 7 eexists; splits; red; splits.
  { eexists; red; splits; [by ins; eauto|].
    eexists; splits; [eby rewrite <- INSTRS, <- PC |].
    eapply inc with (val := 
      if excluded_middle_informative (MOD (ThreadEvent tid (eindex s1'))) 
      then if excluded_middle_informative ((codom_rel new_rfi) (ThreadEvent tid (eindex s1'))) 
           then (get_val (val (lab (G s1')) (new_w (ThreadEvent tid (eindex s1')))))
           else (new_val (ThreadEvent tid (eindex s1')))
      else val_);
    reflexivity. }
  1,2,4,7: ins; congruence.
  { ins.
    destruct (G s2) as [acts2 lab2 rmw2 data2 addr2 ctrl2 rf2 co2].
    inversion UG; subst; clear UG.
    red in EXEC; desc.
    red; splits; ins.
    { by rewrite EINDEX, ACTS. }
    {  by rewrite TS. }
    { rewrite EINDEX.
      unfold same_lab_u2v in *; intro e.
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1'))).
      { subst.
        rewrite updo; [|intros HH; clear -HH; inv HH; lia]. 
        rewrite !upds. unfold same_label_u2v.
        rewrite updo; [|intros HH; clear -HH; inv HH; lia]. 
        rewrite upds; auto. }
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1' + 1))).
      { subst.
        rewrite !upds. unfold same_label_u2v; auto. }
      ins. rewrite !updo; auto. }
    { rewrite EINDEX.
      unfold val.
      destruct (eq_dec_actid a (ThreadEvent tid (eindex s1' + 1))).
      { subst.
        destruct (excluded_middle_informative (MOD (ThreadEvent tid (eindex s1')))) as [MN|NMN].
        { exfalso.
          eapply NDATA. 
          apply seq_eqv_lr. splits; eauto.
          basic_solver 10. }
        assert (SAME_VAL : RegFile.eval_expr (regf s1 ) expr_add =
                           RegFile.eval_expr (regf s1') expr_add).
        { ins; eapply regf_expr_helper; eauto.
          ins; intro; eapply NDATA; unfolder; splits; eauto.
            by rewrite EINDEX. }
        rewrite !upds. by rewrite SAME_VAL. }
      rewrite updo; auto.
      destruct (eq_dec_actid a (ThreadEvent tid (eindex s1'))).
      { subst.
        rewrite !upds.
        destruct (excluded_middle_informative (MOD (ThreadEvent tid (eindex s1')))) as [MN|NMN].
        { exfalso. eauto. }
        rewrite updo; [|intros HH; clear -HH; inv HH; lia]. 
          by rewrite upds. }
      rewrite !updo; auto.
      by apply OLD_VAL in NIN; unfold val in NIN; rewrite NIN. }
    { by rewrite RMW, EINDEX. }
    { by rewrite DATA, EINDEX, DEPF. }
    { by rewrite ADDR, EINDEX, DEPF. }
    { by rewrite CTRL, EINDEX, ECTRL. }
      by rewrite FRMW, EINDEX. }
  { ins; rewrite UREGS, UDEPS.
    unfold RegFun.add, RegFun.find in *; desf; eauto. }
  { eby ins; rewrite <- DEPF, <- EINDEX. }
  { ins; unfold acts_set, is_r, is_w in INr, INw, READ, WRITE; ins.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'+1))); subst.
    { by rewrite upds in READ; desf. }
    destruct (eq_dec_actid w (ThreadEvent tid (eindex s1'))); subst.
    rewrite updo in WRITE; [| intro; desf; lia].
    { by rewrite upds in WRITE; desf. }

    destruct (eq_dec_actid w (ThreadEvent tid (eindex s1' + 1))); subst.
    { exfalso.
      apply RFI_INDEX in RF; unfold ext_sb in RF.
      destruct INr as [[INr|INr]|INr]; subst.
      1,2: clear -RF; lia.
      destruct r; [eauto|]; desc.
      apply sim_execution_same_acts in EXEC.
      apply EXEC in INr.
      apply TWF in INr; desc.
      rewrite <- EINDEX in RF0.
      inv EE. clear -RF0 LT. lia. }

    assert (is_w (lab (G s1')) w) as WW'.
    { rewrite !updo in WRITE; edone. }

    unfold val.
    rewrite updo; auto.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    { rewrite !upds.
      destruct (excluded_middle_informative (MOD (ThreadEvent tid (eindex s1')))) as [MN|NMN].
      2: eby exfalso.
      rewrite !updo; auto.
      destruct (excluded_middle_informative
                  (codom_rel new_rfi (ThreadEvent tid (eindex s1')))) as [|XX].
      2: { exfalso. apply XX. generalize RF. clear. basic_solver. }
      assert (w = new_w (ThreadEvent tid (eindex s1'))); subst.
      { edestruct new_rfi_unique with
            (r:=ThreadEvent tid (eindex s1')) as [wu [_ HH]]; eauto.
        transitivity wu.
        2: by apply HH.
        symmetry. apply HH. do 2 red. generalize RF. clear. basic_solver. }
      unfold get_val.
      clear -WW'. unfold is_w in WW'. desf. }
    rewrite !updo; auto.
    eapply NEW_VAL1; try edone.
    { unfolder in INr; desf. }
    { unfolder in INw; desf. }
      by rewrite !updo in READ; try edone. }
  simpl; ins.
  destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'+1))); subst.
  { by unfold is_r in READ; rewrite upds in READ; desf. }
  unfold val; rewrite updo; [|done].
  destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
  { rewrite upds. desf. }
  unfold val; rewrite updo; try done.
  apply NEW_VAL2; try done.
  unfold is_r in *; rewrite !updo in READ; try done.
  unfolder in IN; desf.
Qed.

Lemma receptiveness_sim_exchange
      (tid : thread_id)
      s1 s2 (INSTRS0 : instrs s1 = instrs s2)
      (new_expr : Instr.expr)
      rexmod xmod
      (ordr ordw : mode)
      (reg : Reg.t)
      (lexpr : Instr.lexpr)
      (ISTEP : Some (Instr.update
                       (Instr.exchange new_expr)
                       rexmod xmod ordr ordw reg lexpr) = nth_error (instrs s1) (pc s1))
      (val_ : nat)
      (UPC : pc s2 = pc s1 + 1)
      (UG : G s2 = add_rmw (G s1) tid (eindex s1)
                           (Aload rexmod ordr (RegFile.eval_lexpr (regf s1) lexpr)
                                  val_)
                           (Astore xmod ordw (RegFile.eval_lexpr (regf s1) lexpr)
                                   (RegFile.eval_expr (regf s1) new_expr))
                           (DepsFile.expr_deps (depf s1) new_expr)
                           (DepsFile.lexpr_deps (depf s1) lexpr)
                           (ectrl s1) ∅)
      (UINDEX : eindex s2 = eindex s1 + 2)
      (UREGS : regf s2 = RegFun.add reg val_ (regf s1))
      (UDEPS : depf s2 = RegFun.add reg (eq (ThreadEvent tid (eindex s1)))
                                    (depf s1))
      (UECTRL : ectrl s2 = ectrl s1)
      MOD (new_rfi : relation actid) new_val
      (NFRMW: MOD ∩₁ dom_rel ((rmw_dep (G s2))) ⊆₁ ∅)
      (NADDR : MOD ∩₁ dom_rel ((addr (G s2))) ⊆₁ ∅)
      (NREX:  MOD ∩₁ (acts_set (G s2)) ∩₁ (R_ex (lab (G s2))) ⊆₁ ∅) 
      (NDATA: ⦗MOD⦘ ⨾ (data (G s2)) ⨾ ⦗set_compl MOD⦘ ⊆ ∅₂)
      (TWF : thread_wf tid s1)
      (RFI_INDEX : new_rfi ⊆ ext_sb)
      (new_rfif : functional new_rfi⁻¹)
      s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
  exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof using.
  generalize (@new_write new_rfi new_rfif); intro F; destruct F as [new_w F].
  red in SIM; desc.
  assert (SAME_LOC : RegFile.eval_lexpr (regf s1) lexpr =
                     RegFile.eval_lexpr (regf s1') lexpr).
  { ins; eapply regf_lexpr_helper; eauto.
    ins; intro; eapply NADDR; unfolder; splits; eauto.
    exists (ThreadEvent tid (eindex s1)).
    rewrite UG; unfold add_rmw; basic_solver. } 

  cut (exists instrs pc G_ eindex regf depf ectrl, 
          step tid s1' (Build_state instrs pc G_ eindex regf depf ectrl) /\ 
          (sim_state s2 (Build_state instrs pc G_ eindex regf depf ectrl)
                     MOD new_rfi new_val)).
  { ins; desc; eauto. }
  do 7 eexists; splits; red; splits.
  { eexists; red; splits; [by ins; eauto|].
    eexists; splits; [eby rewrite <- INSTRS, <- PC |].
    eapply exchange with (val :=
      if excluded_middle_informative (MOD (ThreadEvent tid (eindex s1')))
      then if excluded_middle_informative ((codom_rel new_rfi) (ThreadEvent tid (eindex s1')))
           then (get_val (val (lab (G s1')) (new_w (ThreadEvent tid (eindex s1')))))
           else (new_val (ThreadEvent tid (eindex s1')))
      else val_);
    reflexivity. }
  1,2,4,7: ins; congruence.
  { ins.
    destruct (G s2) as [acts2 lab2 rmw2 data2 addr2 ctrl2 rf2 co2].
    inversion UG; subst; clear UG.
    red in EXEC; desc.
    red; splits; ins.
    { by rewrite EINDEX, ACTS. }
    { by rewrite TS. }
    { rewrite EINDEX.
      unfold same_lab_u2v in *; intro e.
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1'))).
      { subst.
        rewrite updo; [|intros HH; clear -HH; inv HH; lia]. 
        rewrite !upds. unfold same_label_u2v.
        rewrite updo; [|intros HH; clear -HH; inv HH; lia]. 
        rewrite upds; auto. }
      destruct (eq_dec_actid e (ThreadEvent tid (eindex s1' + 1))).
      { subst.
        rewrite !upds. unfold same_label_u2v; auto. }
      ins. rewrite !updo; auto. }
    { rewrite EINDEX.
      destruct (eq_dec_actid a (ThreadEvent tid (eindex s1' + 1))).
      { subst; rewrite SAME_LOC.
        unfold val; rewrite !upds.
        erewrite regf_expr_helper; try edone.
        intro reg0; specialize (REGF reg0); desf; eauto.
        ins; intro DEPS; eapply NDATA; unfolder; splits; eauto.
        by rewrite EINDEX. } 
      unfold val; rewrite updo; [|done].
      destruct (eq_dec_actid a (ThreadEvent tid (eindex s1'))).
      { subst; rewrite SAME_LOC.
         rewrite !upds.
         rewrite updo; [|intro; desf; lia].
         rewrite !upds. desf. }
      rewrite !updo; try done.
      by apply OLD_VAL in NIN; unfold val in NIN; rewrite NIN. }
    { by rewrite RMW, EINDEX. }
    { by rewrite DATA, EINDEX, DEPF. }
    { by rewrite ADDR, EINDEX, DEPF. }
    { by rewrite CTRL, EINDEX, ECTRL. }
      by rewrite FRMW, EINDEX. }
  { ins; rewrite UREGS, UDEPS.
    unfold RegFun.add, RegFun.find in *; desf; eauto. }
  { eby ins; rewrite <- DEPF, <- EINDEX. }
  { ins; unfold acts_set, is_r, is_w in INr, INw, READ, WRITE; ins.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'+1))); subst.
    { by rewrite upds in READ; desf. }
    destruct (eq_dec_actid w (ThreadEvent tid (eindex s1'))); subst.
    rewrite updo in WRITE; [| intro; desf; lia].
    { by rewrite upds in WRITE; desf. }

    destruct (eq_dec_actid w (ThreadEvent tid (eindex s1' + 1))); subst.
    { exfalso.
      apply RFI_INDEX in RF; unfold ext_sb in RF.
      destruct INr as [[INr|INr]|INr]; subst.
      1,2: clear -RF; lia.
      destruct r; [eauto|]; desc.
      apply sim_execution_same_acts in EXEC.
      apply EXEC in INr.
      apply TWF in INr; desc.
      rewrite <- EINDEX in RF0.
      inv EE. clear -RF0 LT. lia. }

    assert (is_w (lab (G s1')) w) as WW'.
    { rewrite !updo in WRITE; edone. }

    unfold val.
    rewrite updo; auto.
    destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
    { rewrite !upds.
      destruct (excluded_middle_informative (MOD (ThreadEvent tid (eindex s1')))) as [MN|NMN].
      2: eby exfalso.
      rewrite !updo; auto.
      destruct (excluded_middle_informative
                  (codom_rel new_rfi (ThreadEvent tid (eindex s1')))) as [|XX].
      2: { exfalso. apply XX. generalize RF. clear. basic_solver. }
      assert (w = new_w (ThreadEvent tid (eindex s1'))); subst.
      { edestruct new_rfi_unique with
            (r:=ThreadEvent tid (eindex s1')) as [wu [_ HH]]; eauto.
        transitivity wu.
        2: by apply HH.
        symmetry. apply HH. do 2 red. generalize RF. clear. basic_solver. }
      unfold get_val.
      clear -WW'. unfold is_w in WW'. desf. }
    rewrite !updo; auto.
    eapply NEW_VAL1; try edone.
    { unfolder in INr; desf. }
    { unfolder in INw; desf. }
      by rewrite !updo in READ; try edone. }
  simpl; ins.
  destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'+1))); subst.
  { by unfold is_r in READ; rewrite upds in READ; desf. }
  unfold val; rewrite updo; [|done].
  destruct (eq_dec_actid r (ThreadEvent tid (eindex s1'))); subst.
  { rewrite upds. desf. }
  unfold val; rewrite updo; try done.
  apply NEW_VAL2; try done.
  { unfold is_r in *; rewrite !updo in READ; done. }
  unfolder in IN; desf.
Qed.

Lemma receptiveness_sim_step (tid : thread_id)
  s1 s2
  (STEP : (step tid) s1 s2) 
  (CASREX : cas_produces_R_ex_instrs (instrs s1))
  MOD (new_rfi : relation actid) new_val
  (NCTRL : MOD ∩₁ ectrl s2 ⊆₁ ∅)
  (NFRMW: MOD ∩₁ dom_rel ((rmw_dep (G s2))) ⊆₁ ∅)
  (NADDR : MOD ∩₁ dom_rel ((addr (G s2))) ⊆₁ ∅)
  (NREX:  MOD ∩₁ (acts_set (G s2)) ∩₁ (R_ex (lab (G s2))) ⊆₁ ∅) 
  (NDATA: ⦗MOD⦘ ⨾ (data (G s2)) ⨾ ⦗set_compl MOD⦘ ⊆ ∅₂)
  (new_rfif : functional new_rfi⁻¹)
   (RFI_INDEX : new_rfi ⊆ ext_sb)
  (TWF : thread_wf tid s1)
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid) s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof using.
destruct STEP; red in H; desf.
destruct ISTEP0; desf.
- eby eapply receptiveness_sim_assign.
- eby eapply receptiveness_sim_if_else.
- eby eapply receptiveness_sim_if_then.
- eby eapply receptiveness_sim_load.
- eby eapply receptiveness_sim_store.
- eby eapply receptiveness_sim_fence.
- eby eapply receptiveness_sim_cas_fail.
- eby eapply receptiveness_sim_cas_suc.
- eby eapply receptiveness_sim_inc.
- eby eapply receptiveness_sim_exchange. 
Qed.

Lemma receptiveness_sim (tid : thread_id)
  s1 s2
  (STEPS : (step tid)＊ s1 s2)
  (CASREX : cas_produces_R_ex_instrs (instrs s1))
  MOD (new_rfi : relation actid) new_val
  (NCTRL : MOD ∩₁ ectrl s2 ⊆₁ ∅)
  (NFRMW: MOD ∩₁ dom_rel ((rmw_dep (G s2))) ⊆₁ ∅)
  (NADDR : MOD ∩₁ dom_rel ((addr (G s2))) ⊆₁ ∅)
  (NREX:  MOD ∩₁ (acts_set (G s2)) ∩₁ (R_ex (lab (G s2))) ⊆₁ ∅) 
  (NDATA: ⦗MOD⦘ ⨾ (data (G s2)) ⨾ ⦗set_compl MOD⦘ ⊆ ∅₂)
  (new_rfif : functional new_rfi⁻¹)
   (RFI_INDEX : new_rfi ⊆ ext_sb)
  (TWF : thread_wf tid s1)
  s1' (SIM: sim_state s1 s1' MOD new_rfi new_val) :
 exists s2', (step tid)＊ s1' s2' /\ sim_state s2 s2' MOD new_rfi new_val.
Proof using.
  apply clos_rt_rtn1 in STEPS.
  induction STEPS.
  { by eexists; vauto. }
  exploit IHSTEPS.
  { unfolder; splits; ins; eauto; desf.
    eapply ectrl_increasing in H1; eauto.
    eapply NCTRL; basic_solver. }
  { unfolder; splits; ins; eauto; desf.
    eapply rmw_dep_increasing in H1; eauto.
    eapply NFRMW; basic_solver. }
  { unfolder; splits; ins; eauto; desf.
    eapply addr_increasing in H1; eauto.
    eapply NADDR; basic_solver. }
  { unfolder; splits; ins; eauto; desf. 
    eapply NREX; split; [split; [eauto |] |].
    eapply acts_increasing; edone.
    eapply is_r_ex_increasing; eauto.
    eapply thread_wf_steps; try edone. 
    { by apply clos_rtn1_rt. }
    basic_solver. }
  { unfolder; splits; ins; eauto; desf.
    eapply data_increasing in H1; eauto.
    eapply NDATA; basic_solver. }
  intro; desc.
  eapply receptiveness_sim_step in x0; eauto; desf.
  { exists s2'0; splits; eauto. 
      by eapply rt_trans; [eauto | econs]. }
  { arewrite (instrs y = instrs s1); auto.
    apply clos_rtn1_rt in STEPS.
    eapply steps_preserve_instrs; eauto. }
  eapply thread_wf_steps; try edone.
    by apply clos_rtn1_rt.
Qed.

Lemma receptiveness_helper (tid : thread_id)
      s_init s
      (CASREX : cas_produces_R_ex_instrs (instrs s_init))
      (GPC : wf_thread_state tid s_init)
      (new_val : actid -> value)
      (new_rfi : relation actid)
      (MOD: actid -> Prop)
      (STEPS : (step tid)＊ s_init s)
      (new_rfiE : new_rfi ≡ ⦗(acts_set (G s))⦘ ⨾ new_rfi ⨾ ⦗(acts_set (G s))⦘)
      (new_rfiD : new_rfi ≡ ⦗is_w (lab (G s))⦘ ⨾ new_rfi ⨾ ⦗is_r (lab (G s))⦘)
      (new_rfif : functional new_rfi⁻¹)
      (RFI_INDEX : new_rfi ⊆ ext_sb)
      (NCTRL : MOD ∩₁ ectrl s ⊆₁ ∅) 
      (NFRMW: MOD ∩₁ dom_rel ((rmw_dep (G s))) ⊆₁ ∅)
      (NADDR : MOD ∩₁ dom_rel ((addr (G s))) ⊆₁ ∅)
      (NREX:  MOD ∩₁ (acts_set (G s)) ∩₁ (R_ex (lab (G s))) ⊆₁ ∅) 
      (NDATA: ⦗MOD⦘ ⨾ (data (G s)) ⨾ ⦗set_compl MOD⦘ ⊆ ∅₂) 
      (new_rfiMOD : codom_rel new_rfi ⊆₁ MOD)
      (NMODINIT: MOD ∩₁ (acts_set (ProgToExecution.G s_init)) ⊆₁ ∅)
      (EMOD : MOD ⊆₁ (acts_set (ProgToExecution.G s))) :
    exists s',
      ⟪ STEPS' : (step tid)＊ s_init s' ⟫ /\
      ⟪ EXEC : sim_execution (G s) (G s') MOD ⟫ /\
      ⟪ NEW_VAL1 : forall r w (RF: new_rfi w r), val ((lab (G s'))) r = val ((lab (G s'))) w ⟫ /\
      ⟪ NEW_VAL2 : forall r (RR : is_r (lab (G s')) r) (IN: MOD r) (NIN: ~ (codom_rel new_rfi) r),
          val ((lab (G s'))) r = Some (new_val r) ⟫ /\
      ⟪ OLD_VAL : forall a (NIN: ~ MOD a), val ((lab (G s'))) a = val ((lab (G s))) a ⟫.
Proof using.
apply receptiveness_sim with (s1':= s_init) (MOD:=MOD) (new_rfi:=new_rfi) (new_val:=new_val) in STEPS.
all: try done.
- desc.
  red in STEPS0; desc.
  exists s2'; splits; eauto.
  * ins; eapply NEW_VAL1; try done.
    + hahn_rewrite new_rfiE in RF; unfolder in RF; desf.
      apply sim_execution_same_acts in EXEC.
      revert EXEC; basic_solver.
    + hahn_rewrite new_rfiE in RF; unfolder in RF; desf.
      apply sim_execution_same_acts in EXEC.
      revert EXEC; basic_solver.
    + hahn_rewrite new_rfiD in RF; unfolder in RF; desf.
      apply sim_execution_same_r in EXEC.
      revert EXEC; basic_solver.
    + hahn_rewrite new_rfiD in RF; unfolder in RF; desf.
      apply sim_execution_same_w in EXEC.
      revert EXEC; basic_solver.
    + revert new_rfiMOD; basic_solver.
  * ins; eapply NEW_VAL2; try done.
    apply sim_execution_same_acts in EXEC.
    revert EXEC; basic_solver.
  * ins; red in EXEC; desc.
    by eapply OLD_VAL.
- red; apply (acts_rep GPC).
- red; splits; eauto.
  { red; splits; eauto; red; red; ins; red; eauto; desf. }
  ins; exfalso; revert NMODINIT; basic_solver.
  ins; exfalso; unfolder in *; basic_solver.
Qed.

Lemma receptiveness_ectrl_helper (tid : thread_id) 
      s_init s 
      (GPC : wf_thread_state tid s_init)
      (STEPS : (step tid)＊ s_init s)
      MOD (NCTRL: MOD ∩₁ dom_rel ((ctrl (G s))) ⊆₁ ∅) 
      (NMODINIT: MOD ∩₁ (acts_set (G s_init)) ⊆₁ ∅):
      exists s', (step tid)＊ s_init s' /\
                 (MOD ∩₁ ectrl s' ⊆₁ ∅) /\ (G s') = (G s).
Proof using.
apply clos_rt_rtn1 in STEPS.
induction STEPS.
- exists s_init; splits; vauto.
  by rewrite (wft_ectrlE GPC).
- assert (A: MOD ∩₁ dom_rel (ctrl (G y)) ⊆₁ ∅).
  generalize (ctrl_increasing H).
  revert NCTRL; basic_solver 12.
  apply IHSTEPS in A.
  desc.
  destruct  (classic (MOD ∩₁ ectrl z ⊆₁ ∅)).
  * exists z; splits; eauto.
    eapply rt_trans.
    eby apply clos_rtn1_rt.
    by apply rt_step.
  * exists s'; splits; eauto.
    transitivity (G y); [done|].
    eapply ectrl_ctrl_step; try edone.
    destruct (classic (exists a : actid, (MOD ∩₁ ectrl z) a)); auto.
    exfalso; apply H0; unfolder; ins; eapply H1; basic_solver.
Qed.

Lemma receptiveness_full (tid : thread_id)
      s_init s
      (new_val : actid -> value)
      (new_rfi : relation actid)
      (MOD: actid -> Prop)
      (GPC : wf_thread_state tid s_init)
      (CASREX : cas_produces_R_ex_instrs (instrs s_init))
      (STEPS : (step tid)＊ s_init s)
      (new_rfiE : new_rfi ≡ ⦗(acts_set (G s))⦘ ⨾ new_rfi ⨾ ⦗(acts_set (G s))⦘)
      (new_rfiD : new_rfi ≡ ⦗is_w (lab (G s))⦘ ⨾ new_rfi ⨾ ⦗is_r (lab (G s))⦘)
      (new_rfif : functional new_rfi⁻¹)
      (RFI_INDEX : new_rfi ⊆ ext_sb)
      (new_rfiMOD : codom_rel new_rfi ⊆₁ MOD)
      (EMOD : MOD ⊆₁ (acts_set (ProgToExecution.G s)))
      (NMODINIT: MOD ∩₁ (acts_set (ProgToExecution.G s_init)) ⊆₁ ∅)
      (NFRMW: MOD ∩₁ dom_rel ((rmw_dep (G s))) ⊆₁ ∅)
      (NADDR : MOD ∩₁ dom_rel ((addr (G s))) ⊆₁ ∅)
      (NREX:  MOD ∩₁ (acts_set (G s)) ∩₁(R_ex (lab (G s))) ⊆₁ ∅) 
      (NCTRL: MOD ∩₁ dom_rel ((ctrl (G s))) ⊆₁ ∅)
      (NDATA: ⦗MOD⦘ ⨾ (data (G s)) ⨾ ⦗set_compl MOD⦘ ⊆ ∅₂) :
    exists s',
      ⟪ STEPS' : (step tid)＊ s_init s' ⟫ /\
      ⟪ RACTS : (acts_set (G s)) = (acts_set (G s')) ⟫ /\
      ⟪ RTS: threads_set (G s) ≡₁ threads_set (G s')⟫ /\
      ⟪ RRMW  : (rmw (G s))  ≡ (rmw (G s'))  ⟫ /\
      ⟪ RDATA : (data (G s)) ≡ (data (G s')) ⟫ /\
      ⟪ RADDR : (addr (G s)) ≡ (addr (G s')) ⟫ /\
      ⟪ RCTRL : (ctrl (G s)) ≡ (ctrl (G s')) ⟫  /\
      ⟪ RFAILRMW : (rmw_dep (G s)) ≡ (rmw_dep (G s')) ⟫  /\
      ⟪ SAME : same_lab_u2v ((lab (G s'))) ((lab (G s)))⟫ /\
      ⟪ NEW_VAL1 : forall r w (RF: new_rfi w r), val ((lab (G s'))) r = val ((lab (G s'))) w ⟫ /\
      ⟪ NEW_VAL2 : forall r (RR : is_r (lab (G s')) r) (IN: MOD r) (NIN: ~ (codom_rel new_rfi) r),
          val ((lab (G s'))) r = Some (new_val r) ⟫ /\
      ⟪ OLD_VAL : forall a (NIN: ~ MOD a), val ((lab (G s'))) a = val ((lab (G s))) a ⟫.
Proof using.
forward (apply receptiveness_ectrl_helper); try edone.

ins; desc.
rewrite <- H1 in *.
clear STEPS H1 s.
forward (eapply receptiveness_helper with (new_rfi:=new_rfi)); ins; eauto.
desc.
red in EXEC; desc.
eexists; splits; eauto.
Qed.
