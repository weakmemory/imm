Require Import PeanoNat.
From PromisingLib Require Import Basic Loc.
Require Import Events.

Set Implicit Arguments.

Module Reg := Ident.
Module RegSet := IdentSet.
Module RegMap := IdentMap.
Module RegFun := IdentFun.

Module Const := Nat.

Module Value.
  Inductive t :=
  | const (const:Const.t)
  | reg (reg:Reg.t)
  .

(*  Definition regs_of (v:t): RegSet.t :=
    match v with
    | reg r => RegSet.singleton r
    | const _ => RegSet.empty
    end.

  Fixpoint regs_of_list (l:list t): RegSet.t :=
    match l with
    | nil => RegSet.empty
    | (reg r)::l => RegSet.add r (regs_of_list l)
    | (const _)::l => regs_of_list l
    end.
*)
End Value.

Module Op1.
  Inductive t :=
  | not
  .

  Definition eval (op:t) (op1:Const.t): Const.t :=
    match op with
    | not =>
      if Const.eq_dec op1 Const.zero
      then Const.one
      else Const.zero
    end.
End Op1.

Module Op2.
  Inductive t :=
  | add
  | sub
  | mul
  .

  Definition eval (op:t): forall (op1 op2:Const.t), Const.t :=
    match op with
    | add => Const.add
    | sub => Const.sub
    | mul => Const.mul
    end.
End Op2.

  (* Definition of_nat (n:nat): t := const n. *)
  (* Definition of_loc (l:Loc.t): t := loc l. *)
(* Coercion Value.reg: Reg.t >-> Value.t. *)
(* Coercion Value.const: Const.t >-> Value.t. *)
(* Coercion Value.of_nat: nat >-> Value.t. *)
(* Coercion Value.of_loc: Loc.t >-> Value.t. *)

Module Instr.
  Inductive expr :=
  | expr_val (val:Value.t)
  | expr_op1 (op:Op1.t) (op:Value.t)
  | expr_op2 (op:Op2.t) (op1 op2:Value.t)
  .

(*
  Definition regs_of_expr (r:expr): RegSet.t :=
    match r with
    | expr_val val => Value.regs_of val
    | expr_op1 _ op => Value.regs_of op
    | expr_op2 _ op1 op2 =>
      RegSet.union (Value.regs_of op1) (Value.regs_of op2)
    end.
*)
  Inductive lexpr :=
  | lexpr_loc    (l:Loc.t)
  | lexpr_choice (r:Value.t) (loc1 loc2:Loc.t)
  .
  
(*  Definition regs_of_lexpr (r:lexpr): RegSet.t :=
    match r with
    | lexpr_loc _ => RegSet.empty
    | lexpr_choice r _ _ => Value.regs_of r
    end.
*)

  Inductive rmw :=
  | fetch_add (addendum:expr)
  | cas (old new:expr)
  .

  Inductive t :=
  | assign (lhs:Reg.t) (rhs:expr)
  | load (ord:mode) (lhs:Reg.t) (loc:lexpr)
  | store (ord:mode) (loc:lexpr) (val:expr)
  | update (rmw:rmw) (xmod:x_mode) (ordr ordw:mode) (lhs:Reg.t) (loc:lexpr)
  | fence (ord:mode)
  | ifgoto (e:expr) (n:nat)
  .

(*  Definition regs_of_rmw (rmw:rmw): RegSet.t :=
    match rmw with
    | fetch_add addendum => (regs_of_expr addendum)
    | cas old new => RegSet.union (regs_of_expr old) (regs_of_expr new)
    end.
*)

(*  Definition regs_of (i:t): RegSet.t :=
    match i with
    | assign reg rhs => RegSet.add reg (regs_of_expr rhs)
    | load _ reg l => RegSet.add reg (regs_of_lexpr l)
    | store _ l val =>
      RegSet.union (regs_of_lexpr l) (regs_of_expr val)
    | update rmw _ _ reg l =>
      RegSet.add reg (RegSet.union (regs_of_rmw rmw) (regs_of_lexpr l))
    | fence _ => RegSet.empty
    | ifgoto e _ => regs_of_expr e 
    end.
*)
End Instr.
Coercion Instr.expr_val: Value.t >-> Instr.expr.

Module Prog.
  Definition t := IdentMap.t (list Instr.t).
  (* Structure t := *)
  (*   mk { *)
  (*       progf : IdentMap.t (list Instr.t); *)
  (*       (* threads : list thread_id; *) *)
  (*       (* thread_id -> list Instr.t; *) *)
  (*     }. *)
        (* tunique : NoDup threads; *)
End Prog.
