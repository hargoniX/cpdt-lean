/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/

namespace Cpdt
namespace Chapter2

inductive Binop where
  | plus : Binop
  | times : Binop

inductive Exp where
  | const : Nat → Exp
  | binop : Binop → Exp → Exp → Exp

namespace Binop

def denote : Binop → (Nat → Nat → Nat)
  | plus => Nat.add
  | times => Nat.mul

theorem denote_plus : denote plus = Nat.add := by rfl
theorem denote_times : denote times = Nat.mul := by rfl

end Binop

namespace Exp

def denote : Exp → Nat
  | const n => n
  | binop op l r => op.denote l.denote r.denote

theorem denote_const (n : Nat) : denote (const n) = n := by rfl
theorem denote_binop (op : Binop) (l r : Exp) : denote (binop op l r) = op.denote l.denote r.denote := by rfl

end Exp

inductive Instr where
  | iConst : Nat → Instr
  | iBinop : Binop → Instr

abbrev Prog := List Instr
abbrev Stack := List Nat

namespace Instr

def denote : Instr → Stack → Option Stack
  | iConst n , s => some (n :: s)
  | iBinop op, arg1 :: arg2 :: rest => some ((op.denote arg1 arg2) :: rest)
  | iBinop op, _ => none

theorem denote_iConst (n : Nat) (s : Stack) : denote (iConst n) s = some (n :: s) := by rfl
theorem denote_iBinop_2args (b : Binop) (s : Stack) (arg1 arg2 : Nat) : denote (iBinop op) (arg1 :: arg2 :: s) = some (op.denote arg1 arg2 :: s) := by rfl
theorem denote_iBinop_1arg (b : Binop) (arg : Nat) : denote (iBinop op) [arg] = none := by rfl
theorem denote_iBinop_nil (b : Binop) (arg : Nat) : denote (iBinop op) [] = none := by rfl

end Instr

namespace Prog

def denote : Prog → Stack → Option Stack
  | [], s => some s
  | i :: p, s =>
    match i.denote s with
    | some res => denote p res
    | none => none

theorem denote_nil (s : Stack) : denote [] s = some s := by rfl
theorem denote_iConst (s : Stack) (p : Prog) (n : Nat) : denote ((.iConst n) :: p) s = denote p (n :: s) := by rfl
theorem denote_iBinop_2args (s : Stack) (p : Prog) (op : Binop) (arg1 arg2 : Nat) : denote (.iBinop op :: p) (arg1 :: arg2 :: s) = denote p (op.denote arg1 arg2 :: s) := by rfl
theorem denote_iBinop_1args (p : Prog) (op : Binop) (arg : Nat) : denote (.iBinop op :: p) [arg] = none := by rfl
theorem denote_iBinop_nil (p : Prog) (op : Binop) : denote (.iBinop op :: p) [] = none := by rfl

end Prog

namespace Exp

def compile : Exp → Prog
  | const n => [.iConst n]
  | binop b l r => compile r ++ compile l ++ [.iBinop b]

theorem compile_const (n : Nat) : compile (const n) = [.iConst n] := by rfl
theorem compile_binop (op : Binop) (l r : Exp) : compile (binop op l r) = compile r ++ compile l ++ [.iBinop op] := by rfl

end Exp

theorem compile_correct_help : ∀ (e : Exp) (p : Prog) (s : Stack), Prog.denote (Exp.compile e ++ p) s = Prog.denote p (Exp.denote e :: s) := by
  intro e p s
  induction e generalizing p s with
  | const n =>
    rw [Exp.compile_const]
    rw [Exp.denote_const]
    simp
    rw [Prog.denote_iConst]
  | binop b l r lih rih =>
    rw [Exp.compile_binop]
    rw [Exp.denote_binop]
    rw [List.append_assoc (Exp.compile r)]
    rw [List.append_assoc (Exp.compile r)]
    rw [rih]
    rw [List.append_assoc]
    rw [lih]
    simp
    rw [Prog.denote_iBinop_2args]

theorem compile_correct : ∀ (e : Exp), Prog.denote (Exp.compile e) [] = some [Exp.denote e] := by
  intro e
  rw [←List.append_nil (Exp.compile e)]
  rw [compile_correct_help]
  rw [Prog.denote_nil]

end Chapter2
end Cpdt
