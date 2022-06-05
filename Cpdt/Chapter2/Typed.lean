/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/

namespace Cpdt
namespace Chapter2

inductive Ty where
  | nat : Ty
  | bool : Ty

inductive TBinop : Ty → Ty → Ty → Type where
  | plus : TBinop .nat .nat .nat
  | times : TBinop .nat .nat .nat
  | eq (t : Ty) : TBinop t t .bool
  | lt : TBinop .nat .nat .bool

inductive TExp : Ty → Type where
  | nConst : Nat → TExp .nat
  | bConst : Bool → TExp .bool
  | binop : TBinop t1 t2 r → TExp t1 → TExp t2 → TExp r

namespace Ty

@[reducible]
def denote : Ty → Type
  | nat => Nat
  | bool => Bool

end Ty

namespace TBinop

def denote : TBinop t1 t2 r → (t1.denote → t2.denote → r.denote)
  | plus => Nat.add
  | times => Nat.mul
  | eq .nat => (· == ·)
  | eq .bool => (· == ·)
  | lt => (· < ·)

end TBinop

namespace TExp

def denote : TExp t → t.denote
  | nConst n => n
  | bConst b => b
  | binop op arg1 arg2 => op.denote (denote arg1) (denote arg2)

@[simp] theorem denote_nConst : denote (nConst n) = n := by rfl
@[simp] theorem denote_bConst : denote (bConst b) = b := by rfl
@[simp] theorem denote_binop : denote (binop op arg1 arg2) = op.denote (denote arg1) (denote arg2) := by rfl

end TExp

abbrev TStack := List Ty

inductive TInstr : TStack → TStack → Type where
  | inConst (n : Nat) : TInstr s (.nat :: s)
  | ibConst (b : Bool) : TInstr s (.bool :: s)
  | iBinop (op : TBinop arg1 arg2 r) : TInstr (arg1 :: arg2 :: s) (r :: s)

inductive TProg : TStack → TStack → Type where
  | nil : TProg s s
  | cons : TInstr s1 s2 → TProg s2 s3 → TProg s1 s3

namespace TStack

@[reducible]
def VStack : TStack → Type
  | [] => Unit
  | t :: ts => t.denote × VStack ts

end TStack

namespace TInstr

open TStack

def denote : TInstr ts ts' → VStack ts → VStack ts'
  | inConst n, s => (n, s)
  | ibConst b, s => (b, s)
  | iBinop op, (arg1, (arg2, s')) => (op.denote arg1 arg2, s')

@[simp] theorem denote_inConst : denote (inConst n) s = (n, s) := by rfl
@[simp] theorem denote_ibConst : denote (ibConst b) s = (b, s) := by rfl
@[simp] theorem denote_iBinop : denote (iBinop op) (arg1, (arg2, s')) = (op.denote arg1 arg2, s') := by rfl

end TInstr

namespace TProg

open TStack

def denote : TProg ts ts' → VStack ts → VStack ts'
  | nil, s => s
  | cons i p, s => (denote p) (i.denote s)

def concat : TProg ts1 ts2 → TProg ts2 ts3 → TProg ts1 ts3
  | nil, ps => ps
  | cons i ps, rs => cons i (concat ps rs)
  
@[simp] theorem denote_nil : denote nil s = s := by rfl
@[simp] theorem denote_cons : denote (cons i p) s = (denote p) (i.denote s) := by rfl
@[simp] theorem concat_nil : concat nil ps = ps := by rfl
@[simp] theorem concat_cons : concat (cons i ps) rs = cons i (concat ps rs) := by rfl

end TProg

namespace TExp

open TInstr TProg TStack

def compile : (e : TExp t) → (ts : TStack) → TProg ts (t :: ts)
  | nConst n, _ => cons (inConst n) nil
  | bConst b, _ => cons (ibConst b) nil
  | binop op arg1 arg2, _ =>
      let arg2Out := compile arg2 _
      let arg1Out := compile arg1 _
      let opOut := cons (iBinop op) nil
      concat arg2Out (concat arg1Out opOut)

@[simp] theorem compile_nConst : compile (nConst n) ts = cons (inConst n) nil := by rfl
@[simp] theorem compile_bConst : compile (bConst b) ts = cons (ibConst b) nil := by rfl
@[simp] theorem compile_binop :
  compile (@binop _ _ r op arg1 arg2) ts
  = concat (compile arg2 ts) (concat (compile arg1 (r :: ts)) (cons (iBinop op) nil)) := by rfl

theorem concat_correct : ∀ (p1 : TProg ts1 ts2) (p2 : TProg ts2 ts3) (s : VStack ts1), TProg.denote (concat p1 p2) s = TProg.denote p2 (TProg.denote p1 s) := by
  intro p1
  induction p1 <;> simp_all

theorem compile_correct_helper : ∀ (e : TExp t) (ts : TStack) (s : VStack ts), TProg.denote (compile e ts) s = (TExp.denote e, s) := by
  intro e 
  induction e <;> simp_all[compile, concat_correct]

theorem compile_correct : ∀ (e : TExp t), TProg.denote (compile e []) () = (TExp.denote e, ()) := by
  simp [compile_correct_helper]

end TExp

end Chapter2
end Cpdt
