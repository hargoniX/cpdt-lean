/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/

namespace Cpdt
namespace Chapter5

inductive Exp where
  | nat : Nat → Exp
  | add : Exp → Exp → Exp
  | bool : Bool → Exp
  | and : Exp → Exp → Exp

inductive Ty where
  | nat : Ty
  | bool : Ty
  deriving DecidableEq

inductive HasType : Exp → Ty → Prop where
  | constNat (n : Nat) : HasType (.nat n) .nat
  | constBool (b : Bool) : HasType (.bool b) .bool
  | addApp (l r : Exp) (hl : HasType l .nat) (hr : HasType r .nat) : HasType (.add l r) .nat
  | andApp (l r : Exp) (hl : HasType l .bool) (hr : HasType r .bool) : HasType (.and l r) .bool

inductive Maybe (p : α → Prop) where
  | found : (a : α) → p a → Maybe p
  | unknown : Maybe p

notation "{{" t "|" p "}}" => Maybe (fun t => p)

def Exp.typecheck : (e : Exp) → {{ t | HasType e t }}
  | nat n => .found .nat (.constNat n)
  | bool b => .found .bool (.constBool b)
  | add l r =>
    match l.typecheck, r.typecheck with
    | .found .nat lth, .found .nat rth => .found .nat (.addApp l r lth rth)
    | _, _ => .unknown
  | and l r =>
    match l.typecheck, r.typecheck with
    | .found .bool lth, .found .bool rth => .found .bool (.andApp l r lth rth)
    | _, _ => .unknown

theorem HasType_det : HasType e t1 → HasType e t2 → t1 = t2 := by
  intro h1 h2
  cases h1 <;> cases h2 <;> rfl

theorem Exp.typecheck_correct : HasType e t → typecheck e ≠ .unknown → typecheck e = .found t h := by
  intro ht1
  cases typecheck e with
  | found t2 ht2 =>
    intros
    have h : t = t2 := HasType_det ht1 ht2
    simp [h]
  | unknown =>
    intros
    contradiction

theorem Exp.typecheck_complete : typecheck e = .unknown → ∀ t, ¬HasType e t := by
  induction e with simp [Exp.typecheck]
  | add l r lih rih =>
    split
    case add.h_1 _ _ htl htr rl rr =>
      intros
      contradiction
    case add.h_2 _ _ hnp =>
      intro h t ht
      cases ht with
      | addApp lt rt lth rth =>
        exact hnp lth rth (typecheck_correct lth (lih · _ lth)) (typecheck_correct rth (rih · _ rth))
  | and l r lih rih =>
    split
    case and.h_1 _ _ htl htr rl rr =>
      intros
      contradiction
    case and.h_2 _ _ hnp =>
      intro h t ht
      cases ht with
      | andApp lt rt lth rth =>
        exact hnp lth rth (typecheck_correct lth (lih · _ lth)) (typecheck_correct rth (rih · _ rth))


def Exp.typecheck' (e : Exp) : {t : Ty // HasType e t} ⊕' (∀ t, ¬HasType e t) :=
  match h:Exp.typecheck e with
  | .found t ht => PSum.inl ⟨t, ht⟩
  | .unknown => PSum.inr (typecheck_complete h)

end Chapter5
end Cpdt
