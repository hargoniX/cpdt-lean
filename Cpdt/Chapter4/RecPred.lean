/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/

namespace Cpdt
namespace Chapter4

inductive Even : Nat → Prop where
  | zero : Even 0
  | succSucc (n : Nat) : Even n → Even n.succ.succ

theorem even4 : Even 4 := by
  simp[Even.succSucc, Even.zero]

theorem even_3_contra : Even 3 → False := by
  intro h
  cases h with
  | succSucc _ h => cases h


theorem even_add : Even n → Even m → Even (n + m) := by
  intro h1
  induction h1 with
  | zero =>
    intro h
    simp_arith
    assumption
  | succSucc x xh ih =>
    intro h
    simp_arith
    constructor
    simp_arith
    apply ih
    assumption

theorem even_contra_helper : ∀ n', Even n' → ∀ n, n' ≠ Nat.succ (n + n) := by
  intro n' hn'
  induction hn' with
  | zero => simp_all
  | succSucc x hx ih =>
    intro n hn
    cases x <;> cases n <;> simp_all <;> simp_arith at *
    case succSucc.succ.succ y m =>
      apply ih m
      assumption

theorem even_contra : Even (Nat.succ (n + n)) → False := by
  intro h
  apply even_contra_helper
  assumption
  rfl

end Chapter4
end Cpdt
