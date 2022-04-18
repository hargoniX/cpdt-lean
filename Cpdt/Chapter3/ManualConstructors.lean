
/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/

namespace Cpdt
namespace Chapter3

def Bool.toProp : Bool → Prop := fun b => if b then True else False
theorem Bool.toProp_false : Bool.toProp false = False := by rfl
theorem Bool.toProp_true : Bool.toProp true = True := by rfl

theorem true_neq_false : true ≠ false := by
  intro h
  rw [←Bool.toProp_false]
  rw [←h]
  rw [Bool.toProp_true]
  exact True.intro

theorem s_inj : Nat.succ n = Nat.succ m → n = m := by
  intro h
  rw [←Nat.pred_succ n]
  rw [←Nat.pred_succ m]
  rw [h]

end Chapter3
end Cpdt
