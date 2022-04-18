/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/

namespace Cpdt
namespace Chapter4

inductive IsZero : Nat → Prop where
  | zero : IsZero 0

theorem add_IsZero : IsZero m → n + m = n := by
  intro h
  cases h
  rfl

theorem IsZero_contra : IsZero 1 → False := by
  intro h
  cases h

end Chapter4
end Cpdt
