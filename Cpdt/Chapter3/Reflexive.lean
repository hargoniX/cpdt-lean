/-
 (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/

namespace Cpdt
namespace Chapter3

inductive Formula where
  | eq : Nat → Nat → Formula
  | and : Formula → Formula → Formula
  | universal : (Nat → Formula) → Formula

namespace Formula

def denote : Formula → Prop
  | eq l r => l = r
  | and l r => (denote l) ∧ (denote r)
  | universal p => ∀ x, denote (p x)

@[simp] theorem denote_eq : denote (eq l r) = (l = r) := by rfl
@[simp] theorem denote_and : denote (and l r) = (denote l ∧ denote r) := by rfl
@[simp] theorem denote_universal : denote (universal p) = (∀ x, denote (p x)) := by rfl

def swapper : Formula → Formula
  | eq l r => eq r l
  | and l r => and r l
  | universal p => universal (fun x => swapper (p x))

@[simp] theorem swapper_eq : swapper (eq l r) = eq r l := by rfl
@[simp] theorem swapper_and : swapper (and l r) = and r l := by rfl
@[simp] theorem swapper_universal : swapper (universal p) = universal (fun x => swapper (p x)) := by rfl

theorem swapper_of_normal : ∀ f, (denote f) → denote (swapper f) := by
  intro f
  induction f <;> simp_all

end Formula

end Chapter3
end Cpdt
