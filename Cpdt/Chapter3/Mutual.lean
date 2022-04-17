/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/

namespace Cpdt
namespace Chapter3

mutual
  inductive EvenList where
    | nil : EvenList
    | eCons : Nat → OddList → EvenList
  
  inductive OddList where
    | oCons : Nat → EvenList → OddList
end


mutual
  def elength : EvenList → Nat
    | EvenList.nil => 0
    | EvenList.eCons _ xs => 1 + olength xs

  def olength : OddList → Nat
    | OddList.oCons _ xs => 1 + elength xs
end


mutual
  def eappend : EvenList → EvenList → EvenList
    | EvenList.nil, ys => ys
    | EvenList.eCons x xs, ys => EvenList.eCons x (oappend xs ys)

  def oappend : OddList → EvenList → OddList
    | OddList.oCons x xs, ys => OddList.oCons x (eappend xs ys)
end

namespace EvenList

@[simp] theorem elength_nil : elength nil = 0 := by rfl
@[simp] theorem elength_econs : elength (eCons x xs) = 1 + olength xs := by rw[elength]
@[simp] theorem nil_eappend : eappend nil ys = ys := by rfl
@[simp] theorem eCons_eappend : eappend (eCons x xs) ys = eCons x (oappend xs ys) := by rw[eappend]

end EvenList

namespace OddList

@[simp] theorem olength_oCons : olength (oCons x xs) = 1 + elength xs := by rw [olength]
@[simp] theorem oCons_oappend : oappend (oCons x xs) ys = oCons x (eappend xs ys) := by rw[oappend]

end OddList

theorem elength_eappend (xs ys : EvenList) : elength (eappend xs ys) = elength xs + elength ys := by
  apply @EvenList.rec
    (fun xs => ∀ ys, elength (eappend xs ys) = elength xs + elength ys)
    (fun ol => ∀ el, olength (oappend ol el) = olength ol + elength el)
  <;> simp_all[Nat.add_assoc]

end Chapter3
end Cpdt
