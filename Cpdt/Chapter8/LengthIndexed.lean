/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
namespace Cpdt
namespace Chapter8

inductive IList (α : Type) : Nat → Type where
  | nil : IList α 0
  | cons : α → IList α n → IList α n.succ

namespace IList

def append : IList α n → IList α m → IList α (m + n)
  | nil, ys => ys
  | cons x xs, ys => cons x (append xs ys)

def inject : (xs : List α) → (IList α xs.length)
  | [] => nil
  | x :: xs => cons x (inject xs)

def unject : (xs : IList α n) → {ys : List α // ys.length = n}
  | nil => ⟨[], rfl⟩
  | cons x xs =>
    let ⟨rest, prop⟩ := unject xs
    ⟨x :: rest, by simp [prop]⟩

theorem inject_unject_inv : (unject (inject xs)).val = xs := by
  induction xs <;> simp_all[unject, inject]

def head : IList α (Nat.succ n) → α
  | cons x xs => x

end IList
end Chapter8
end Cpdt
