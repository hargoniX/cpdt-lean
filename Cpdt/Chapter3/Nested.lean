/-
 (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/

namespace Cpdt
namespace Chapter3

inductive NatTree where
  | node : Nat → List NatTree → NatTree

#check NatTree.rec -- not useful for use with the induction tactic since it has two motives

def all (p : α → Prop) : List α → Prop
  | [] => True
  | x :: xs => p x ∧ all p xs

@[simp] theorem all_nil : all p [] := True.intro
@[simp] theorem all_cons : all p (x :: xs) = (p x ∧ all p xs) := by rfl

namespace NatTree

section Ind

variable {motive : NatTree → Prop}
variable (node_case : ∀ (n : Nat) (ls : List NatTree), all motive ls → motive (node n ls))

mutual
  def nat_tree_ind : (tr : NatTree) → motive tr
    | node n rest => node_case n rest (list_nat_tree_ind rest)

  def list_nat_tree_ind : (ls : List NatTree) → all motive ls
    | [] => True.intro
    | l :: ls => And.intro (nat_tree_ind l) (list_nat_tree_ind ls)
end

end Ind

#check nat_tree_ind

-- Sadly writing the definition like in the book doesnt work yet :(
mutual
  def size : NatTree → Nat
    | node x ts => 1 + nodeListSize ts

  def nodeListSize : List NatTree → Nat
    | [] => 0
    | t :: ts => size t + nodeListSize ts
end

def splice : NatTree → NatTree → NatTree
  | node x [], t2 => node x [t2]
  | node x (t :: ts), t2 => node x (splice t t2 :: ts)

@[simp] theorem size_tree : size (node x ts) = 1 + nodeListSize ts := by rw [size]
@[simp] theorem nodeListSize_nil : nodeListSize [] = 0 := by rfl
@[simp] theorem nodeListSize_cons : nodeListSize (t :: ts) = size t + nodeListSize ts := by rw[nodeListSize]
@[simp] theorem splice_node_nil : splice (node x []) t2 = node x [t2] := by rfl
@[simp] theorem splice_node_cons : splice (node x (t :: ts)) t2 = node x (splice t t2 :: ts) := by rw[splice]

theorem splice_size : ∀ t1 t2, size (splice t1 t2) = size t1 + size t2 := by
  intro t1
  induction t1 using nat_tree_ind with
  | node_case x ts ih =>
    cases ts <;> simp_all
    simp_arith

end NatTree

end Chapter3
end Cpdt
