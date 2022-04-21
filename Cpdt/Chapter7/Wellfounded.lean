/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
namespace Cpdt
namespace Chapter7

variable {α : Type} [LE α] [DecidableRel (@LE.le α _)]

def insert (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: (insert x ys)

def merge (l1 l2 : List α) : List α :=
  match l1 with
  | [] => l2
  | x :: xs => insert x (merge xs l2)

def split : List α → List α × List α
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: zs =>
    let (l1, l2) := split zs
    (x :: l1, y :: l2)

theorem split_wf_match (x y : α) (zs : List α) :
    let spl := split (x :: y :: zs);
    spl.fst.length < zs.length + 2 ∧ spl.snd.length < zs.length + 2 :=
    match zs with
    | [] => by simp[split]
    | [a] => by simp[split]
    | a :: b :: cs => by
      have helper := split_wf_match a b cs
      simp_all_arith[split]
      constructor
      apply Nat.le_trans helper.left
      simp_arith
      apply Nat.le_trans helper.right
      simp_arith

def mergeSort : List α → List α
  | [] => []
  | [x] => [x]
  | ls@(x :: y :: zs) =>
    let lss := split ls
    have h1 : List.length (split ls).fst < Nat.succ (Nat.succ (List.length zs)) := by
      have helper := (split_wf_match x y zs).left
      simp_all
    have h2 : List.length (split ls).snd < Nat.succ (Nat.succ (List.length zs)) := by
      have helper := (split_wf_match x y zs).right
      simp_all
    merge (mergeSort lss.fst) (mergeSort lss.snd)
  termination_by mergeSort ls => ls.length

end Chapter7
end Cpdt
