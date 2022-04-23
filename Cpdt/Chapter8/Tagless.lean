/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
namespace Cpdt
namespace Chapter8

inductive Ty where
  | nat : Ty
  | bool : Ty
  | prod : Ty → Ty → Ty

inductive Exp : Ty → Type
  | nConst : Nat → Exp .nat
  | plus : Exp .nat → Exp .nat → Exp .nat
  | eq : Exp .nat → Exp .nat → Exp .bool
  | bConst : Bool → Exp .bool
  | and : Exp .bool → Exp .bool → Exp .bool
  | if_ : Exp .bool → Exp α → Exp α → Exp α
  | pair : Exp α → Exp β → Exp (.prod α β)
  | fst : Exp (.prod α β) → Exp α
  | snd : Exp (.prod α β) → Exp β

@[reducible]
def Ty.denote : Ty → Type
  | nat => Nat
  | bool => Bool
  | prod α β => Prod (denote α) (denote β)

def Exp.denote : Exp α → α.denote
  | nConst n => n
  | plus l r => Nat.add (denote l) (denote r)
  | eq l r => (denote l) == (denote r)
  | bConst b => b
  | and l r => (denote l) && (denote r)
  | if_ d l r => if (denote d) then (denote l) else (denote r)
  | pair l r => (denote l, denote r)
  | fst p => (denote p).fst
  | snd p => (denote p).snd

def Exp.pairOut : Exp (.prod α β) → Option (Exp α × Exp β)
  | pair l r => some (l, r)
  | _ => none

def Exp.cfold : Exp α → Exp α
  | nConst n => nConst n
  | plus l r =>
    let lfold := cfold l
    let rfold := cfold r
    match lfold, rfold with
    | nConst n, nConst m => nConst (n + m)
    | _, _ => plus lfold rfold
  | eq l r =>
    let lfold := cfold l
    let rfold := cfold r
    match lfold, rfold with
    | nConst n, nConst m => bConst (n == m)
    | _, _ => eq lfold rfold
  | bConst b => bConst b
  | and l r =>
    let lfold := cfold l
    let rfold := cfold r
    match lfold, rfold with
    | bConst n, bConst m => bConst (n && m)
    | _, _ => and lfold rfold
  | if_ d l r =>
    let dfold := cfold d
    let lfold := cfold l
    let rfold := cfold r
    match dfold with
    | bConst true => lfold
    | bConst false => rfold
    | _ => if_ dfold lfold rfold
  | pair l r => pair (cfold l) (cfold r)
  | fst p =>
    let pfold := cfold p
    match pairOut pfold with
    | some p => p.fst
    | none => fst pfold
  | snd p =>
    let pfold := cfold p
    match pairOut pfold with
    | some p => p.snd
    | none => snd pfold

theorem Exp.cfold_correct : denote e = denote (cfold e) := by
  induction e with simp[denote, cfold]
  | plus l r => split <;> simp_all[denote, cfold]
  | eq l r => split <;> simp_all[denote, cfold]
  | and l r => split <;> simp_all[denote, cfold]
  | if_ d l r dih lih rih =>
    rw[dih, lih, rih]
    cases cfold d with simp[denote]
    | bConst b => cases b <;> simp
  | pair l r => simp_all[denote]
  | fst p ih => 
    rw[ih]
    cases cfold p <;> simp[pairOut, denote]
  | snd p ih =>
    rw[ih]
    cases cfold p <;> simp[pairOut, denote]

end Chapter8
end Cpdt
