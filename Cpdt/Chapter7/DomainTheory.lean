/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Cpdt.Chapter7.Wellfounded

namespace Cpdt
namespace Chapter7

abbrev Computation (α : Type) :=
  {f : Nat → Option α // ∀ n (v : α), f n = some v → ∀ n', n' ≥ n → f n' = some v}

namespace Subtype

end Subtype

namespace Computation

def runTo (m : Computation α) (n : Nat) (v : α) :=
  m.val n = some v 

def run (m : Computation α) (v : α) :=
  ∃ n, m.val n = some v 

def bottom : Computation α :=
  ⟨fun _ => none, by intros; contradiction⟩

theorem run_bottom : ∀ (v : α), ¬ (run bottom v) := by
  intro v
  simp[run, bottom]
  intro h
  cases h
  assumption

def ret (v : α) : Computation α :=
  ⟨fun _ => some v, by intros; assumption⟩

theorem run_return : ∀ (v : α), run (ret v) v := by
  intro v
  simp [run, ret]
  exact Exists.intro 0 True.intro

def bind_fun (m1 : Computation α) (m2 : α → Computation β) (n : Nat) : Option β :=
  match m1.val n with
  | none => none
  | some a => (m2 a).val n

theorem bind_fun_computation (m1 : Computation α) (m2 : α → Computation β) :
    ∀ n v , bind_fun m1 m2 n = some v → ∀ n', n' ≥ n → bind_fun m1 m2 n' = some v := by
  intro n v h1 n' h
  cases h2 : m1.val n with
  | none => simp_all[bind_fun]
  | some x =>
    simp_all[bind_fun]
    have m1_n'_runs : m1.val n' = some x := m1.property n x h2 n' h
    have m2_n'_runs : (m2 x).val n' = some v := (m2 x).property n v h1 n' h
    simp[m1_n'_runs, m2_n'_runs]

def bind (m1 : Computation α) (m2 : α → Computation β) : Computation β :=
  ⟨bind_fun m1 m2, bind_fun_computation m1 m2⟩

def ext (m1 m2 : Computation α) : (∀ n, m1.val n = m2.val n) → m1 = m2 := by
  intro h
  cases m1; cases m2
  simp
  apply funext
  exact h

instance : Monad Computation where
  pure := ret
  bind := bind

instance : LawfulMonad Computation where
  id_map         := by
    intros
    simp[Functor.map, ret, bind, bind_fun]
    apply ext
    intros
    simp
    split <;> simp_all
  map_const      := by simp[Functor.mapConst, ret, bind, bind_fun, Functor.map]
  seqLeft_eq     := by
    intro α β x y
    simp [SeqLeft.seqLeft, Seq.seq, bind, bind_fun, ret, Functor.map, Function.const]
    apply funext
    intro n
    cases x.val n <;> cases y.val n <;> simp
  seqRight_eq    := by
    intro α β x y
    simp [SeqRight.seqRight, Seq.seq, bind, bind_fun, ret, Functor.map, Function.const]
    apply funext
    intro n
    cases x.val n <;> cases y.val n <;> simp
  pure_seq       := by simp [Seq.seq, pure, ret, bind, bind_fun, Functor.map]
  -- Since our monads are basically Option.bind + Subtype which is very
  -- easy to argue about we can just get everything with definition unwrapping
  bind_pure_comp := by simp [Bind.bind, bind, bind_fun, pure, ret, Functor.map]
  bind_map       := by simp [Bind.bind, bind, bind_fun, Seq.seq, ret, Functor.map]
  pure_bind      := by
    intro α m1 m2 f
    simp [Bind.bind, bind, bind_fun, pure, ret]
    apply ext
    simp
  bind_assoc     := by
    intro α β γ x f g
    simp [Bind.bind, bind, bind_fun]
    apply funext
    intro n
    cases x.val n <;> simp

def approximationOrder (l r : Option α) := ∀ v, l = some v → r = some v

infix:60 " ⊑ " => approximationOrder

section Fix

variable {α β : Type} (f : (α → Computation β) → (α → Computation β))
variable (f_continious : ∀ n v v1 x,
  runTo (f v1 x) n v → ∀ (v2: α → Computation β),
    (∀ x, (v1 x).val n ⊑ (v2 x).val n) → runTo (f v2 x) n v)

def fix' (n : Nat) (x : α) : Computation β :=
  match n with
  | 0 => bottom
  | m + 1 => f (fix' m) x

theorem fix'_ok :
    ∀ steps n x v, (fix' f n x).val steps = some v →
      ∀ n', n' ≥ n → (fix' f n' x).val steps = some v := by
  intro steps n x v h1 n' h2
  induction n with
  | zero => simp_all_arith[fix', bottom]
  | succ m ih =>
    simp_all[fix', runTo]
    sorry 

def fix (x : α) : Computation β :=
  ⟨fun n => ((fix' f n x).val n), by
    intro n v h1 n' h2
    simp_all[fix']
    apply fix'_ok
    sorry
    assumption
  ⟩

theorem run_fix : ∀ x v, run (f (fix f) x) v → run (fix f x) v:= by
  intro x v h
  cases h with
  | intro n h =>
    exists n.succ
    apply f_continious
    sorry
    sorry
    sorry

end Fix

-- some experimentation with the merge sort example showed, that as its
-- is presented in the book this approach will not work out. Hence I stopped
-- work on it.

end Computation

end Chapter7
end Cpdt
