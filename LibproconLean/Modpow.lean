import Mathlib.Tactic.Linarith
import Aesop
open Nat

namespace Modint

/--
def modpow {mod : Nat} [NeZero mod] (a : Modint mod) : Nat → Modint mod :=
  | 0 => 1
  | n + 1 =>
    let b := n + 1
    let half := modpow a (b / 2)
    let remain := if b % 2 == 0 then 1 else a
    half * half * remain
  decreasing_by
    refine Nat.bitwise_rec_lemma ?_
    apply Ne.symm (Nat.zero_ne_add_one n)

def modpow' {mod : Nat} [NeZero mod] (a : Modint mod) : Nat → Modint mod
  | 0 => 1
  | n + 1 =>
    (modpow' a n) * a

#eval modpow (3 : Modint 5) (2 : Nat)
-/
def modpow (c a b : Nat) (hc : c ≠ 0) := (a ^ b) % c

def modpow' (c a b : Nat) (hc : c ≠ 0) :=
  match b with
  | 0 => (if c = 1 then 0 else 1)
  | b' + 1 => ((modpow c a b' hc) * a) % c

def modpow'' (c a b : Nat) (hc : c ≠ 0) :=
  match b with
  | 0 => (if c = 1 then 0 else 1)
  | b' + 1 =>
    let d := b' + 1
    let half := modpow'' c a (d / 2) hc
    let remain := if d % 2 == 0 then 1 else a
    half * half * remain

theorem modpow_eq_modpow' : modpow = modpow' := by
  ext c a b hc
  unfold modpow modpow'
  split
  next b =>
    simp_all only [ne_eq, pow_zero]
    split
    next h =>
      subst h
      simp_all only [one_ne_zero, not_false_eq_true, mod_self]
    next h =>
      exact one_mod_eq_one.mpr h
  next b b' =>
      unfold modpow
      simp_all only [ne_eq, succ_eq_add_one, mod_mul_mod]
      rfl

theorem modpow_eq_modpow'' : modpow = modpow'' := by
  sorry

end Modint
