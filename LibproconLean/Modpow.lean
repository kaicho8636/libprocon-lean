import Mathlib.Tactic.Linarith
import Aesop
open Nat

namespace Modint

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
    (half * half * remain) % c

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


theorem Modint.extracted_1 (b' : ℕ) (s : b' % 2 = 0) : b' / 2 + b' / 2 = b' := by
  calc
  _ = (b' + b') / 2 := by
    have p : ∃ b, b' = 2 * b := by
      refine Even.exists_two_nsmul b' ?_
      exact even_iff.mpr s
    obtain ⟨p', hp⟩ := p
    rw [hp]
    subst hp
    simp_all only [mul_mod_right, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]
    refine Eq.symm (Nat.div_eq_of_eq_mul_right ?_ ?_)
    exact Nat.zero_lt_two
    exact Eq.symm (Nat.mul_add 2 p' p')
  _ = (2 * b') / 2 := by
    rw [Eq.symm (Nat.two_mul b')]
  _ = _ := by
    refine mul_div_right b' ?_
    simp

theorem modpow_eq_modpow'' (c a b : Nat) (hc : c ≠ 0) : modpow c a b hc = modpow'' c a b hc := by
  unfold modpow modpow''
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
    simp
    by_cases s : (b' + 1) % 2 = 0
    · simp [s]
      have ih_n := modpow_eq_modpow'' c a ((b' + 1) / 2) hc
      rw [<- ih_n]
      unfold modpow
      have q : a ^ (b' + 1) % c = (a ^ ((b' + 1) / 2) % c * (a ^ ((b' + 1) / 2) % c)) % c := by
        calc
        _ = a ^ (((b' + 1) / 2) + ((b' + 1) / 2)) % c := by
          rw [Modint.extracted_1 (b' + 1) s]
        _ = (a ^ ((b' + 1) / 2) * a ^ ((b' + 1) / 2)) % c := by
          rw [Nat.pow_add a ((b' + 1) / 2) ((b' + 1) / 2)]
        _ = _ := mul_mod (a ^ ((b' + 1) / 2)) (a ^ ((b' + 1) / 2)) c
      rw [q]
    · simp [s]
      sorry


end Modint
