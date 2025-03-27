abbrev Modint (mod : Nat) [NeZero mod] := Fin mod

namespace Modint

def modpow {mod : Nat} [NeZero mod] (a : Modint mod) : Nat → Modint mod
  | 0 => 1
  | n + 1 =>
    let b := n + 1
    let half := modpow a (b / 2)
    let remain := if b % 2 == 0 then 1 else a
    half * half * remain
  decreasing_by
    refine Nat.bitwise_rec_lemma ?_
    apply Ne.symm (Nat.zero_ne_add_one n)

instance {mod n : Nat} [NeZero mod] : OfNat (Modint mod) n  where
  ofNat := ⟨n % mod, by
    refine Nat.mod_lt n ?_
    exact Nat.pos_of_neZero mod⟩

instance {mod : Nat} [NeZero mod] : NatPow (Modint mod) where
  pow a b := modpow a b

end Modint
