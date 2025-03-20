namespace SCCs

abbrev Node (n : Nat) := Fin n
abbrev Graph (n : Nat) := Vector (List (Fin n)) n
abbrev Component (n : Nat) := List (Node n)
abbrev Components (n : Nat) := List (Component n)

inductive reachable (g : Graph n) : Node n → Node n → Prop where
| base {a b : Node n} (h : b ∈ g[a]) : reachable g a b
| step {a b c : Node n} (h : c ∈ g[a]) (r : reachable g c b) : reachable g a b

def strongly_connected (g : Graph n) (c : Component n) : Prop :=
  ∀ a ∈ c, ∀ b ∈ c, reachable g a b

def partition (cs : Components n) : Prop :=
  ∀ a, ∃ c ∈ cs, a ∈ c ∧ (∀ d ∈ cs, d ≠ c → a ∉ d)

def maximality (g : Graph n) (c : Component n) : Prop :=
  ∀ a, ((∀ b ∈ c, reachable g a b) ∧ (∀ b ∈ c, reachable g b a)) → a ∈ c

def strong_components (g : Graph n) (cs : Components n) : Prop :=
  partition cs ∧ ∀ c ∈ cs, strongly_connected g c ∧ maximality g c
