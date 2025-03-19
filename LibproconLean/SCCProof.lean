import LibproconLean.SCC
import Mathlib.Combinatorics.Digraph.Basic
open Graph

def toDigraph (g : Graph) : Digraph Nat :=
  let Adj (u v : Node) := u < g.n ∧ v ∈ g.adj[u]!
  { Adj }
