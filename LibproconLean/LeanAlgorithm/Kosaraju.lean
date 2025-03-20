--import Std.Data.HashSet
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Card
import LibproconLean.LeanAlgorithm.SCCs


open Std

abbrev Node n := Fin n
abbrev Graph n := Vector (List (Node n)) n
abbrev Visited n := Finset (Node n)
abbrev Components n := List (List (Node n))

namespace Kosaraju

def dfs_postorder
  (graph : Graph n)
  (visited : Visited n)
  (current : Node n)
  : Visited n × List (Node n) :=
  if h : current ∈ visited then
    (visited, [])
  else
    let visited' := insert current visited
    let nexts := (graph.get current).filter (λ next => !(next ∈ visited))
    nexts.foldl (λ acc next =>
      let (v, r) := dfs_postorder graph acc.fst next
      (v, acc.snd ++ r)
    ) (visited', [current])
  termination_by (n + 1) - visited.card
  decreasing_by
    refine Nat.sub_lt_sub_left ?_ ?_
    refine Nat.lt_add_one_of_le ?_
    exact card_finset_fin_le visited
    have s : current ∈ acc.1 := by
      sorry
    refine Finset.card_lt_card ?_
    refine Finset.ssubset_iff_subset_ne.mpr ?_
    constructor
    · sorry
    · exact Ne.symm (ne_of_mem_of_not_mem' s h)

def dfs_all_nodes (graph : Graph n) : List (Node n) :=
  let nodes := List.finRange n
  let (_, postorder) := nodes.foldl (
    λ (acc : Visited n × List (Node n)) (start : Node n) =>
      let (v, r) := acc
      if start ∈ v then
        acc
      else
        let (v', r') := dfs_postorder graph v start
        (v', r ++ r')
  ) (Finset.empty, [])
  postorder

def dfs_collect_component
  (inverted : Graph n)
  (postorder : List (Node n))
  : Components n :=
  let (_, components) := postorder.foldl (
    λ (acc : Visited n × Components n) (start : Node n) =>
      let (v, r) := acc
      if start ∈ v then
        acc
      else
        let (v', r') := dfs_postorder inverted v start
        (v', r' :: r)
  ) (Finset.empty, [])
  components

def add_edge
  (graph : Graph n)
  (origin : Node n)
  (target : Node n)
  : Graph n :=
  graph.set origin (target :: graph.get origin)

def vecFinRange (n : Nat) : Vector (Fin n) n :=
  match n with
  | 0 => Vector.mkEmpty 0
  | m + 1 => ((vecFinRange m).map Fin.castSucc).push (Fin.mk m (by simp))

def invert_graph (graph : Graph n) : Graph n :=
  (graph.zip (vecFinRange n)).foldl (λ acc (v, i) =>
    v.foldl (λ acc' j => add_edge acc' j i) acc
  ) (Vector.mkVector n [])

def kosaraju (graph : Graph n) : Components n :=
  let postorder := dfs_all_nodes graph
  let inverted := invert_graph graph
  dfs_collect_component inverted postorder

theorem kosaraju_proof : ∀ g : Graph n, SCCs.strong_components g (kosaraju g) := by
  sorry
