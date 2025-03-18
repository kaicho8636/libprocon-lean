import Std.Data.HashSet
open Std


-- Graphs
abbrev Node := Nat
abbrev Edge := Node × Node

structure Graph where
  n : Nat
  adjecent : Array (List Node)

namespace Graph

def nodes (g : Graph) : List Node :=
  List.range g.n

def edges (g : Graph) : List Edge :=
  g.nodes.flatMap (λ u =>
    let vs := g.adjecent[u]!
    vs.map (λ v => (u, v))
  )

def buildGraph (n : Nat) (es : List Edge) : Graph :=
  let init := Array.mkArray n []
  let adjecent := es.foldl (λ adj (u, v) =>
      adj.modify u (λ vs => vs.insert v)
    ) init
  { n, adjecent }

def reverseEdges (g : Graph) : List Edge :=
  g.edges.map (λ (u, v) => (v, u))

def transposeGraph (g : Graph) : Graph :=
  buildGraph g.n g.reverseEdges


-- Depth-first search
structure dfsTree where
  node ::
  label : Node
  children : List dfsTree

partial def dfsM (g : Graph) (ns : List Node)
  : StateM (HashSet Node) (List dfsTree) :=
  match ns with
  | [] => return []
  | v::vs => do
    let visited ← get
    if visited.contains v then
      dfsM g vs
    else
      let nexts := g.adjecent[v]!
      let as ← dfsM g nexts
      let bs ← dfsM g vs
      return dfsTree.node v as::bs

def dfs (g : Graph) (ns : List Node) : List dfsTree :=
  (dfsM g ns).run' HashSet.empty

def dfsAll (g : Graph) : List dfsTree :=
  dfs g g.nodes


-- Algorithms
partial def postorderRec (t : dfsTree) (state : List Node) : List Node :=
  t.label::(t.children.foldr postorderRec state)

def postorder (g : Graph) : List Node :=
  (dfsAll g).foldr postorderRec []

def scc (g : Graph) : List dfsTree :=
  g.dfs g.transposeGraph.postorder.reverse

end Graph
