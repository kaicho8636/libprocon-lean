import Std.Data.HashSet
open Std

--
-- Graphs
--
abbrev Node := Nat
abbrev Edge := Node × Node

-- Graph構造体: 頂点数と各頂点の隣接リストを保持する
structure Graph where
  n : Nat
  adjecent : Array (List Node)

namespace Graph

-- 指定されたグラフの全頂点（0からn-1まで）のリストを返す
def nodes (g : Graph) : List Node :=
  List.range g.n

-- グラフ内の全辺のリストを返す
def edges (g : Graph) : List Edge :=
  g.nodes.flatMap (λ u =>
    let vs := g.adjecent[u]!
    vs.map (λ v => (u, v))
  )

-- 指定された頂点数と辺のリストからグラフを構築する
def buildGraph (n : Nat) (es : List Edge) : Graph :=
  let init := Array.mkArray n []
  let adjecent := es.foldl (λ adj (u, v) =>
      adj.modify u (λ vs => vs.insert v)
    ) init
  { n, adjecent }

-- 各辺の向きを逆転させた辺のリストを返す
def reverseEdges (g : Graph) : List Edge :=
  g.edges.map (λ (u, v) => (v, u))

-- 各辺の向きを逆転させたグラフを返す
def transposeGraph (g : Graph) : Graph :=
  buildGraph g.n g.reverseEdges


--
-- Depth-first search
--
-- 深さ優先探索の結果として得る探索木のノードを表す構造体
structure dfsTree where
  node ::
  label : Node  -- ノードの値
  children : List dfsTree  -- 子ノードのリスト

namespace dfsTree

partial def flatten (t : dfsTree) : List Node :=
  t.label::t.children.flatMap flatten

end dfsTree

-- StateMモナドを用いて深さ優先探索を実行する内部関数
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

-- 与えられた頂点リストに対して深さ優先探索を実行する
def dfs (g : Graph) (ns : List Node) : List dfsTree :=
  (dfsM g ns).run' HashSet.empty

-- グラフ全体に対して深さ優先探索を実行する
def dfsAll (g : Graph) : List dfsTree :=
  dfs g g.nodes


--
-- Algorithms
--
-- dfsTreeのノードを後順（postorder）に走査する再帰関数
partial def postorderRec (t : dfsTree) (state : List Node) : List Node :=
  t.label::(t.children.foldr postorderRec state)

-- グラフの探索木に対して後順走査を実行し、ノードのリストを返す
def postorder (g : Graph) : List Node :=
  (dfsAll g).foldr postorderRec []

-- グラフの強連結成分（Strongly Connected Components）を求める
def sccTree (g : Graph) : List dfsTree :=
  g.dfs g.transposeGraph.postorder.reverse

def scc (g : Graph) : List (List Node) :=
  g.sccTree.map dfsTree.flatten

end Graph
