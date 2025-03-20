--import Std.Data.HashSet
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Insert
open Std


abbrev Node := Nat
abbrev Edge := Node × Node
structure Graph where
  n : Nat -- 頂点数
  adj : Array (List Node) -- 隣接リスト

namespace Graph

-- グラフに含まれる頂点のリストを返す
def nodes (g : Graph) : List Node :=
  List.range g.n

-- グラフに含まれる辺のリストを返す
def edges (g : Graph) : List Edge :=
  let getEdges := λ u => g.adj[u]!.map λ v => (u, v)
  g.nodes.flatMap getEdges

-- 頂点数nと辺のリストesからグラフを構築
def buildGraph (n : Nat) (es : List Edge) : Graph :=
  let init := Array.mkArray n []
  let insertEdge := λ adj (u, v) => adj.modify u (λ vs => v::vs)
  let adj := es.foldl insertEdge init
  { n, adj }

-- 転置(辺の向きを反転)したグラフを返す
def transposeGraph (g : Graph) : Graph :=
  let reverseEdge := λ (u, v) => (v, u)
  buildGraph g.n (g.edges.map reverseEdge)


-- DFSの結果を保持する木構造
structure DFSTree where
  node ::
  label : Node
  children : List DFSTree

-- 木に含まれるノードのリストを返す
partial def dfsTree.flatten (t : DFSTree) : List Node :=
  t.label :: t.children.flatMap flatten

-- (内部関数)nsをスタックとしてグラフをDFS
partial def dfsM (g : Graph) (ns : List Node) : StateM (Finset Node) (List DFSTree) :=
  match ns with
  | [] => return []
  | v::vs => do
    let visited ← get
    if v ∈ visited then
      dfsM g vs
    else
      set (insert v visited)
      let nexts := g.adj[v]!
      let as ← dfsM g nexts
      let bs ← dfsM g vs
      return DFSTree.node v as::bs

-- nsに含まれる各ノードを起点に探索し、探索木のリストを返す
-- ただし起点が既に探索済みの場合、その探索はスキップされる
def dfs (g : Graph) (ns : List Node) : List DFSTree :=
  (g.dfsM ns).run' Finset.empty

-- すべてのNodeについてdfsする
def dfsAll (g : Graph) : List DFSTree :=
  dfs g g.nodes


--
--  Algorithms
--

-- （内部関数）自分を後退順の最後に追加して再帰
partial def postorderRec (t : DFSTree) (state : List Node) : List Node :=
  t.children.foldr postorderRec (t.label::state)

-- グラフの全頂点をdfsし、後退順で頂点が入ったリストを返す
def postorder (g : Graph) : List Node :=
  g.dfsAll.foldr postorderRec []

-- sccの内部関数
def sccTree (g : Graph) : List DFSTree :=
  g.transposeGraph.dfs g.postorder.reverse

-- Kosaraju AlgorithmでグラフをSCCに分解する
def scc (g : Graph) : List (List Node) :=
  g.sccTree.map dfsTree.flatten

end Graph
