import Std.Data.HashSet
open Std

namespace Tarjan

abbrev Node n := Fin n

structure TarjanState where
  visited : HashSet (Node n)
