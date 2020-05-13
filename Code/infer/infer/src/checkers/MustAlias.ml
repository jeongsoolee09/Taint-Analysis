open! IStd

(* Faithful implementation of CC'18 paper *)

module Hashtbl = Caml.Hashtbl

exception NotImplemented

module V = struct
  include Var
  let hash = Hashtbl.hash
end

module E = struct
  type t = Fieldname.t [@@deriving compare]
  let default =
    let dummy_java_classname = JavaClassName.from_string "DummyClass" in
    let typ_name = Fieldname.make (JavaClass dummy_java_classname) "dummy" in
    typ_name
end

module G = Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (V) (E)

