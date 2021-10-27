open Yojson.Basic

exception TODO

module StringWithHash = struct
  include String

  let hash = Hashtbl.hash
end

module G = struct
  include Graph.Persistent.Digraph.ConcreteBidirectional (StringWithHash)

  let graph_attributes _ = []

  let default_vertex_attributes _ = []

  let vertex_name x = x

  let vertex_attributes (_ : V.t) = [`Shape `Box]

  let get_subgraph _ = None

  let default_edge_attributes _ = []

  let edge_attributes _ = []
end

module BFS = Graph.Traverse.Bfs (G)
module Dot = Graph.Graphviz.Dot (G)

type json = Yojson.Basic.t

module VertexMaker = struct
  let get_all_vertices (json : json) : G.V.t list =
    (* for this to work, we need to process individual chains. *)
    raise TODO


  let get_all_methods () =
    Deserializer.deserialize_method_txt "Methods.txt"
    |> List.filter ~f:(fun method_str ->
           (not @@ String.is_substring method_str ~substring:"lambda")
           && (not @@ String.is_substring method_str ~substring:"Lambda")
           && (not @@ String.is_substring method_str ~substring:"<init>")
           && (not @@ String.is_substring method_str ~substring:"<clinit>") )
end

module EdgeMaker = struct
  let get_all_edges (json : json) : G.E.t list = raise TODO
end

module GraphMaker = struct
  let batch_add_vertex (json : json) (graph : G.t) = raise TODO

  let batch_add_edge (json : json) (graph : G.t) = raise TODO

  let init_graph (json : json) : G.t =
    let all_vertices = VertexMaker.get_all_vertices in
    let all_edges = EdgeMaker.get_all_edges in
    G.empty |> batch_add_vertex json |> batch_add_edge json
end
