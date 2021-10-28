open Yojson.Basic
open GraphRepr

exception TODO

module G = GraphRepr.G

type json = Yojson.Basic.t

module GraphMaker = struct
  (* 너는 그래프 만드는 데만 집중해! 디펜던시는 알아서 넣어줄 테니까 *)
  let batch_add_vertex (json : json) (graph : G.t) = raise TODO

  let batch_add_edge (json : json) (graph : G.t) = raise TODO

  let init_graph (json : json) : G.t =
    let all_vertices = VertexMaker.get_all_vertices in
    let all_edges = EdgeMaker.get_all_edges in
    G.empty |> batch_add_vertex json |> batch_add_edge json
end
