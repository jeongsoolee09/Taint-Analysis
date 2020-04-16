open! IStd
open DefLocAliasSearches
open DefLocAliasLogicTests
open DefLocAliasDomain

module Hashtbl = Caml.Hashtbl
module S = DefLocAliasDomain.AbstractState
module A = DefLocAliasDomain.SetofAliases

module L = Logging
module F = Format

exception NotImplemented
exception NoEarliestTuple
exception CatFailed

type status =
  | Define of Var.t
  | Call of (Procname.t * Var.t)
  | Redefine of Var.t
  | Dead

type chain = (Procname.t * status) list

type alias_chain = Var.t list

(* GOAL: x가 m2에서 u1으로 redefine되었고 m3 이후로 안 쓰인다는 chain 정보 계산하기 *)
(* --> [(f, Define x), (f, Call (g, y)), (g, Call (m2, u1)), (m2, Redefine u1), (g, Define z), (g, Call (h, w)), (h, Call (m3, u2)), (m3, Dead)] *)
(* TODO: Var.t를 Var.t의 해시값으로 바꾸기 *)

module type Stype = module type of S

module Pair (Domain1:Methname) (Domain2:Stype) = struct
  type t = Domain1.t * Domain2.t [@@deriving compare]
end

module PairOfMS = struct
  include Pair (Procname) (S)
  let hash = Hashtbl.hash
  let equal (a, b) (c, d) = Procname.equal a c && S.equal b d
end

module G = Graph.Imperative.Digraph.ConcreteBidirectional (PairOfMS)

module BFS = Graph.Traverse.Bfs (G)

(** map from procname to its formal args. *)
let formal_args = Hashtbl.create 777

let add_formal_args (key:Procname.t) (value:Var.t list) = Hashtbl.add formal_args key value

let get_formal_args (key:Procname.t) = Hashtbl.find formal_args key

let summary_table = DefLocAlias.TransferFunctions.summaries

let get_summary (key:Procname.t) = Hashtbl.find summary_table key

let callgraph_table = DefLocAlias.TransferFunctions.callgraph

let callgraph = G.create ()

(** 주어진 var이 formal arg인지 검사하고, 맞다면 procname과 formal arg의 리스트를 리턴 *)
let find_procpair_by_var (var:Var.t) =
  let key_values = Hashtbl.fold (fun k v acc -> (k, v)::acc) formal_args [] in
  List.fold_left key_values ~init:[] ~f:(fun acc ((_, varlist) as target) -> if List.mem varlist var ~equal:Var.equal then target::acc else acc)
                                                               
(** 해시 테이블 형태의 콜그래프를 ocamlgraph로 변환한다.*)
let callg_hash2og () : unit =
  Hashtbl.iter (fun key value -> G.add_edge callgraph (key, get_summary key) (value, get_summary value)) (callgraph_table)

(** 주어진 변수 var에 있어 가장 이른 정의 튜플을 찾는다. *)
let find_first_occurrence_of (var:Var.t) : Procname.t * S.t * S.elt =
  let astate = BFS.fold (fun (_, astate) acc ->
      let var_is_in = fun tupleset ->
        match S.find_first_opt (fun tup -> Var.equal (second_of tup) var) tupleset with
        | Some _ -> true
        | None -> false in
      match S.find_first_opt (fun tup -> Var.equal (second_of tup) var) astate with
      | Some _ -> if var_is_in acc then acc else astate
      | None -> acc) S.empty callgraph in
  let elements = S.elements astate in
  let methname = first_of @@ List.nth_exn elements 0 in
  let targetTuples = search_target_tuples_by_vardef var methname astate in
  let earliest_tuple =
    match find_earliest_tuple_within targetTuples with
    | Some earliest_tuple -> earliest_tuple
    | None -> raise NoEarliestTuple in
  (methname, astate, earliest_tuple)


let collect_program_vars_from (aliases:A.t) : Var.t list =
  List.filter ~f:is_program_var (A.elements aliases)


let cat_some : 'a option list -> 'a list =
  List.map ~f:(function
      | Some sth -> sth
      | None -> raise CatFailed)


(** 콜 그래프와 분석 결과를 토대로 체인 (Define -> ... -> Dead)을 계산해 낸다 **)
let compute_chain (var:Var.t) : chain =
  


(** interface with the driver *)
let run_lrm () = () 
