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

type chain = (Var.t * status) list

type alias_chain = Var.t list

(* GOAL: x가 m2에서 u1으로 redefine되었고 m3 이후로 안 쓰인다는 chain 정보 계산하기 *)
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

let update_summary (key:Procname.t) (astate:S.t) = Hashtbl.replace summary_table key astate

let get_summary (key:Procname.t) = Hashtbl.find summary_table key

let callgraph_table = DefLocAlias.TransferFunctions.callgraph

let callgraph = G.create ()

let match_procname_astate (procname:Procname.t) : Procname.t*S.t = (procname, get_summary procname)
                                                               
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


(** 주어진 변수 var에 대한 alias들을 계산해 낸다. **)
let compute_alias_chain (var:Var.t) : alias_chain =
  let (methname, astate, firsttuple) = find_first_occurrence_of var in
  let rec compute_alias_chain_inner (current_methname:Procname.t) (current_tuple:S.elt) (current_astate:S.t) (aliaschain:alias_chain) : alias_chain =
    let aliases = collect_program_vars_from @@ fourth_of @@ current_tuple in
    let earliest_alias_tuples = cat_some @@ List.map ~f:(find_earliest_tuple_of_var_within @@ S.elements current_astate) aliases in
    List.map ~f:(fun tup -> compute_alias_chain_inner current_methname tup current_astate @@ (second_of tup) :: aliaschain) earliest_alias_tuples
  in
    compute_alias_chain_inner methname firsttuple astate []

(** 주어진 변수 var에 대한 Dead Point를 계산해 낸다. **)
(* let compute_dead_point (var:Var.t) : Procname *)

(** 콜 그래프와 분석 결과를 토대로 체인 (Define -> ... -> Dead)을 계산해 낸다 **)
(* let compute_chain (var:Var.t) : chain *)

(** interface with the driver *)
let run_lrm () = () 
