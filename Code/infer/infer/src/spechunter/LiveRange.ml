open! IStd
open DefLocAliasSearches
open DefLocAliasDomain

module Hashtbl = Caml.Hashtbl
module S = DefLocAliasDomain.AbstractState
module A = DefLocAliasDomain.SetofAliases

module L = Logging
module F = Format

exception NotImplemented

type activity =
    Call of (Procname.t * Procname.t)
  | Redefine of (Var.t * Var.t)
  | Define of Var.t

(* a chain is a (Var * activity) list *)
(* GOAL: x가 m2에서 u1으로 redefine되었고 m3 이후로 안 쓰인다는 chain 정보 계산하기 *)
(* TODO: Chain의 Dead point 계산 위해 Call graph 읽어오기 *)


(** map from procname to its formal args. *)
let formal_args = Hashtbl.create 777

let add_formal_args (key:Procname.t) (value:Var.t list) = Hashtbl.add formal_args key value

let get_formal_args (key:Procname.t) = Hashtbl.find formal_args key

let summary_table = DefLocAlias.TransferFunctions.summaries

let update_summary (key:Procname.t) (astate:S.t) = Hashtbl.replace summary_table key astate

let get_summary (key:Procname.t) = Hashtbl.find summary_table key

(** collect all formals from a summary *)
(* uses the invariant that procnames are unique in a state *)
let collect_formals (summary:S.t) =
  let astates = S.elements summary in
  let procname = first_of @@ List.nth_exn astates 0 in
  let locations = List.sort ~compare:Location.compare (List.map ~f:third_of astates) in (* 잘 되겠지? 안 되면 라인 넘버를 끌고 오자 *)
  let earliest_location = List.nth_exn locations 0 in
  let parameters_withthis = List.map ~f:second_of @@ search_tuples_by_loc earliest_location astates in
  let parameters = List.filter ~f:(Var.is_this >> not) parameters_withthis in
  add_formal_args procname parameters


(** filter all formals from a summary, accessed by a procname *)
let filter_formals (methname:Procname.t) =
  let formals = get_summary methname in
  let astates = S.elements formals in
  let locations = List.sort ~compare:Location.compare (List.map ~f:third_of astates) in (* 잘 되겠지? 안 되면 라인 넘버를 끌고 오자 *)
  let earliest_location = List.nth_exn locations 0 in
  let tuples_withthis = search_tuples_by_loc earliest_location astates in
  let formaltuples = List.filter ~f:(fun tup -> not @@ Var.is_this (second_of tup)) tuples_withthis in
  S.diff formals (S.of_list formaltuples)


(** interface with the driver *)
let run_lrm summary_table = raise NotImplemented 
