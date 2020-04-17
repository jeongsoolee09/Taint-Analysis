open! IStd
open DefLocAlias.TransferFunctions
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
exception NoParent

type status =
  | Define of Var.t
  | Call of (Procname.t * Var.t)
  | Redefine of Var.t
  | Dead

type chain = (Procname.t * status) list

type alias_chain = Var.t list

(* GOAL: x가 m2에서 u1으로 redefine되었고 m3 이후로 안 쓰인다는 chain 정보 계산하기
 * --> [(f, Define x), (f, Call (g, y)), (g, Call (m2, u1)), (m2, Redefine u1), (g, Define z), (g, Call (h, w)), (h, Call (m3, u2)), (m3, Dead)] *)
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
  let key_values = Hashtbl.fold (fun k v acc -> (k, v) ::acc) formal_args [] in
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
  let earliest_tuple = find_earliest_tuple_within targetTuples in
  (methname, astate, earliest_tuple)


(** alias set에서 자기 자신, this, ph를 빼고 남은 program variable들을 리턴 *)
let collect_program_vars_from (aliases:A.t) (self:Var.t) : Var.t list =
  List.filter ~f:(fun x -> is_program_var x &&
                           not @@ Var.equal self x &&
                           not @@ is_placeholder_vardef x &&
                           not @@ Var.is_this x) (A.elements aliases)


let select_up_to (tuple:S.elt) (astate:S.t) : S.t =
  let tuples = S.elements astate in
  let select_up_to_inner (tuple:S.elt) : S.t =
    S.of_list @@ List.fold_left tuples ~init:[] ~f:(fun acc elem -> if third_of elem ==> third_of tuple then elem::acc else acc) in
  select_up_to_inner tuple


(** 중복 튜플을 제거함 *)
(* NOTE: 완성품에는 이 함수가 필요 없어야 함 *)
(* NOTE: 본 함수에는 ph와 this를 걸러 주는 기능도 있음. *)
let remove_duplicates_from (astate:S.t) : S.t =
  let grouped_by_duplicates = (group_by_duplicates >> collect_duplicates) astate in
  (* 위의 리스트 안의 각 리스트들 안에 들어 있는 튜플들 중 가장 alias set이 큰 놈을 남김 *)
  let leave_biggest_aliasset = fun lst -> List.fold_left lst ~init:bottuple ~f:(fun acc elem -> if (A.cardinal @@ fourth_of acc) <= (A.cardinal @@ fourth_of elem) then elem else acc) in
  S.of_list @@ List.map ~f:leave_biggest_aliasset grouped_by_duplicates
  

let equal_btw_vertices : PairOfMS.t -> PairOfMS.t -> bool =
  fun (m1, s1) (m2, s2) -> Procname.equal m1 m2 && S.equal s1 s2


(** accumulator를 따라가면서 최초의 parent (즉, 직전의 caller)를 찾아낸다. *)
let traverse_accumulator (target_meth:Procname.t) (acc:chain) =
  let target_vertex = (target_meth, get_summary target_meth) in
  let rec traverse_accumulator_inner (acc:chain) =
    match acc with
    | [] -> raise NoParent
    | (cand_meth, _)::t ->
        let is_pred = fun v -> List.mem (G.pred callgraph target_vertex) v ~equal:equal_btw_vertices in
        let cand_vertex = (cand_meth, get_summary cand_meth) in
        if is_pred cand_vertex
        then cand_vertex
        else traverse_accumulator_inner t
  in
  traverse_accumulator_inner acc


(** 콜 그래프와 분석 결과를 토대로 체인 (Define -> ... -> Dead)을 계산해 낸다 **)
let compute_chain (var:Var.t) : chain =
  (* alias set에서 다음 program var이 발견됨 *)
  let (first_methname, first_astate, first_tuple) = find_first_occurrence_of var in
  let rec compute_chain_inner (current_methname:Procname.t) (current_astate:S.t) (current_tuple:S.elt) (current_chain:chain) : chain =
    let aliasset = fourth_of current_tuple in
    let vardef = second_of current_tuple in
    match collect_program_vars_from aliasset vardef with
    | [] -> (* either redefinition or dead end *)
        let tuples = S.elements current_astate in
        let redefined_tuples = List.fold_left tuples ~init:[] ~f:(fun acc tup -> if Var.equal vardef @@ second_of tup then tup::acc else acc) in
        begin match redefined_tuples with
          | [] -> (* Dead end *) (current_methname, Dead) :: current_chain
          | _ -> (* Redefinition *)
              let future_tuples = S.diff current_astate @@ select_up_to current_tuple (remove_duplicates_from current_astate) in
              let new_tuple = find_earliest_tuple_of_var_within (S.elements future_tuples) vardef in
              let new_chain = (current_methname, Redefine vardef) :: current_chain in
              compute_chain_inner current_methname current_astate new_tuple new_chain
        end
    | nonempty_list -> (* either definition or call *)
        if List.exists nonempty_list ~f:Var.is_return
        then (* caller에서의 define: alternative behavior is needed *)
          (* 1. 바로 직전 콜러를 찾아간다: accumulator를 따라가면서 처음으로 나타나는 parent를 찾는다. *)
          (* 2. 그 중에서 리턴되는 변수와 같은 것이 있는지를 본다. *)
          (*   2-1. 여러 개 있다면, 그 중에서 안 가본 것 중 가장 이른 것을 찾는다.*)
          let (direct_caller, caller_summary) = traverse_accumulator current_methname current_chain in
          raise NotImplemented 
        else (* 동일 procedure 내에서의 define 혹은 call *)
          raise NotImplemented
  in
  List.rev @@ compute_chain_inner first_methname first_astate first_tuple []


(** interface with the driver *)
let run_lrm () = () 
