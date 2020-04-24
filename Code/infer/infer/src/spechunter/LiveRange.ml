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
exception NoParent
exception UnexpectedSituation
exception IDontKnow

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


(** map from procnames to their summaries. *)
let summary_table = Hashtbl.create 777

let get_summary (key:Procname.t) = Hashtbl.find summary_table key


(** a primitive representation of the call graph. *)
let callgraph_table = Hashtbl.create 777

let callgraph = G.create ()


let chains = Hashtbl.create 777

let add_chain (key:Var.t) (value:chain) = Hashtbl.add chains key value

(** 주어진 var이 formal arg인지 검사하고, 맞다면 procname과 formal arg의 리스트를 리턴 *)
let find_procpair_by_var (var:Var.t) =
  let key_values = Hashtbl.fold (fun k v acc -> (k, v)::acc) formal_args [] in
  List.fold_left key_values ~init:[] ~f:(fun acc ((_, varlist) as target) -> if List.mem varlist var ~equal:Var.equal then target::acc else acc)
                                                               

(** 해시 테이블 형태의 콜그래프를 ocamlgraph로 변환한다.*)
let callg_hash2og () : unit =
  Hashtbl.iter (fun key value -> G.add_edge callgraph (key, get_summary key) (value, get_summary value)) callgraph_table


let filter_callgraph_table hashtbl =
  let procs = Hashtbl.fold (fun k _ acc -> k::acc) summary_table [] in
  Hashtbl.iter (fun k v ->
      if not @@ List.mem procs k ~equal:Procname.equal ||
         not @@ List.mem procs v ~equal:Procname.equal
      then Hashtbl.remove hashtbl k
      else ()) hashtbl


(** 주어진 변수 var에 있어 가장 이른 정의 튜플을 찾는다. *)
let find_first_occurrence_of (var:Var.t) : Procname.t * S.t * S.elt =
  let tupleset = BFS.fold (fun (_, astate) acc ->
      match S.exists (fun tup -> Var.equal (second_of tup) var) astate with
      | true -> L.progress "found it!\n"; astate
      | false -> L.progress "nah..:(\n"; acc) S.empty callgraph in
  let elements = S.elements tupleset in
  let methname = first_of @@ List.nth_exn elements 0
  in
  let targetTuples = search_target_tuples_by_vardef var methname tupleset in
  let earliest_tuple = find_earliest_tuple_within targetTuples in
  (methname, tupleset, earliest_tuple)


(** 디버깅 용도로 BFS 사용해서 그래프 출력하기 *)
let print_graph graph =
  BFS.iter (fun (proc, _) -> L.progress "proc: %a@." Procname.pp proc) graph


(** alias set에서 자기 자신, this, ph, 직전 variable을 빼고 남은 program variable들을 리턴 *)
let collect_program_vars_from (aliases:A.t) (self:Var.t) (just_before:Var.t) : Var.t list =
  List.filter ~f:(fun x -> is_program_var x &&
                           not @@ Var.equal self x &&
                           not @@ Var.is_this x &&
                           not @@ is_placeholder_vardef x &&
                           not @@ Var.equal just_before x) (A.elements aliases)


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
let find_direct_caller (target_meth:Procname.t) (acc:chain) =
  let target_vertex = (target_meth, get_summary target_meth) in
  let rec find_direct_caller_inner (acc:chain) =
    match acc with
    | [] -> raise NoParent
    | (cand_meth, _) :: t ->
        let is_pred = fun v -> List.mem (G.pred callgraph target_vertex) v ~equal:equal_btw_vertices in
        let cand_vertex = (cand_meth, get_summary cand_meth) in
        if is_pred cand_vertex
        then cand_vertex
        else find_direct_caller_inner t in
  find_direct_caller_inner acc


(** 가 본 적이 있는지를 검사하는 술어. *)
(** NOTE: status 패턴 매칭 부분이 맞는지 잘 모르겠다.*)
let rec have_been_before (tuple:S.elt) (acc:chain) : bool =
  match acc with
  | [] -> false
  | (methname, status)::t ->
      let procname = first_of tuple in
      let vardef = second_of tuple in
      begin match status with
        | Define var ->
            if Procname.equal procname methname && Var.equal vardef var
            then true else have_been_before tuple t
        | Call (callee, var) -> (* 맞으려나? *)
            if (Procname.equal callee procname || Procname.equal callee methname) && Var.equal vardef var then true else have_been_before tuple t
        | Redefine var ->
            if Procname.equal procname methname && Var.equal vardef var
            then true else have_been_before tuple t
        | Dead ->
            have_been_before tuple t end


(** 가 본 적이 *없는* 튜플들만을 남긴다. *)
let filter_have_been_before (tuplelist:S.elt list) (current_chain:chain) =
  List.fold_left tuplelist ~init:[] ~f:(fun acc tup -> if not @@ have_been_before tup current_chain then tup::acc else acc)


(** 바로 다음의 successor들 중에서 파라미터를 들고 있는 함수를 찾아 낸다. 못 찾을 경우, Procname.empty_block을 내뱉는다. *)
let find_immediate_successor (current_methname:Procname.t) (current_astate:S.t) (param:Var.t) =
  let succs = G.succ callgraph (current_methname, current_astate) in
  let succ_meths_and_formals = List.map ~f:(fun (meth, _) -> (meth, get_formal_args meth)) succs in
  List.fold_left ~init:Procname.empty_block ~f:(fun acc (m, p) -> if List.mem p param ~equal:Var.equal then m else acc) succ_meths_and_formals


let pop (lst:'a list) : 'a option =
  match lst with
  | [] -> None
  | _ -> Some (List.nth_exn lst 0)


let extract_variable_from_chain_slice (slice:(Procname.t*status) option) : Var.t =
  match slice with
  | Some (_, status) ->
      begin match status with
      | Define var -> var
      | Call (_, var) -> var
      | Redefine var -> var
      | Dead -> L.progress "Extracting from Dead\n"; second_of bottuple end
  | None -> L.progress "Extracting from empty chain\n"; second_of bottuple


(** 콜 그래프와 분석 결과를 토대로 체인 (Define -> ... -> Dead)을 계산해 낸다 *)
let compute_chain (var:Var.t) : chain =
  let (first_methname, first_astate, first_tuple) =
    L.progress "Target Var: %a\n" Var.pp var ; (* outputs x *)
    find_first_occurrence_of var in
  let rec compute_chain_inner (current_methname:Procname.t) (current_astate:S.t) (current_tuple:S.elt) (current_chain:chain) : chain =
    let aliasset = fourth_of current_tuple in
    let vardef = second_of current_tuple in
    let just_before = extract_variable_from_chain_slice @@ pop current_chain in
    match collect_program_vars_from aliasset vardef just_before with
    | [] -> (* either redefinition or dead end *)
        let tuples = S.elements current_astate in
        let redefined_tuples = List.fold_left tuples ~init:[] ~f:(fun acc tup -> if Var.equal vardef @@ second_of tup then tup::acc else acc) in
        begin match redefined_tuples with
          | [] -> (* Dead end *) (current_methname, Dead) :: current_chain
          | _ -> (* Redefinition *)
              let future_tuples = S.diff current_astate @@ select_up_to current_tuple (remove_duplicates_from current_astate) in
              let new_tuple = find_earliest_tuple_of_var_within (S.elements future_tuples) vardef in
              let new_chain = (current_methname, Redefine vardef) :: current_chain in
              compute_chain_inner current_methname current_astate new_tuple new_chain end
    | [var] -> (* either definition or call *)
        if Var.is_return var
        then (* caller에서의 define *)
          let var_being_returned = find_var_being_returned aliasset in
          let (direct_caller, caller_summary) = find_direct_caller current_methname current_chain in
          let tuples_with_return_var = search_target_tuples_by_pvar var_being_returned direct_caller caller_summary in
          let new_tuple = find_earliest_tuple_within @@ filter_have_been_before tuples_with_return_var current_chain in
          let new_chain = (first_of new_tuple, Define (second_of new_tuple)) :: current_chain in
          compute_chain_inner direct_caller caller_summary new_tuple new_chain
        else (* 동일 procedure 내에서의 define 혹은 call *)
          (* 다음 튜플을 현재 procedure 내에서 찾을 수 있는지를 기준으로 경우 나누기 *)
          begin match search_target_tuples_by_vardef var current_methname current_astate with
          | [] -> (* Call *)
              let callee_methname = find_immediate_successor current_methname current_astate var in
              let new_tuples = search_target_tuples_by_vardef var callee_methname (get_summary callee_methname) in
              let new_tuple = find_earliest_tuple_within new_tuples in
              let new_chain = (current_methname, Call (callee_methname, var))::current_chain in
              compute_chain_inner callee_methname (get_summary callee_methname) new_tuple new_chain
          | nonempty_list -> (* 동일 proc에서의 Define *)
              let new_tuple = find_earliest_tuple_within nonempty_list in
              let new_chain = (current_methname, Define var)::current_chain in
              compute_chain_inner current_methname current_astate new_tuple new_chain end
    | _ -> raise UnexpectedSituation in
  List.rev @@ compute_chain_inner first_methname first_astate first_tuple []


let collect_all_vars () =
  let setofallstates =  Hashtbl.fold (fun _ v acc -> S.union v acc) summary_table S.empty in
  let listofallstates = S.elements setofallstates in
  let listofallvars = List.map ~f:second_of listofallstates in
  A.of_list listofallvars

let pp_status fmt x =
  match x with
  | Define var -> F.fprintf fmt "Defined as %a" Var.pp var
  | Call (proc, var) -> F.fprintf fmt "Called %a with parameter %a" Procname.pp proc Var.pp var
  | Redefine var -> F.fprintf fmt "Redefined to %a" Var.pp var
  | Dead -> F.fprintf fmt "Variable Dead"
 

let pp_pair fmt (proc, v) = F.fprintf fmt "(%a, %a)" Procname.pp proc pp_status v


let pp_chain fmt x = Pp.seq pp_pair fmt x


let to_string hashtbl =
  Hashtbl.fold (fun k v acc -> String.concat ~sep:"@." [acc; (F.asprintf "%a -> %a" Var.pp k pp_chain v)]) hashtbl ""


(** interface with the driver *)
let run_lrm () =
  MyCallGraph.load_summary_from_disk_to callgraph_table;
  load_summary_from_disk_to summary_table;
  filter_callgraph_table callgraph_table ;
  callg_hash2og ();
  print_graph callgraph;
  let setofallvars_with_garbage = collect_all_vars () in
  let setofallvars = A.filter (fun var -> not @@ Var.is_this var && not @@ is_placeholder_vardef var) setofallvars_with_garbage in
  (* A.iter (fun var -> L.progress "Var: %a\n" Var.pp var) setofallvars; *)
  A.iter (fun var -> add_chain var (compute_chain var)) setofallvars;
  let out_string = F.asprintf "%s" (to_string chains) in
  let ch = Out_channel.create "chain.txt" in
  Out_channel.output_string ch out_string;
  Out_channel.flush ch;
  Out_channel.close ch
