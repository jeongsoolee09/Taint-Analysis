open! IStd
open DefLocAliasSearches
open DefLocAliasLogicTests
open DefLocAliasDomain
open Yojson.Basic

module Hashtbl = Caml.Hashtbl
module P = DefLocAliasDomain.AbstractPair
module S = DefLocAliasDomain.AbstractStateSetFinite
module A = DefLocAliasDomain.SetofAliases
module T = DefLocAliasDomain.AbstractState
module L = Logging
module F = Format

exception TODO
exception IDontKnow

type status =
  | Define of (Procname.t * MyAccessPath.t)
  | Call of (Procname.t * MyAccessPath.t)
  | Redefine of MyAccessPath.t
  | Dead [@@deriving equal]

type json = Yojson.Basic.t

module Status = struct (* Status.equal 하나만을 위해 작성한 boilerplate ㅠㅠ *)
  type t = status [@@deriving equal]
end

type chain = (Procname.t * status) list

(* GOAL: x가 m2에서 u1으로 redefine되었고 m3 이후로 안 쓰인다는 chain 정보 계산하기
 * --> [(f, Define x), (f, Call (g, y)), (g, Call (m2, u1)), (m2, Redefine u1), (g, Define z), (g, Call (h, w)), (h, Call (m3, u2)), (m3, Dead)] *)

module type Stype = module type of S

(* Domain 과 Summary의 쌍 *)
module Pair (Domain1: Methname) (Domain2: Stype) = struct
  type t = Domain1.t * Domain2.t [@@deriving compare, equal]
end

(* Pair of Method and its Astate sets *)
module PairOfMS = struct
  include Pair (Procname) (S)
  type t = Procname.t * S.t
  let hash = Hashtbl.hash
end


let rec catMaybes_tuplist (optlist: ('a*'b option) list) : ('a*'b) list =
  match optlist with
  | [] -> []
  | (sth1, Some sth2) :: t -> (sth1, sth2)::catMaybes_tuplist t
  | (_, None) :: _ -> L.die InternalError "catMaybes_tuplist failed"


let pp_status fmt x =
  match x with
  | Define (proc, ap) -> F.fprintf fmt "Define (%a using %a)" MyAccessPath.pp ap Procname.pp proc
  | Call (proc, ap) -> F.fprintf fmt "Call (%a with %a)" Procname.pp proc MyAccessPath.pp ap
  | Redefine ap -> F.fprintf fmt "Redefine (%a)" MyAccessPath.pp ap
  | Dead -> F.fprintf fmt "Dead"


let pp_pair fmt (proc, v) = F.fprintf fmt "(%a, %a) ->" Procname.pp proc pp_status v

let pp_chain fmt x = Pp.seq pp_pair fmt x

let string_of_vertex (proc, astateset) = F.asprintf "\"(%a, %a)\"" Procname.pp proc S.pp astateset


module G = struct
  include Graph.Imperative.Digraph.ConcreteBidirectional (PairOfMS)
  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let vertex_name (vertex:V.t) : string =
    string_of_vertex vertex
  let vertex_attributes (_:V.t) = [`Shape `Box]
  let get_subgraph _ = None
  let default_edge_attributes _ = []
  let edge_attributes _ = []
end
module BFS = Graph.Traverse.Bfs (G)
module Dot = Graph.Graphviz.Dot (G)


(** map from procnames to their summaries. *)
let summary_table = Hashtbl.create 777


let get_summary (key: Procname.t) : S.t =
  try
    Hashtbl.find summary_table key
  with _ ->
    S.empty


let pp_summary_table fmt hashtbl : unit =
  Hashtbl.iter (fun k v ->
      F.fprintf fmt "%a -> %a\n" Procname.pp k S.pp v) hashtbl


(** Function for debugging by exporting Ocamlgraph to Graphviz Dot *)
let graph_to_dot (graph: G.t): unit =
  let out_channel = Out_channel.create "callgraph_with_astate.dot" in
  Dot.output_graph out_channel graph;
  Out_channel.flush out_channel;
  Out_channel.close out_channel


(** map from procname to its formal args. *)
let formal_args = Hashtbl.create 777

let batch_add_formal_args () =
  let procnames = Hashtbl.fold (fun k _ acc -> k::acc) summary_table [] in
  let pname_and_pdesc_opt = List.map ~f:(fun pname -> (pname, Procdesc.load pname)) procnames in
  let pname_and_pdesc = catMaybes_tuplist pname_and_pdesc_opt in
  let pname_and_params_with_type = List.map ~f:(fun (pname, pdesc) -> (pname, Procdesc.get_pvar_formals pdesc)) pname_and_pdesc in
  let pname_and_params = List.map ~f:(fun (pname, with_type_list) -> (pname,List.map ~f:(fun (a,_) -> Var.of_pvar a) with_type_list)) pname_and_params_with_type in
  List.iter pname_and_params ~f:(fun (pname, params) -> Hashtbl.add formal_args pname params)

let get_formal_args (key: Procname.t) = Hashtbl.find formal_args key

let batch_print_formal_args () =
  Hashtbl.iter (fun k v -> L.progress "procname: %a, " Procname.pp k;
                 L.progress "vars: ";
                 List.iter v ~f:(L.progress "%a, " Var.pp);
                 L.progress "\n") formal_args


(** a tabular representation of the call graph. *)
let callgraph_table = Hashtbl.create 777

let callgraph = G.create ()

let chains = Hashtbl.create 777

(** Procname과 AP로부터 chain으로 가는 Hash table *)
let add_chain (key: (Procname.t * MyAccessPath.t)) (value: chain) = Hashtbl.add chains key value

(** 주어진 var이 formal arg인지 검사하고, 맞다면 procname과 formal arg의 리스트를 리턴 *)
let find_procpair_by_var (var: Var.t) =
  let key_values = Hashtbl.fold (fun k v acc -> (k, v)::acc) formal_args [] in
  List.fold_left key_values ~init:[] ~f:(fun acc ((_, varlist) as target) -> if List.mem varlist var ~equal:Var.equal then target::acc else acc)


let pp_tuplelistlist fmt (lstlst: T.t list list) =
  F.fprintf fmt "[";
  List.iter ~f:(fun lst -> pp_tuplelist fmt lst) lstlst;
  F.fprintf fmt "]"


(** 중복 튜플을 제거함 *)
let remove_duplicates_from (astate_set: S.t) : S.t =
  let partitioned_by_duplicates = P.partition_tuples_modulo_123 astate_set in
  (* 위의 리스트 안의 각 리스트들 안에 들어 있는 튜플들 중 가장 alias set이 큰 놈을 남김 *)
  let leave_tuple_with_biggest_aliasset = fun lst ->
    if (List.length lst) > 1
    then
      List.fold_left lst
        ~init:bottuple
        ~f:(fun (acc:T.t) (elem:T.t) ->
            if (A.cardinal @@ fourth_of acc) < (A.cardinal @@ fourth_of elem)
            then elem
            else acc)
    else
      List.nth_exn lst 0 in
  let result = S.of_list @@ List.map ~f:leave_tuple_with_biggest_aliasset partitioned_by_duplicates in
  S.filter
    (fun tup ->
       let var, _ = second_of tup in
       not @@ is_placeholder_vardef var && not @@ Var.is_this var) result


(** 해시 테이블 형태의 콜그래프를 ocamlgraph로 변환한다. *)
let callg_hash2og () : unit =
  let filterfunc = fun tup ->
    let var, _ = second_of tup in
    not @@ is_placeholder_vardef var &&
    not @@ is_logical_var var &&
    not @@ is_frontend_tmp_var var in
  Hashtbl.iter (fun key value ->
      let key_astate_set = S.filter filterfunc @@ get_summary key in
      let value_astate_set = S.filter filterfunc @@  get_summary value in
      G.add_edge callgraph (key, key_astate_set) (value, value_astate_set)) callgraph_table


(** 주어진 hashtbl의 엔트리 중에서 (callgraph_table이 쓰일 것) summary_table에 있지 않은 엔트리를 날린다. *)
let filter_callgraph_table hashtbl : unit =
  let procs = Hashtbl.fold (fun k _ acc -> k::acc) summary_table [] in
  Hashtbl.iter (fun k v ->
      if not @@ List.mem procs k ~equal:Procname.equal &&
         not @@ List.mem procs v ~equal:Procname.equal
      then Hashtbl.remove hashtbl k
      else ()) hashtbl


(** specially mangled variable to mark a value as returned from callee *)
let mk_returnv procname =
  Var.of_pvar @@ Pvar.mk (Mangled.from_string "returnv") procname


(** 주어진 AccessPath ap에 있어 가장 이른 정의 state를 찾는다. *)
let find_first_occurrence_of (ap: MyAccessPath.t) : Procname.t * S.t * S.elt =
  let astate_set = BFS.fold (fun (_, astate) acc ->
      match S.exists (fun tup -> MyAccessPath.equal (second_of tup) ap) astate with
      | true -> astate
      | false -> acc) S.empty callgraph in
  match S.elements astate_set with
  | [] -> (Procname.empty_block, S.empty, bottuple) (* probably clinit *)
  | _ ->
      let astate_set_nodup = remove_duplicates_from astate_set in
      let elements = S.elements astate_set_nodup in
      let methname = first_of @@ (List.nth_exn elements 0) in
      let targetTuples = search_target_tuples_by_vardef_ap ap methname astate_set_nodup in
      let earliest_state = find_earliest_astate_within targetTuples methname in
      (methname, astate_set, earliest_state)


(** 디버깅 용도로 BFS 사용해서 그래프 출력하기 *)
let print_graph graph = BFS.iter (fun (proc, _) -> L.progress "proc: %a@." Procname.pp proc) graph


(** alias set에서 자기 자신, ph, 직전 variable을 빼고 남은 program variable들을 리턴 *)
let collect_program_var_aps_from
    (aliasset: A.t)
    ~(self: MyAccessPath.t)
    ~(just_before: MyAccessPath.t) : MyAccessPath.t list =
  List.filter ~f:(fun x -> is_program_var (fst x) &&
                           not @@ MyAccessPath.equal self x &&
                           (* not @@ Var.is_this (fst x) && *)
                           not @@ is_placeholder_vardef (fst x) &&
                           not @@ MyAccessPath.equal just_before x) @@ A.elements aliasset


let select_up_to (state: S.elt) ~(within: S.t) : S.t =
  let astates = S.elements within in
  let select_up_to_inner (astate:S.elt) : S.t =
    S.of_list @@ List.fold_left astates ~init:[]
      ~f:(fun (acc:T.t list) (elem:T.t) ->
          if third_of elem => third_of astate then elem::acc else acc) in
  select_up_to_inner state


let equal_btw_vertices : PairOfMS.t -> PairOfMS.t -> bool =
  fun (m1, s1) (m2, s2) -> Procname.equal m1 m2 && S.equal s1 s2


(** callgraph 상에서, 혹은 accumulator를 따라가면서 최초의 parent (즉, 직전의 caller)와 그 astate_set을 찾아낸다. *)
let find_direct_caller (target_meth: Procname.t) (acc: chain) : Procname.t * S.t =
  let target_vertex = (target_meth, get_summary target_meth) in
  let parents = G.pred callgraph target_vertex in
  let rec find_direct_caller_inner (initial:chain) (acc:chain) =
    match acc with
    | [] -> L.die InternalError "find_direct_caller failed (1), target_meth: %a, acc: %a@." Procname.pp target_meth pp_chain initial
    | (cand_meth, _) :: t ->
        let is_pred = fun v -> List.mem parents v ~equal:equal_btw_vertices in
        let cand_vertex = (cand_meth, get_summary cand_meth) in
        if is_pred cand_vertex
        then cand_vertex
        else find_direct_caller_inner initial t in
  match parents with
  | [] -> L.die InternalError "find_direct_caller failed (2), target_meth: %a, acc: %a@." Procname.pp target_meth pp_chain acc
  | [parent_and_astateset] -> parent_and_astateset
  | _ -> find_direct_caller_inner acc acc


(** 가 본 적이 있는지를 검사하는 술어. *)
(** NOTE: status 패턴 매칭 부분이 맞는지 잘 모르겠다.*)
let rec have_been_before (astate: S.elt) (acc: chain) : bool =
  match acc with
  | [] -> false
  | (methname, status) :: t ->
      let procname = first_of astate in
      let vardef = second_of astate in
      begin match status with
        | Define (_, ap) ->
            if Procname.equal procname methname && MyAccessPath.equal vardef ap
            then true else have_been_before astate t
        | Call (callee, ap) -> (* 맞으려나? *)
            if (Procname.equal callee procname || Procname.equal callee methname) && MyAccessPath.equal vardef ap then true else have_been_before astate t
        | Redefine ap ->
            if Procname.equal procname methname && MyAccessPath.equal vardef ap
            then true
            else have_been_before astate t
        | Dead ->
            have_been_before astate t end


(** 가 본 적이 있는 튜플들을 없앰으로써, 가 본 적이 *없는* 튜플들만을 남긴다. *)
let filter_have_been_before (tuplelist: S.elt list) (current_chain: chain) =
  List.fold_left tuplelist ~init:[]
    ~f:(fun acc tup ->
        if not @@ have_been_before tup current_chain then tup::acc else acc)


let pp_pairofms fmt (proc, summ) =
  F.fprintf fmt "(";
  F.fprintf fmt "%a, %a" Procname.pp proc S.pp summ;
  F.fprintf fmt ")"


let pp_pairofms_list list =
  List.iter ~f:(fun x -> L.progress "%a@." pp_pairofms x) list


let pp_ap_list list =
  L.progress "[";
  List.iter ~f:(fun ap -> L.progress "%a\n" MyAccessPath.pp ap) list;
  L.progress "]"


(** get_formal_args는 skip_function에 대해 실패한다는 점을 이용한 predicate *)
let is_skip_function (methname: Procname.t) : bool =
  Option.is_none @@ Procdesc.load methname


let save_skip_function () : unit =
  let procnames = Hashtbl.fold (fun meth1 meth2 acc ->
      let meth1_is_skip = is_skip_function meth1 in
      let meth2_is_skip = is_skip_function meth2 in
      match meth1_is_skip, meth2_is_skip with
      | true, true -> Procname.Set.add meth1 acc |> Procname.Set.add meth2
      | true, false -> Procname.Set.add meth1 acc
      | false, true -> Procname.Set.add meth2 acc
      | false, false -> acc) callgraph_table Procname.Set.empty in
  let out_chan = Out_channel.create "skip_func.txt" in
  let procnames_list = Procname.Set.elements procnames in
  List.iter ~f:(fun procname ->
      let func_name = Procname.to_string procname in
      Out_channel.output_string out_chan @@ func_name^"\n") procnames_list


(** returnv 혹은 callv 안에 들어 있는 callee method name을 뽑아 낸다. *)
let extract_callee_from (ap: MyAccessPath.t) =
  let special, _ = ap in
  match special with
  | LogicalVar _ -> L.die InternalError "extract_callee_from failed"
  | ProgramVar pv ->
      begin match Pvar.get_declaring_function pv with
        | Some procname -> procname
        | None -> L.die InternalError "extract_callee_from failed" end


(** 바로 다음의 successor들 중에서 파라미터를 들고 있는 함수를 찾아 낸다. 못 찾을 경우, Procname.empty_block을 내뱉는다. *)
let find_immediate_successor (current_methname: Procname.t) (current_astate_set: S.t) (param: MyAccessPath.t) =
  let succs = G.succ callgraph (current_methname, current_astate_set) in
  (* let not_skip_succs = List.filter ~f:(fun (proc, _) -> not @@ is_skip_function proc) succs in *)
  let succ_meths_and_formals = List.map ~f:(fun (meth, _) -> (meth, get_formal_args meth)) succs (*not_skip_succs*) in
  List.fold_left ~init:Procname.empty_block ~f:(fun acc (m, p) ->
      if List.mem p (fst param) ~equal:Var.equal then m else acc) succ_meths_and_formals


let extract_ap_from_chain_slice (slice: (Procname.t*status) option) : MyAccessPath.t =
  match slice with
  | Some (_, status) ->
      begin match status with
        | Define (_, ap) -> ap
        | Call (_, ap) -> ap
        | Redefine ap -> ap
        | Dead -> second_of bottuple end
  | None -> second_of bottuple


let remove_from_aliasset ~(from:T.t) ~remove:var =
  let (a, b, c, aliasset) = from in
  let aliasset' = A.remove var aliasset in
  (a, b, c, aliasset')


let procname_of (ap:A.elt) : Procname.t =
  let var, _ = ap in
  match var with
  | ProgramVar pv ->
      begin match Pvar.get_declaring_function pv with
        | Some proc -> proc
        | _ -> L.die InternalError "procname_of failed, ap: %a@." MyAccessPath.pp ap end
  | LogicalVar _ -> L.die InternalError "procname_of failed, ap: %a@." MyAccessPath.pp ap


(** chain_slice 끼리의 equal *)
let double_equal ((methname1, status1): (Procname.t * status))
    ((methname2, status2): (Procname.t*status)) : bool =
  Procname.equal methname1 methname2 && Status.equal status1 status2


(** 주어진 (methname, status)가 chain의 일부분인지를 확인한다. *)
let is_contained_in_chain (chain_slice: Procname.t * status) (chain: chain) =
  List.mem chain chain_slice ~equal:double_equal


(** chain_slice가 chain 안에 들어 있다는 전제 하에 그 index를 찾아 냄 *)
let elem_is_at (chain: chain) (chain_slice: Procname.t * status) : int =
  List.fold ~f:(fun acc elem -> if double_equal chain_slice elem then acc+1 else acc) ~init:0 chain


(** -1을 리턴할 수도 있게끔 elem_is_at을 포장 *)
let find_index_in_chain (chain: chain) (chain_slice: Procname.t * status) : int =
  match is_contained_in_chain chain_slice chain with
  | true -> elem_is_at chain chain_slice
  | false -> -1


(** chain과 chain_slice를 받아, chain_slice가 있는 지점부터 시작되는 subchain을 꺼내 온다. 실패하면 empty list. *)
let extract_subchain_from (chain: chain) (chain_slice: Procname.t * status) : chain =
  let index = find_index_in_chain chain chain_slice in
  match index with
  | -1 -> []
  | _ ->
      let subchain_length = List.length chain - index in
      List.sub chain ~pos:index ~len:subchain_length


(** returnv가 들어 있는 aliasset을 받아서, 그 안에 callee로부터 carry over된 var가 있다면 날린다. returnv는 무조건 날린다. *)
let filter_carrriedover_ap (aliasset: A.t) : A.t =
  if not @@ List.exists ~f:is_returnv_ap (A.elements aliasset) then aliasset else
    let returnv_ap = List.find_exn (A.elements aliasset) ~f:is_returnv_ap in
    let callee_methname = extract_callee_from returnv_ap in
    let callee_astate_set = get_summary callee_methname in
    (* astate_set 안에서 aliasset 안에 returnv가 들어 있는 astate 찾기 *)
    let astate_with_return = S.fold (fun astate acc ->
        let aliasset = fourth_of astate in
        if A.exists is_return_ap aliasset
        then astate::acc
        else acc) callee_astate_set [] in
    match astate_with_return with
    | [] -> (* Skip_function으로, summary가 없는 경우이다. -> 아무것도 할 것 없이 returnv만 날려 준다. *)
        A.remove returnv_ap aliasset
    | statelist -> (* return 지점이 여러 개인 method로, 제거 대상이 여러 개이다. *)
        let aps_to_remove = A.of_list @@ List.map ~f:second_of statelist in
        A.remove returnv_ap @@ A.diff aliasset aps_to_remove


(** pvar가 여러 개 있는 aliasset 내에서 관련 없는 pvar들을 (하나 남기고) 모두 없앰 *)
let cleanup_aliasset (aliasset: A.t) (self: MyAccessPath.t) : A.t =
  let carried_over_ap_filtered = filter_carrriedover_ap aliasset in
  let self_filtered = A.remove self carried_over_ap_filtered in
  let aliasset_filtered = A.filter (fun (var, _) ->
      (not @@ is_logical_var var &&
       not @@ is_frontend_tmp_var var)) self_filtered in
  aliasset_filtered


(** Define에 들어 있는 Procname과 AP의 쌍을 받아서 그것이 들어 있는 chain을 리턴 *)
let find_entry_containing_chainslice (methname: Procname.t) (status: status) : chain option =
  let all_chains = Hashtbl.fold (fun _ v acc -> v::acc) chains [] in
  let result_chains = List.fold ~f:(fun acc chain ->
      if is_contained_in_chain (methname, status) chain
      then chain::acc
      else acc) ~init:[] all_chains in
  List.nth result_chains 0


let mk_noparam (procname: Procname.t) : A.elt =
  let noparam = Var.of_pvar @@ Pvar.mk (Mangled.from_string "noparam") procname in
  (noparam, [])


(** callee가 astate_set이 없는 skip_function일 때, caller의 returnv 중 skip_function의 methname이 있는 것이 있는지 확인하고, 그에 맞게 다음 chain 조각을 만듦 *)
let handle_empty_astateset (caller_methname: Procname.t) (caller_astate_set: S.t)
    (skip_function: Procname.t) : chain =
  (* 일단 이 안에 있는 returnv를 전부 골라내야 함 *)
  let collect_all_returnv (astate_set:S.t) : A.elt list =
    let astate_list = S.elements astate_set in
    let aliasset_list = List.map ~f:fourth_of astate_list in
    let filtered_aliasset_list =
      List.map ~f:(A.filter (fun (var, _) -> is_returnv var)) aliasset_list in
    List.fold ~f:(fun acc set ->
        if Int.equal (A.cardinal set) 1
        then (extract_from_singleton set)::acc
        else acc) ~init:[] filtered_aliasset_list in
  let returnv_list = collect_all_returnv caller_astate_set in
  (* 경우에 따라 returnv를 가진 튜플이 여러 개일 수 있음 *)
  let target_returnv_list = List.fold ~f:(fun acc returnv -> if Procname.equal (extract_callee_from returnv) skip_function then returnv::acc else acc) ~init:[] returnv_list in
  let returnv = List.nth target_returnv_list 0 in
  match returnv with
  (* 가정된 invariant: caller 내에서 callee는 한 번만 불렸다 *)
  | None -> (* Data flow가 다시 caller에게로 돌아오지 않음: unsound하게 판단 *)
      List.rev [(caller_methname, Call (skip_function, mk_noparam skip_function)); (skip_function, Dead)]
  | Some rv ->
      (* returnv를 가진 튜플이 우리가 원하는 것 외에도 많을 수 있지만, MyAccessPath.equal을 사용하므로 상관없음 *)
      let var_defined_in_caller = second_of @@ search_target_tuple_by_pvar_ap rv caller_methname caller_astate_set in
      List.rev [(caller_methname, Call (skip_function, mk_noparam skip_function)); (caller_methname, Define (skip_function, var_defined_in_caller))]


let is_carriedover_ap (ap: A.elt) (current_methname: Procname.t) (current_astate_set: S.t) : bool =
  let callee_nodes = G.succ callgraph (current_methname, current_astate_set) in
  (* 주어진 ap가 callee의 astate_set 중에서 return이랑 alias가 있는 튜플이 있는지 확인 *)
  List.fold ~f:(fun acc (proc, astate_set) ->
      match search_target_tuples_by_vardef_ap ap proc astate_set with
      | [] -> acc
      | tuples -> List.fold ~f:(fun _ elem ->
          let aliasset = fourth_of elem in
          A.exists is_returnv_ap aliasset) ~init:false tuples)
    ~init:false callee_nodes


let rec compute_chain_inner (current_methname: Procname.t) (current_astate_set: S.t)
    (current_astate: S.elt) (current_chain: chain) (retry: int): chain =
  (* We need to leverage the information provided by *callv* and *returnv*! *)
  let current_aliasset_cleanedup = A.filter (fun tup ->
      not @@ is_logical_var @@ fst tup &&
      not @@ is_frontend_tmp_var @@ fst tup)
    @@ fourth_of current_astate in
  let current_vardef = second_of current_astate in
  (* 직전에 방문했던 astate에서 끄집어낸 variable *)
  let just_before = extract_ap_from_chain_slice @@ List.hd current_chain in
  match collect_program_var_aps_from current_aliasset_cleanedup
          ~self:current_vardef ~just_before:just_before with
  | [] -> (* either redefinition or dead end *) raise TODO
  | otherwise -> raise TODO


(** 콜 그래프와 분석 결과를 토대로 체인 (Define -> ... -> Dead)을 계산해 낸다 *)
let compute_chain_ (ap: MyAccessPath.t) : chain =
  let (first_methname, first_astate_set, first_astate) = find_first_occurrence_of ap in
  let first_aliasset = fourth_of first_astate in
  let returnv_opt = A.find_first_opt is_returnv_ap first_aliasset in
  let source_meth = match returnv_opt with
    | Some returnv -> procname_of returnv
    | None -> first_methname in
  List.rev @@ compute_chain_inner first_methname first_astate_set
    first_astate [(first_methname, Define (source_meth, ap))] 3


(** 본체인 compute_chain_을 포장하는 함수 *)
let compute_chain (ap: MyAccessPath.t) : chain =
  let (first_methname, _, first_astate) = find_first_occurrence_of ap in
  if Procname.equal first_methname Procname.empty_block then [] else
    let first_aliasset = fourth_of first_astate in
    match A.exists is_returnv_ap first_aliasset with
    | true -> (* 이미 어떤 chain의 subchain이라면 새로 계산할 필요 없음 *)
        let initial_chain_slice = Define (first_methname, ap) in
        begin match find_entry_containing_chainslice first_methname initial_chain_slice with
          | None -> (* 이전에 계산해 놓은 게 없네 *)
              compute_chain_ ap
          | Some chain -> (* 이전에 계산해 놓은 게 있네! 거기서 단순 추출만 해야지 *)
              extract_subchain_from chain (first_methname, initial_chain_slice) end
    | false ->
        compute_chain_ ap


let collect_all_proc_and_ap () =
  let setofallstates = Hashtbl.fold (fun _ v acc -> S.union v acc) summary_table S.empty in
  let listofallstates = S.elements setofallstates in
  let list_of_all_proc_and_ap = List.map ~f:(fun (x:T.t) -> (first_of x, second_of x)) listofallstates in
  list_of_all_proc_and_ap


(** chains 해시 테이블 전체를 프린트한다 *)
let chains_to_string hashtbl =
  Hashtbl.fold (fun (proc, ap) v acc ->
      String.concat ~sep:"\n" [acc; (F.asprintf "(%a, %a): %a"
                                       Procname.pp proc
                                       MyAccessPath.pp ap pp_chain v)])
    hashtbl ""


(** 파일로 call graph를 출력 *)
let save_callgraph () =
  let ch = Out_channel.create "Callgraph.txt" in
  Hashtbl.iter (fun k v ->
      Out_channel.output_string ch @@ (Procname.to_string k)^" -> "^(Procname.to_string v^"\n")) callgraph_table;
  Out_channel.flush ch;
  Out_channel.close ch


let extract_pvar_from_var (var: Var.t) : Pvar.t =
  match var with
  | LogicalVar _ -> L.die InternalError "extract_pvar_from_var failed, var: %a@." Var.pp var
  | ProgramVar pv -> pv


(* Method for Jsons ======================== *)
(* ========================================= *)


(** 하나의 status에 대한 representation을 만든다. *)
let represent_status (current_method: Procname.t) (status: status) : json =
  match status with
  | Define (callee, ap) ->
      `Assoc [("current_method", `String (Procname.to_string current_method));
              ("status", `String "Define");
              ("access_path", `String (MyAccessPath.to_string ap));
              ("using", `String (Procname.to_string callee))]
  | Call (callee, ap) ->
      `Assoc [("current_method", `String (Procname.to_string current_method));
              ("status", `String "Call");
              ("callee", `String (Procname.to_string callee));
              ("with", `String (MyAccessPath.to_string ap))]
  | Redefine ap ->
      `Assoc [("current_method", `String (Procname.to_string current_method));
              ("status", `String "Redefine");
              ("access_path", `String (MyAccessPath.to_string ap))]
  | Dead ->
      `Assoc [("current_method", `String (Procname.to_string current_method));
              ("status", `String "Dead")]


(** chain을 수식해서 ap에 관한 완전한 정보를 나타내는 Json object를 만든다. *)
let wrap_chain_representation defining_method ap (chain_repr: json list) : json =
  `Assoc [("defining_method", `String (Procname.to_string defining_method));
          ("access_path", `String (MyAccessPath.to_string ap));
          ("chain", `List chain_repr)]


(** 수식된 chain들의 array를 만든다. *)
let make_complete_representation (wrapped_chains: json list) : json =
  `List wrapped_chains


let write_json (json: json) : unit =
  let out_channel = Out_channel.create "Chain.json" in
  pretty_to_channel out_channel json;
  Out_channel.flush out_channel;
  Out_channel.close out_channel


(* Main Method ============================= *)
(* ========================================= *)


(** interface with the driver *)
let main () =
  MyCallGraph.load_callgraph_from_disk_to callgraph_table;
  save_callgraph ();
  SummaryLoader.load_summary_from_disk_to summary_table;
  batch_add_formal_args ();
  filter_callgraph_table callgraph_table;
  save_skip_function ();
  callg_hash2og ();
  graph_to_dot callgraph;
  (* List.stable_dedup @@ collect_all_proc_and_ap ()
   * |> List.filter ~f:(fun (_, (var, _)) ->
   *     let pv = extract_pvar_from_var var in
   *     not @@ Var.is_this var &&
   *     not @@ is_placeholder_vardef var &&
   *     not @@ Pvar.is_frontend_tmp pv)
   * |> List.iter ~f:(fun (proc, ap) ->
   *     add_chain (proc, ap) (compute_chain ap));
   * let wrapped_chains = Hashtbl.fold (fun (current_meth, target_ap) chain acc ->
   *     wrap_chain_representation current_meth target_ap (List.map ~f:(fun (proc, status) ->
   *         represent_status proc status) chain)::acc) chains [] in
   * let complete_json_representation = make_complete_representation wrapped_chains in
   * write_json complete_json_representation *)
