open! IStd
open DefLocAlias.TransferFunctions
open DefLocAliasSearches
open DefLocAliasLogicTests
open DefLocAliasDomain

module Hashtbl = Caml.Hashtbl
module P = DefLocAliasDomain.AbstractPair
module S = DefLocAliasDomain.AbstractStateSetFinite
module A = DefLocAliasDomain.SetofAliases
module T = DefLocAliasDomain.AbstractState
module L = Logging
module F = Format

exception NotImplemented
exception IDontKnow

type status =
  | Define of (Procname.t * MyAccessPath.t)
  | Call of (Procname.t * MyAccessPath.t)
  | Redefine of MyAccessPath.t
  | Dead [@@deriving equal]

module Status = struct (* Status.equal 하나만을 위해 작성한 boilerplate ㅠㅠ *)
  type t = status [@@deriving equal]
end

type chain = (Procname.t * status) list

(* GOAL: x가 m2에서 u1으로 redefine되었고 m3 이후로 안 쓰인다는 chain 정보 계산하기
 * --> [(f, Define x), (f, Call (g, y)), (g, Call (m2, u1)), (m2, Redefine u1), (g, Define z), (g, Call (h, w)), (h, Call (m3, u2)), (m3, Dead)] *)
(* TODO: Var.t를 Var.t의 해시값으로 바꾸기 *)

module type Stype = module type of S

(* Domain 과 Summary의 쌍 *)
module Pair (Domain1:Methname) (Domain2:Stype) = struct
  type t = Domain1.t * Domain2.t [@@deriving compare, equal]
end

module PairOfMS = struct
  include Pair (Procname) (S)
  type t = Procname.t * S.t
  let hash = Hashtbl.hash
end


let pp_status fmt x =
  match x with
  | Define (proc, ap) -> F.fprintf fmt "Define (%a using %a)" MyAccessPath.pp ap Procname.pp proc
  | Call (proc, ap) -> F.fprintf fmt "Call (%a with %a)" Procname.pp proc MyAccessPath.pp ap
  | Redefine ap -> F.fprintf fmt "Redefine (%a)" MyAccessPath.pp ap
  | Dead -> F.fprintf fmt "Dead"
 

let pp_pair fmt (proc, v) = F.fprintf fmt "(%a, %a) ->" Procname.pp proc pp_status v


let pp_chain fmt x = Pp.seq pp_pair fmt x
module G = Graph.Imperative.Digraph.ConcreteBidirectional (PairOfMS)


module BFS = Graph.Traverse.Bfs (G)

(** map from procnames to their summaries. *)
let summary_table = Hashtbl.create 777

let get_summary (key:Procname.t) : S.t =
  try
    Hashtbl.find summary_table key
  with _ ->
    S.empty


let pp_summary_table fmt hashtbl : unit =
  Hashtbl.iter (fun k v ->
      F.fprintf fmt "%a -> %a\n" Procname.pp k S.pp v) hashtbl


(** map from procname to its formal args. *)
let formal_args = Hashtbl.create 777

let batch_add_formal_args () =
  let procnames = Hashtbl.fold (fun k _ acc -> k::acc) summary_table [] in
  let pname_and_pdesc_opt = List.map ~f:(fun pname -> (pname, Procdesc.load pname)) procnames in
  let pname_and_pdesc = catMaybes_tuplist pname_and_pdesc_opt in
  let pname_and_params_with_type = List.map ~f:(fun (pname, pdesc) -> (pname, Procdesc.get_pvar_formals pdesc)) pname_and_pdesc in
  let pname_and_params = List.map ~f:(fun (pname, with_type_list) -> (pname,List.map ~f:(fun (a,_) -> Var.of_pvar a) with_type_list)) pname_and_params_with_type in
  List.iter pname_and_params ~f:(fun (pname, params) -> Hashtbl.add formal_args pname params)

let get_formal_args (key:Procname.t) = Hashtbl.find formal_args key

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
let add_chain (key:(Procname.t * MyAccessPath.t)) (value:chain) = Hashtbl.add chains key value

(** 주어진 var이 formal arg인지 검사하고, 맞다면 procname과 formal arg의 리스트를 리턴 *)
let find_procpair_by_var (var:Var.t) =
  let key_values = Hashtbl.fold (fun k v acc -> (k, v)::acc) formal_args [] in
  List.fold_left key_values ~init:[] ~f:(fun acc ((_, varlist) as target) -> if List.mem varlist var ~equal:Var.equal then target::acc else acc)


let pp_tuplelistlist fmt (lstlst:T.t list list) =
  F.fprintf fmt "[";
  List.iter ~f:(fun lst -> pp_tuplelist fmt lst) lstlst;
  F.fprintf fmt "]"


(** 중복 튜플을 제거함 *)
let remove_duplicates_from (astate_set:S.t) : S.t =
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
  Hashtbl.iter (fun key value ->
    G.add_edge callgraph (key, get_summary key) (value, get_summary value)) callgraph_table


let filter_callgraph_table hashtbl =
  let procs = Hashtbl.fold (fun k _ acc -> k::acc) summary_table [] in
  Hashtbl.iter (fun k v ->
      if not @@ List.mem procs k ~equal:Procname.equal ||
         not @@ List.mem procs v ~equal:Procname.equal
      then Hashtbl.remove hashtbl k
      else ()) hashtbl


(** 주어진 AccessPath ap에 있어 가장 이른 정의 state를 찾는다. *)
let find_first_occurrence_of (ap:MyAccessPath.t) : Procname.t * S.t * S.elt =
  let astate_set = BFS.fold (fun (_, astate) acc ->
      match S.exists (fun tup -> MyAccessPath.equal (second_of tup) ap) astate with
      | true -> (*L.progress "found it!\n";*) astate
      | false -> (*L.progress "nah..:(\n";*) acc) S.empty callgraph in
  (* L.progress "astate_set with dup: %a@." S.pp astate_set; *)
  let astate_set_nodup = remove_duplicates_from astate_set in
  (* L.progress "astate_set without dup: %a@." S.pp astate_set_nodup; *)
  let elements = S.elements astate_set_nodup in
  let methname = first_of @@ (List.nth_exn elements 0) in
  let targetTuples = search_target_tuples_by_vardef_ap ap methname astate_set_nodup in
  let earliest_state = find_earliest_astate_within targetTuples in
  (methname, astate_set, earliest_state)


(** 디버깅 용도로 BFS 사용해서 그래프 출력하기 *)
let print_graph graph = BFS.iter (fun (proc, _) -> L.progress "proc: %a@." Procname.pp proc) graph


(** alias set에서 자기 자신, this, ph, 직전 variable을 빼고 남은 program variable들을 리턴 *)
let collect_program_var_aps_from (aliases:A.t) (self:MyAccessPath.t) (just_before:MyAccessPath.t) : MyAccessPath.t list =
  List.filter ~f:(fun x -> is_program_var (fst x) &&
                           not @@ MyAccessPath.equal self x &&
                           not @@ Var.is_this (fst x) &&
                           not @@ is_placeholder_vardef (fst x) &&
                           not @@ MyAccessPath.equal just_before x) (A.elements aliases)


let select_up_to (state:S.elt) ~within:(astate_set:S.t) : S.t =
  let astates = S.elements astate_set in
  let select_up_to_inner (astate:S.elt) : S.t =
    S.of_list @@ List.fold_left astates ~init:[] ~f:(fun (acc:T.t list) (elem:T.t) -> if third_of elem => third_of astate then elem::acc else acc) in
  select_up_to_inner state


let equal_btw_vertices : PairOfMS.t -> PairOfMS.t -> bool =
  fun (m1, s1) (m2, s2) -> Procname.equal m1 m2 && S.equal s1 s2


(** callgraph 상에서, 혹은 accumulator를 따라가면서 최초의 parent (즉, 직전의 caller)와 그 astate_set을 찾아낸다. *)
let find_direct_caller (target_meth:Procname.t) (acc:chain) : Procname.t * S.t =
  let target_vertex = (target_meth, get_summary target_meth) in
  let parents = G.pred callgraph target_vertex in
  let rec find_direct_caller_inner (acc:chain) =
    match acc with
    | [] -> L.die InternalError "find_direct_caller failed, target_meth: %a, acc: %a@." Procname.pp target_meth pp_chain acc
    | (cand_meth, _) :: t ->
        let is_pred = fun v -> List.mem parents v ~equal:equal_btw_vertices in
        let cand_vertex = (cand_meth, get_summary cand_meth) in
        if is_pred cand_vertex
        then cand_vertex
        else find_direct_caller_inner t in
  match parents with
  | [] -> L.die InternalError "find_direct_caller failed, target_meth: %a, acc: %a@." Procname.pp target_meth pp_chain acc
  | [parent_and_astateset] -> parent_and_astateset
  | _ -> find_direct_caller_inner acc


(** 가 본 적이 있는지를 검사하는 술어. *)
(** NOTE: status 패턴 매칭 부분이 맞는지 잘 모르겠다.*)
let rec have_been_before (astate:S.elt) (acc:chain) : bool =
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


(** 가 본 적이 *없는* 튜플들만을 남긴다. *)
let filter_have_been_before (tuplelist:S.elt list) (current_chain:chain) =
  List.fold_left tuplelist ~init:[] ~f:(fun acc tup -> if not @@ have_been_before tup current_chain then tup::acc else acc)


(** 바로 다음의 successor들 중에서 파라미터를 들고 있는 함수를 찾아 낸다. 못 찾을 경우, Procname.empty_block을 내뱉는다. *)
let find_immediate_successor (current_methname:Procname.t) (current_astate:S.t) (param:MyAccessPath.t) =
  let succs = G.succ callgraph (current_methname, current_astate) in
  let succ_meths_and_formals = List.map ~f:(fun (meth, _) -> (meth, get_formal_args meth)) succs in
  List.fold_left ~init:Procname.empty_block ~f:(fun acc (m, p) ->
    if List.mem p (fst param) ~equal:Var.equal
    then m
    else acc) succ_meths_and_formals


let pop (lst:'a list) : 'a option =
  match lst with
  | [] -> None
  | _ -> Some (List.nth_exn lst 0)


let extract_ap_from_chain_slice (slice:(Procname.t*status) option) : MyAccessPath.t =
  match slice with
  | Some (_, status) ->
      begin match status with
      | Define (_, ap) -> ap
      | Call (_, ap) -> ap
      | Redefine ap -> ap
      | Dead -> (* L.progress "Extracting from Dead\n"; *) second_of bottuple end
  | None -> (* L.progress "Extracting from empty chain\n"; *) second_of bottuple


let remove_from_aliasset ~from:(astate:T.t) ~remove:var =
  let (a, b, c, aliasset) = astate in
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
let double_equal ((methname1, status1):(Procname.t*status)) ((methname2, status2):(Procname.t*status)) : bool =
  Procname.equal methname1 methname2 && Status.equal status1 status2


(** 주어진 (methname, status)가 chain의 일부분인지를 확인한다. *)
let is_contained_in_chain (chain_slice:Procname.t * status) (chain:chain) =
  List.mem chain chain_slice ~equal:double_equal


(** chain_slice가 chain 안에 들어 있다는 전제 하에 그 index를 찾아 냄 *)
let elem_is_at (chain:chain) (chain_slice:Procname.t * status) : int =
  List.fold ~f:(fun acc elem -> if double_equal chain_slice elem then acc+1 else acc) ~init:0 chain


(** -1을 리턴할 수도 있게끔 elem_is_at을 포장 *)
let find_index_in_chain (chain:chain) (chain_slice:Procname.t * status) : int =
  match is_contained_in_chain chain_slice chain with
  | true -> elem_is_at chain chain_slice
  | false -> -1


(** chain과 chain_slice를 받아, chain_slice가 있는 지점부터 시작되는 subchain을 꺼내 온다. 실패하면 empty list. *)
let extract_subchain_from (chain:chain) (chain_slice:Procname.t * status) : chain =
  let index = find_index_in_chain chain chain_slice in
  match index with
  | -1 -> []
  | _ ->
    let subchain_length = (List.length chain) - index in
    List.sub chain ~pos:index ~len:subchain_length


(** returnv 안에 들어 있는 callee method name을 뽑아 낸다. *)
let extract_callee_from_returnv (returnv_ap:MyAccessPath.t) =
  let returnv, _ = returnv_ap in
  match returnv with
  | LogicalVar _ -> L.die InternalError "extract_callee_from_returnv failed"
  | ProgramVar pv ->
      begin match Pvar.get_declaring_function pv with
      | Some procname -> procname
      | None -> L.die InternalError "extract_callee_from_returnv failed" end


(** returnv가 들어 있는 aliasset을 받아서, 그 안에 callee로부터 carry over된 var가 있다면 날린다. returnv는 무조건 날린다. *)
let filter_carrriedover_ap (aliasset:A.t) : A.t =
  let returnv_ap = A.find_first is_returnv_ap aliasset in
  let callee_methname = extract_callee_from_returnv returnv_ap in
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
let cleanup_aliasset (aliasset:A.t) (self:MyAccessPath.t) : A.t =
  let carried_over_ap_filtered = filter_carrriedover_ap aliasset in
  let self_filtered = A.remove self carried_over_ap_filtered in
  let logicalvar_filtered = A.filter (fun (var, lst) ->
    not @@ is_logical_var var || not @@ List.is_empty lst) self_filtered in
  logicalvar_filtered


(** Define에 들어 있는 Procname과 AP의 쌍을 받아서 그것이 들어 있는 chain을 리턴 *)
let find_entry_containing_chainslice (methname:Procname.t) (status:status) : chain option =
  let all_chains = Hashtbl.fold (fun _ v acc -> v::acc) chains [] in
  let result_chains = List.fold ~f:(fun acc chain ->
    if is_contained_in_chain (methname, status) chain
    then chain::acc
    else acc) ~init:[] all_chains in
  List.nth result_chains 0


let rec compute_chain_inner (current_methname:Procname.t) (current_astate_set:S.t) (current_astate:S.elt) (current_chain:chain) : chain =
  (* L.progress "current_astate: %a@." T.pp current_astate; *)
  let current_aliasset_without_returnv = A.filter (is_returnv_ap >> not) @@ fourth_of current_astate in
  let current_vardef = second_of current_astate in
  (* 직전에 추론했던 chain 토막에서 끄집어낸 variable *)
  let just_before = extract_ap_from_chain_slice @@ pop current_chain in
  (* 직전의 variable과 현재의 variable과 returnv를 모두 제거하고 나서 남은 pvar를 봤더니 *)
  match collect_program_var_aps_from current_aliasset_without_returnv current_vardef just_before with
  | [] -> (* either redefinition or dead end *)
      let states = S.elements (remove_duplicates_from current_astate_set) in
      let redefined_states = List.fold_left states ~init:[] ~f:(fun (acc:T.t list) (st:T.t) ->
          if MyAccessPath.equal current_vardef (second_of st)
          then st::acc
          else acc) in
      begin match redefined_states with
        | [_] -> (* Dead end *)
            (current_methname, Dead) :: current_chain
        | _::_ -> (* Redefinition *) (* 현재에서 가장 가까운 future state 중에서 vardef가 같은 state 찾기 *)
            let future_states = S.diff (remove_duplicates_from current_astate_set) @@ select_up_to current_astate ~within:(remove_duplicates_from current_astate_set) in
            let new_state = find_earliest_astate_of_var_within (S.elements future_states) in
            let new_chain = (current_methname, Redefine (current_vardef)) :: current_chain in
            compute_chain_inner current_methname current_astate_set new_state new_chain
        | _ -> L.die InternalError "compute_chain_inner failed, current_methname: %a, current_astate_set: %a, current_astate: %a, current_chain: %a@." Procname.pp current_methname S.pp current_astate_set T.pp current_astate pp_chain current_chain end
  | [ap] -> (* either definition or call *)
      if Var.is_return (fst ap)
      then (* caller에서의 define *)
        let var_being_returned = find_var_being_returned current_aliasset_without_returnv in
        let (direct_caller, caller_summary) = find_direct_caller current_methname current_chain in
        let states_with_return_var = search_target_tuples_by_pvar (mk_returnv current_methname) direct_caller (remove_duplicates_from caller_summary) in
        let have_been_before_filtered = filter_have_been_before states_with_return_var current_chain in
        let new_state = remove_from_aliasset ~from:(find_earliest_astate_within have_been_before_filtered) ~remove:(var_being_returned, []) in
        let new_slice = (first_of new_state, Define (current_methname, second_of new_state)) in
        (* cycle을 막기 위해, 이미 동일 slice를 만든 적이 있었다면 생성 중단 *)
        if List.mem current_chain new_slice ~equal:double_equal
        then (current_methname, Dead)::current_chain
        else 
          let new_chain = new_slice::current_chain in
          compute_chain_inner direct_caller caller_summary new_state new_chain
      else (* 동일 procedure 내에서의 define 혹은 call *)
        (* 다음 튜플을 현재 procedure 내에서 찾을 수 있는지를 기준으로 경우 나누기 *)
        begin match search_target_tuples_by_vardef_ap ap current_methname current_astate_set with
          | [] -> (* Call *)
              let callee_methname = find_immediate_successor current_methname current_astate_set ap in
              let new_states = search_target_tuples_by_vardef_ap ap callee_methname (remove_duplicates_from @@ get_summary callee_methname) in
              let new_state = find_earliest_astate_within new_states in
              let new_chain = (current_methname, Call (callee_methname, ap))::current_chain in
              compute_chain_inner callee_methname (get_summary callee_methname) new_state new_chain
          | nonempty_list -> (* 동일 proc에서의 Define *)
              L.progress "current ap: %a@." MyAccessPath.pp current_vardef;
              let new_state = find_earliest_astate_within @@ S.elements (remove_duplicates_from @@ S.of_list nonempty_list) in
              let new_slice = (current_methname, Define (current_methname, ap)) in
              (* cycle을 막기 위해, 이미 동일 slice를 만든 적이 있었다면 생성 중단 *)
              if List.mem current_chain new_slice ~equal:double_equal
              then (current_methname, Dead)::current_chain
              else
                let new_chain = new_slice::current_chain in
                compute_chain_inner current_methname current_astate_set new_state new_chain end
  | _ -> (* 현재 astate의 aliasset을 청소해서 불필요한 pvar를 없애고 재시도 *)
      try
        let (a, b, c, aliasset) = current_astate in
        let current_aliasset_cleaned_up = cleanup_aliasset aliasset current_vardef in
        let current_astate_cleaned_up = (a, b, c, current_aliasset_cleaned_up) in
        compute_chain_inner current_methname (current_astate_set) current_astate_cleaned_up current_chain
      with _ ->
        L.die InternalError "compute_chain_inner failed, current_methname: %a, current_astate_set: %a, current_astate: %a, current_chain: %a@." Procname.pp current_methname S.pp current_astate_set T.pp current_astate pp_chain current_chain


(** 콜 그래프와 분석 결과를 토대로 체인 (Define -> ... -> Dead)을 계산해 낸다 *)
let compute_chain_ (ap:MyAccessPath.t) : chain =
  let (first_methname, first_astate_set, first_astate) = find_first_occurrence_of ap in
  let first_aliasset = fourth_of first_astate in
  let returnv_opt = A.find_first_opt is_returnv_ap first_aliasset in
  let source_meth = match returnv_opt with
    | Some returnv -> procname_of returnv
    | None -> first_methname in
  List.rev @@ compute_chain_inner first_methname first_astate_set first_astate [(first_methname, Define (source_meth, ap))]


(** 본체인 compute_chain_을 포장하는 함수 *)
let compute_chain (ap:MyAccessPath.t) : chain =
  try
    let (first_methname, _, first_astate) = find_first_occurrence_of ap in
    let first_aliasset = fourth_of first_astate in
    match A.exists is_returnv_ap first_aliasset with
    | true -> (* 이미 어떤 chain의 subchain이라면 새로 계산할 필요 없음 *)
        let initial_chain_slice = Define (first_methname, ap) in
        begin match find_entry_containing_chainslice first_methname initial_chain_slice with
        | None -> (* 이전에 계산해 놓은 게 없네 *)
            L.progress "not extracting chain for %a@." MyAccessPath.pp ap;
            compute_chain_ ap
        | Some chain -> (* 이전에 계산해 놓은 게 있네! 거기서 단순 추출만 해야지 *)
            extract_subchain_from chain (first_methname, initial_chain_slice) end
    | false ->
        L.progress "false for %a@." MyAccessPath.pp ap;
        compute_chain_ ap
  with _ -> (* first_methname missing in the callgraph for some reason :( *)
    []


let collect_all_proc_and_ap () =
  let setofallstates = Hashtbl.fold (fun _ v acc -> S.union v acc) summary_table S.empty in
  let listofallstates = S.elements setofallstates in
  let list_of_all_proc_and_ap = List.map ~f:(fun (x:T.t) -> (first_of x, second_of x)) listofallstates in
  list_of_all_proc_and_ap


(** chains 해시 테이블 전체를 프린트한다 *)
let chains_to_string hashtbl =
  Hashtbl.fold (fun (proc, ap) v acc -> String.concat ~sep:"\n" [acc; (F.asprintf "(%a, %a): %a" Procname.pp proc MyAccessPath.pp ap pp_chain v)]) hashtbl ""


(** 파일로 call graph를 출력 *)
let save_callgraph () =
  let ch = Out_channel.create "Callgraph.txt" in
  Hashtbl.iter (fun k v -> Out_channel.output_string ch @@ (Procname.to_string k)^" -> "^(Procname.to_string v^"\n") ) callgraph_table;
  Out_channel.flush ch;
  Out_channel.close ch


let extract_pvar_from_var (var:Var.t) : Pvar.t =
  match var with
  | LogicalVar _ -> L.die InternalError "extract_pvar_from_var failed, var: %a@." Var.pp var
  | ProgramVar pv -> pv


(** throwaway code for debugging infinite loop for GuideRenderer.render *)
let find_ap_for_guiderenderer () =
  (* render라는 method name을 가진 (Procname.t * Summary.t) 쌍 전부 *)
  let ms_pairs_with_render = BFS.fold (fun ((proc, _) as target) acc ->
    if String.equal (Procname.get_method proc) "render"
    then target::acc
    else acc) [] callgraph in
  let is_'type' = fun var ->
    match var with
    | Var.LogicalVar _ -> false
    | Var.ProgramVar pv -> String.equal (Pvar.to_string pv) "type" in
  (* render라는 method를 가진 쌍들 중에서 ap가 (type, [])인 튜플을 가진 astate_set *)
  let render_summary = List.fold ~f:(fun acc (_, astate_set) ->
    if S.exists (fun astate -> is_'type' (fst @@ second_of astate)) astate_set
    then astate_set
    else acc) ~init:S.empty ms_pairs_with_render in
  let target_tuple = S.fold (fun astate acc -> 
    if is_'type' (fst @@ second_of astate)
    then astate
    else acc) render_summary bottuple in
  target_tuple


(** interface with the driver *)
let run_lrm () =
  MyCallGraph.load_summary_from_disk_to callgraph_table;
  save_callgraph ();
  load_summary_from_disk_to summary_table;
  batch_add_formal_args ();
  (* batch_print_formal_args (); *)
  filter_callgraph_table callgraph_table;
  callg_hash2og ();
  (* pp_chains callgraph; *)
  let setofallprocandap_with_garbage = List.stable_dedup (collect_all_proc_and_ap ()) in
  let setofallprocandap = List.filter ~f:(fun (_, (var, _)) ->
    let pv = extract_pvar_from_var var in
    not @@ Var.is_this var &&
    not @@ is_placeholder_vardef var &&
    not @@ Pvar.is_frontend_tmp pv) setofallprocandap_with_garbage in

  (* temp code for debugging WhatIWantExample.java *)
  let setofallap = List.map ~f:(fun (_, b) -> b) setofallprocandap in
  let xvar = (List.nth_exn setofallap 0) in
  let setofallprocandap_nox = List.filter ~f:(fun (_, x) -> not @@ MyAccessPath.equal xvar x) setofallprocandap in
  (* temp code end *)

  List.iter ~f:(fun (proc, ap) ->
    add_chain (proc, ap) (compute_chain ap)) setofallprocandap;
  let out_string = F.asprintf "%s\n" (chains_to_string chains) in
  let ch = Out_channel.create "Chain.txt" in
  Out_channel.output_string ch out_string;
  Out_channel.flush ch;
  Out_channel.close ch
