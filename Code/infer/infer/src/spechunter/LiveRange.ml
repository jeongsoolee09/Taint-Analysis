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
  | Define of (Procname.t * Var.t)
  | Call of (Procname.t * Var.t)
  | Redefine of Var.t
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
  | Define (proc, var) -> F.fprintf fmt "Define (%a using %a)" Var.pp var Procname.pp proc
  | Call (proc, var) -> F.fprintf fmt "Call (%a with %a)" Procname.pp proc Var.pp var
  | Redefine var -> F.fprintf fmt "Redefine (%a)" Var.pp var
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
  Hashtbl.iter (fun k v -> L.progress "procname: %a, " Procname.pp k; L.progress "vars: "; List.iter v ~f:(L.progress "%a, " Var.pp); L.progress "\n") formal_args

(** a primitive representation of the call graph. *)
let callgraph_table = Hashtbl.create 777

let callgraph = G.create ()

let chains = Hashtbl.create 777

let add_chain (key:Var.t) (value:chain) = Hashtbl.add chains key value

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
  (* L.progress "partitioned_by_duplicates: %a@." pp_tuplelistlist partitioned_by_duplicates; *)
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


(** 주어진 변수 var에 있어 가장 이른 정의 state를 찾는다. *)
let find_first_occurrence_of (var:Var.t) : Procname.t * S.t * S.elt =
  let astate_set = BFS.fold (fun (_, astate) acc ->
      match S.exists (fun tup -> Var.equal (fst @@ second_of tup) var) astate with
      | true -> (*L.progress "found it!\n";*) astate
      | false -> (*L.progress "nah..:(\n";*) acc) S.empty callgraph in
  (* L.progress "astate_set with dup: %a@." S.pp astate_set; *)
  let astate_set_nodup = remove_duplicates_from astate_set in
  (* L.progress "astate_set without dup: %a@." S.pp astate_set_nodup; *)
  let elements = S.elements astate_set_nodup in
  let methname = first_of @@ (List.nth_exn elements 0) in
  let targetTuples = search_target_tuples_by_vardef var methname astate_set_nodup in
  let earliest_state = find_earliest_astate_within targetTuples in
  (methname, astate_set, earliest_state)


(** 디버깅 용도로 BFS 사용해서 그래프 출력하기 *)
let print_graph graph = BFS.iter (fun (proc, _) -> L.progress "proc: %a@." Procname.pp proc) graph


(** alias set에서 자기 자신, this, ph, 직전 variable을 빼고 남은 program variable들을 리턴 *)
let collect_program_vars_from (aliases:A.t) (self:Var.t) (just_before:Var.t) : Var.t list =
  let filtered = List.filter ~f:(fun (x, _) -> is_program_var x &&
                           not @@ Var.equal self x &&
                           not @@ Var.is_this x &&
                           not @@ is_placeholder_vardef x &&
                           not @@ Var.equal just_before x) (A.elements aliases) in
  List.map ~f:fst filtered


let select_up_to (state:S.elt) ~within:(astate_set:S.t) : S.t =
  let astates = S.elements astate_set in
  let select_up_to_inner (astate:S.elt) : S.t =
    S.of_list @@ List.fold_left astates ~init:[] ~f:(fun (acc:T.t list) (elem:T.t) -> if third_of elem => third_of astate then elem::acc else acc) in
  select_up_to_inner state


let equal_btw_vertices : PairOfMS.t -> PairOfMS.t -> bool =
  fun (m1, s1) (m2, s2) -> Procname.equal m1 m2 && S.equal s1 s2


(** accumulator를 따라가면서 최초의 parent (즉, 직전의 caller)를 찾아낸다. *)
let find_direct_caller (target_meth:Procname.t) (acc:chain) =
  let target_vertex = (target_meth, get_summary target_meth) in
  let rec find_direct_caller_inner (acc:chain) =
    match acc with
    | [] -> L.die InternalError "find_direct_caller failed, target_meth: %a, acc: %a@." Procname.pp target_meth pp_chain acc
    | (cand_meth, _) :: t ->
        let is_pred = fun v -> List.mem (G.pred callgraph target_vertex) v ~equal:equal_btw_vertices in
        let cand_vertex = (cand_meth, get_summary cand_meth) in
        if is_pred cand_vertex
        then cand_vertex
        else find_direct_caller_inner t in
  find_direct_caller_inner acc


(** 가 본 적이 있는지를 검사하는 술어. *)
(** NOTE: status 패턴 매칭 부분이 맞는지 잘 모르겠다.*)
let rec have_been_before (astate:S.elt) (acc:chain) : bool =
  match acc with
  | [] -> false
  | (methname, status) :: t ->
      let procname = first_of astate in
      let vardef = second_of astate in
      begin match status with
        | Define (_, var) ->
            if Procname.equal procname methname && Var.equal (fst vardef) var
            then true else have_been_before astate t
        | Call (callee, var) -> (* 맞으려나? *)
            if (Procname.equal callee procname || Procname.equal callee methname) && Var.equal (fst vardef) var then true else have_been_before astate t
        | Redefine var ->
            if Procname.equal procname methname && Var.equal (fst vardef) var
            then true else have_been_before astate t
        | Dead ->
            have_been_before astate t end


(** 가 본 적이 *없는* 튜플들만을 남긴다. *)
let filter_have_been_before (tuplelist:S.elt list) (current_chain:chain) =
  List.fold_left tuplelist ~init:[] ~f:(fun acc tup -> if not @@ have_been_before tup current_chain then tup::acc else acc)


(** 바로 다음의 successor들 중에서 파라미터를 들고 있는 함수를 찾아 낸다. 못 찾을 경우, Procname.empty_block을 내뱉는다. *)
let find_immediate_successor (current_methname:Procname.t) (current_astate:S.t) (param:Var.t) =
  let succs = G.succ callgraph (current_methname, current_astate) in
  let succ_meths_and_formals = List.map ~f:(fun (meth, _) -> (meth, get_formal_args meth)) succs in
  List.fold_left ~init:Procname.empty_block ~f:(fun acc (m, p) -> (*L.progress "m: %a, " Procname.pp m;*) (*L.progress "p: "; List.iter ~f:(fun v -> L.progress "%a, " Var.pp v) p; L.progress "param: %a\n" Var.pp param;*) if List.mem p param ~equal:Var.equal then m else acc) succ_meths_and_formals


let pop (lst:'a list) : 'a option =
  match lst with
  | [] -> None
  | _ -> Some (List.nth_exn lst 0)


let extract_variable_from_chain_slice (slice:(Procname.t*status) option) : Var.t =
  match slice with
  | Some (_, status) ->
      begin match status with
      | Define (_, var) -> var
      | Call (_, var) -> var
      | Redefine var -> var
      | Dead -> (* L.progress "Extracting from Dead\n"; *) (fst @@ second_of bottuple) end
  | None -> (* L.progress "Extracting from empty chain\n"; *) (fst @@ second_of bottuple)


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


  let rec split_lists (n:int) (lst:chain) : chain list =
    match lst with
    | [] -> []
    | lst ->
        let list = List.take lst n :: split_lists n (List.drop lst 1) in
        List.filter ~f:(fun x -> Int.equal (List.length x) n) list


  let double_equal ((methname1, status1):(Procname.t*status)) ((methname2, status2):(Procname.t*status)) : bool =
    Procname.equal methname1 methname2 && Status.equal status1 status2


  let rec check_lists (lst:chain) (lstlst:chain list) : bool =
    match lstlst with
    | [] -> true
    | y::ys ->
      begin match List.equal double_equal lst y with
        | true -> true
        | false -> check_lists lst ys end


  let subchain (first:chain) (second:chain) : bool =
    match first, second with
    | [], [] -> true
    | xs, ys ->
        let subys = split_lists (List.length xs) ys in
        check_lists xs subys


(** 콜 그래프와 분석 결과를 토대로 체인 (Define -> ... -> Dead)을 계산해 낸다 *)
let compute_chain_ (var:Var.t) : chain =
  let (first_methname, first_astate_set, first_astate) = find_first_occurrence_of var in
  let first_aliasset = fourth_of first_astate in
  let returnv = A.find_first is_returnv_ap first_aliasset in
  let source_meth = procname_of returnv in
  let rec compute_chain_inner (current_methname:Procname.t) (current_astate_set:S.t) (current_astate:S.elt) (current_chain:chain) : chain =
    let current_aliasset_without_returnv = A.filter (is_returnv_ap >> not) @@ fourth_of current_astate in
    let current_vardef = second_of current_astate in
    (* 직전에 추론했던 chain 토막에서 끄집어낸 variable *)
    let just_before = extract_variable_from_chain_slice @@ pop current_chain in
    (* 직전의 variable과 현재의 variable을 모두 제거하고 나서 남은 pvar를 봤더니 *)
    match collect_program_vars_from current_aliasset_without_returnv (fst current_vardef) just_before with
    | [] -> (* either redefinition or dead end *)
        let states = S.elements (remove_duplicates_from current_astate_set) in
        let redefined_states = List.fold_left states ~init:[] ~f:(fun (acc:T.t list) (st:T.t) -> if Var.equal (fst current_vardef) @@ (fst @@ second_of st) then st::acc else acc) in
        begin match redefined_states with
          | [_] -> (* Dead end *)
              (current_methname, Dead) :: current_chain
          | _::_ -> (* Redefinition *) (* 현재에서 가장 가까운 future state 중에서 vardef가 같은 state 찾기 *)
              let future_states = S.diff (remove_duplicates_from current_astate_set) @@ select_up_to current_astate ~within:(remove_duplicates_from current_astate_set) in
              let new_state = find_earliest_astate_of_var_within (S.elements future_states) in
              let new_chain = (current_methname, Redefine (fst current_vardef)) :: current_chain in
              compute_chain_inner current_methname current_astate_set new_state new_chain
          | _ -> L.die InternalError "compute_chain_inner failed, current_methname: %a, current_astate_set: %a, current_astate: %a, current_chain: %a@." Procname.pp current_methname S.pp current_astate_set T.pp current_astate pp_chain current_chain
        end
    | [var] -> (* either definition or call *)
        if Var.is_return var
        then (* caller에서의 define *)
          let var_being_returned = find_var_being_returned current_aliasset_without_returnv in
          let (direct_caller, caller_summary) = find_direct_caller current_methname current_chain in
          let states_with_return_var = search_target_tuples_by_pvar (mk_returnv current_methname) direct_caller (remove_duplicates_from caller_summary) in
          let have_been_before_filtered = filter_have_been_before states_with_return_var current_chain in
          let new_state = remove_from_aliasset ~from:(find_earliest_astate_within have_been_before_filtered) ~remove:(var_being_returned, []) in
          let new_chain = (first_of new_state, Define (current_methname, (fst @@ second_of new_state))) :: current_chain in
          compute_chain_inner direct_caller caller_summary new_state new_chain
        else (* 동일 procedure 내에서의 define 혹은 call *)
          (* 다음 튜플을 현재 procedure 내에서 찾을 수 있는지를 기준으로 경우 나누기 *)
          begin match search_target_tuples_by_vardef var current_methname current_astate_set with
          | [] -> (* Call *)
              let callee_methname = find_immediate_successor current_methname current_astate_set var in
              let new_states = search_target_tuples_by_vardef var callee_methname (remove_duplicates_from @@ get_summary callee_methname) in
              let new_state = find_earliest_astate_within new_states in
              let new_chain = (current_methname, Call (callee_methname, var))::current_chain in
              compute_chain_inner callee_methname (get_summary callee_methname) new_state new_chain
          | nonempty_list -> (* 동일 proc에서의 Define *)
              L.progress "Define! var: %a, current_methname: %a@." Var.pp var Procname.pp current_methname;
              let new_state = find_earliest_astate_within @@ S.elements (remove_duplicates_from @@ S.of_list nonempty_list) in
              let new_chain = (current_methname, Define (current_methname, var)) :: current_chain in
              compute_chain_inner current_methname current_astate_set new_state new_chain end
    | _ -> L.die InternalError "compute_chain_inner failed, current_methname: %a, current_astate_set: %a, current_astate: %a, current_chain: %a@." Procname.pp current_methname S.pp current_astate_set T.pp current_astate pp_chain current_chain in
  List.rev @@ compute_chain_inner first_methname first_astate_set first_astate [(first_methname, Define (source_meth, var))]


let compute_chain (var:Var.t) : chain =
  let (first_methname, first_astate_set, first_astate) = find_first_occurrence_of var in
  let first_aliasset = fourth_of first_astate in
  match A.exists is_returnv_ap first_aliasset with
  | true -> compute_chain_ var
  | false -> [(first_methname, Define (first_methname, var))]


let collect_all_vars () =
  let setofallstates =  Hashtbl.fold (fun _ v acc -> S.union v acc) summary_table S.empty in
  let listofallstates = S.elements setofallstates in
  let listofallvars = List.map ~f:(fun (x:T.t) -> second_of x) listofallstates in
  A.of_list listofallvars


let to_string hashtbl =
  Hashtbl.fold (fun k v acc -> String.concat ~sep:"\n" [acc; (F.asprintf "%a: %a" Var.pp k pp_chain v)]) hashtbl ""


let save_callgraph () =
  let ch = Out_channel.create "Callgraph.txt" in
  Hashtbl.iter (fun k v -> Out_channel.output_string ch @@ (Procname.to_string k)^" -> "^(Procname.to_string v^"\n") ) callgraph_table


(** interface with the driver *)
let run_lrm () =
  MyCallGraph.load_summary_from_disk_to callgraph_table;
  save_callgraph ();
  load_summary_from_disk_to summary_table;
  batch_add_formal_args ();
  (* batch_print_formal_args (); *)
  filter_callgraph_table callgraph_table;
  callg_hash2og ();
  let setofallvars_with_garbage = collect_all_vars () in
  let setofallvars = A.filter (fun (var, _) -> not @@ Var.is_this var && not @@ is_placeholder_vardef var) setofallvars_with_garbage in
  (*let xvar, _ = (List.nth_exn (A.elements setofallvars) 0) in
  add_chain xvar (compute_chain xvar);*)
  A.iter (fun (var, _) ->
    L.progress "computing chain for: %a@." Var.pp var;
    add_chain var (compute_chain var)) setofallvars;
  (* A.iter (fun var -> L.progress "Var: %a\n" Var.pp var) setofallvars; *)
  (* A.iter (fun var -> L.progress "computing chain for %a\n" Var.pp var; add_chain var (compute_chain var)) setofallvars; *)
  let out_string = F.asprintf "%s\n" (to_string chains) in
  let ch = Out_channel.create "Chain.txt" in
  Out_channel.output_string ch out_string;
  Out_channel.flush ch;
  Out_channel.close ch
