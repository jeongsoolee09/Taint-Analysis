open! IStd
open DefLocAlias.TransferFunctions
open DefLocAliasSearches
open DefLocAliasLogicTests
open DefLocAliasDomain

module Hashtbl = Caml.Hashtbl
module S = DefLocAliasDomain.AbstractStateSet
module A = DefLocAliasDomain.SetofAliases
module T = DefLocAliasDomain.AbstractState
module Q = DefLocAliasDomain.QuadrupleWithPP
module L = Logging
module F = Format

exception NotImplemented
exception NoEarliestTuple
exception NoParent
exception UnexpectedSituation1
exception UnexpectedSituation2
exception IDontKnow
exception StripError
exception ProcExtractFailed

type status =
  | Define of (Procname.t * Var.t)
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
  type t = Domain1.t * Domain2.t [@@deriving compare, equal]
end

module PairOfMS = struct
  include Pair (Procname) (S)
  type t = Procname.t * S.t
  let hash = Hashtbl.hash
end

module G = Graph.Imperative.Digraph.ConcreteBidirectional (PairOfMS)

module BFS = Graph.Traverse.Bfs (G)

(** map from procnames to their summaries. *)
let summary_table = Hashtbl.create 777

let get_summary (key:Procname.t) = Hashtbl.find summary_table key


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


  let duplicated_times (var:Var.t) (lst:T.t list) =
    let rec duplicated_times_inner (var:Var.t) (current_line:LocationSet.t) (current_time:int) (lst:T.t list) =
      match lst with
      | [] -> (*L.progress "dup time: %d\n" current_time;*) current_time
      | {T.tuple=(_, (vardef, _), loc, _)}::t ->
          if Var.equal var vardef
          then (if LocationSet.equal loc current_line
                then duplicated_times_inner var current_line (current_time+1) t
                else duplicated_times_inner var current_line current_time t)
          else duplicated_times_inner var current_line current_time t in
    let first_loc : LocationSet.t = third_of @@ (List.nth_exn lst 0).tuple in
    duplicated_times_inner var first_loc 0 lst


  (** 실행이 끝난 astate_set에서 중복된 튜플들 (proc과 vardef가 같음)끼리 묶여 있는 list of list를 만든다. *)
  let group_by_duplicates (astate_set:S.t) : T.t list list = 
    let keys = get_keys astate_set in
    let rec get_tuple_by_key tuplelist key =
      match tuplelist with
      | [] -> []
      | {T.tuple=(proc,(name, _), loc,_)} as targetTuple::t ->
          if triple_equal key (proc, name, loc)
          then ((*L.progress "generating key: %a, targetTuple: %a\n" Var.pp name QuadrupleWithPP.pp targetTuple;*) targetTuple::get_tuple_by_key t key) 
          else get_tuple_by_key t key in
    let get_tuples_by_keys tuplelist keys = List.map ~f:(get_tuple_by_key tuplelist) keys in
    let elements = S.elements astate_set in
    get_tuples_by_keys elements keys


  (** group_by_duplicates가 만든 list of list를 받아서, duplicate된 변수 list를 반환하되, ph와 this는 무시한다. *)
  let rec collect_duplicates (listlist:T.t list list) : T.t list list =
    match listlist with
    | [] -> []
    | lst::t ->
        let sample_tuple = (List.nth_exn lst 0).tuple in
        (*L.progress "sample tuple: %a\n" Q.pp sample_tuple;*)
        let current_var, _ = second_of sample_tuple in
        if not @@ is_placeholder_vardef current_var && not @@ Var.is_this current_var
        then (if duplicated_times current_var lst >= 2
              then lst::collect_duplicates t
              else collect_duplicates t)
        else collect_duplicates t


(** 중복 튜플을 제거함 *)
(* NOTE: 완성품에는 이 함수가 필요 없어야 함 *)
(* NOTE: 본 함수에는 ph와 this를 걸러 주는 기능도 있음 (collect_duplicates 사용). *)
let remove_duplicates_from (astate_set:S.t) : S.t =
  let grouped_by_duplicates = (group_by_duplicates >> collect_duplicates) astate_set in
  (* 위의 리스트 안의 각 리스트들 안에 들어 있는 튜플들 중 가장 alias set이 큰 놈을 남김 *)
  let leave_biggest_aliasset = fun lst -> List.fold_left lst ~init:botstate ~f:(fun (acc:T.t) (elem:T.t) -> if (A.cardinal @@ fourth_of acc.tuple) < (A.cardinal @@ fourth_of elem.tuple) then elem else acc) in
  S.of_list @@ List.map ~f:leave_biggest_aliasset grouped_by_duplicates
  

(** 해시 테이블 형태의 콜그래프를 ocamlgraph로 변환한다. *)
let callg_hash2og () : unit =
  Hashtbl.iter (fun key value -> G.add_edge callgraph (key, get_summary key) (value, get_summary value)) callgraph_table


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
      match S.exists (fun tup -> Var.equal (fst @@ second_of tup.tuple) var) astate with
      | true -> (*L.progress "found it!\n";*) astate
      | false -> (*L.progress "nah..:(\n";*) acc) S.empty callgraph in
  let astate_set_nodup = remove_duplicates_from astate_set in
  let elements = S.elements astate_set_nodup in
  let methname = first_of @@ (List.nth_exn elements 0).tuple in
  let targetTuples = search_target_astates_by_vardef var methname astate_set_nodup in
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
    S.of_list @@ List.fold_left astates ~init:[] ~f:(fun (acc:T.t list) (elem:T.t) -> if third_of elem.tuple => third_of astate.tuple then elem::acc else acc) in
  select_up_to_inner state


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
let rec have_been_before (astate:S.elt) (acc:chain) : bool =
  match acc with
  | [] -> false
  | (methname, status) :: t ->
      let procname = first_of astate.tuple in
      let vardef = second_of astate.tuple in
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
  let {T.tuple=(a, b, c, aliasset)} = astate in
  let aliasset' = A.remove var aliasset in
  {astate with tuple=(a, b, c, aliasset')}


let procname_of (ap:A.elt) : Procname.t =
  let var, _ = ap in
  match var with
  | ProgramVar pv ->
      begin match Pvar.get_declaring_function pv with
        | Some proc -> proc
        | _ -> raise ProcExtractFailed end
  | LogicalVar _ -> raise ProcExtractFailed


(** 콜 그래프와 분석 결과를 토대로 체인 (Define -> ... -> Dead)을 계산해 낸다 *)
let compute_chain (var:Var.t) : chain =
  let (first_methname, first_astate_set, first_astate) =
    (* L.progress "Target Var: %a\n" Var.pp var ; *)
    find_first_occurrence_of var in
  (* L.progress "first_methname: %a\n" Procname.pp first_methname ;
  L.progress "first_astate: %a\n" S.pp first_astate ;
  L.progress "first_tuple: %a\n" Q.pp first_tuple ; *)
  let first_aliasset = fourth_of first_astate.tuple in
  let returnv = A.find_first is_returnv_ap first_aliasset in
  let source_meth = procname_of returnv in
  let rec compute_chain_inner  (current_methname:Procname.t) (current_astate_set:S.t) (current_astate:S.elt) (current_chain:chain) : chain =
    let aliasset = A.filter (is_returnv_ap >> not) @@ fourth_of current_astate.tuple in
    let vardef = second_of current_astate.tuple in
    (* L.progress "vardef: %a\n" Var.pp vardef;
    L.progress "current tuple: %a\n" Q.pp current_astate; *)
    let just_before = extract_variable_from_chain_slice @@ pop current_chain in
    match collect_program_vars_from aliasset (fst vardef) just_before with
    | [] -> (* either redefinition or dead end *)
        let states = S.elements (remove_duplicates_from current_astate_set) in
        let redefined_states = List.fold_left states ~init:[] ~f:(fun (acc:T.t list) (st:T.t) -> if Var.equal (fst vardef) @@ (fst @@ second_of st.tuple) then st::acc else acc) in
        (* L.progress "redefined_states: "; List.iter ~f:(fun tup -> L.progress "%a, " Q.pp tup) redefined_states; L.progress "\n"; *)
        begin match redefined_states with
          | [_] -> (* Dead end *) (current_methname, Dead) :: current_chain
          | _::_ -> (* Redefinition *)
              (* let states_to_be_deleted = select_up_to current_astate ~within:(remove_duplicates_from current_astate_set) in *)
              let future_states = S.diff (remove_duplicates_from current_astate_set) @@ select_up_to current_astate ~within:(remove_duplicates_from current_astate_set) in
              (* L.progress "current state: %a\n" Q.pp current_astate;
               * L.progress "states_to_be_deleted: %a\n future_states: %a\n" S.pp states_to_be_deleted S.pp future_states; *)
              let new_state = find_earliest_astate_of_var_within (S.elements future_states) in
              let new_chain = (current_methname, Redefine (fst vardef)) :: current_chain in
              compute_chain_inner current_methname current_astate_set new_state new_chain
          | _ -> raise UnexpectedSituation1
        end
    | [var] -> (* either definition or call *)
        (* L.progress "next var: %a\n" Var.pp var; *)
        if Var.is_return var
        then (* caller에서의 define *)
          let var_being_returned = find_var_being_returned aliasset in
          (* L.progress "var_being_returned: %a\n" Var.pp var_being_returned; *)
          let (direct_caller, caller_summary) = find_direct_caller current_methname current_chain in
          let states_with_return_var = search_target_astates_by_pvar (mk_returnv current_methname) direct_caller (remove_duplicates_from caller_summary) in
          (* L.progress "states_with_return_var: "; List.iter ~f:(fun tup -> L.progress "%a, " Q.pp tup) states_with_return_var ; *)
          let have_been_before_filtered = filter_have_been_before states_with_return_var current_chain in
          (* L.progress "have_been_before_filtered: "; List.iter ~f:(fun tup -> L.progress "%a, " Q.pp tup) have_been_before_filtered; *)
          let new_state = remove_from_aliasset ~from:(find_earliest_astate_within have_been_before_filtered) ~remove:(var_being_returned, []) in
          let new_chain = (first_of new_state.tuple, Define (current_methname, (fst @@ second_of new_state.tuple))) :: current_chain in
          compute_chain_inner direct_caller caller_summary new_state new_chain
        else (* 동일 procedure 내에서의 define 혹은 call *)
          (* 다음 튜플을 현재 procedure 내에서 찾을 수 있는지를 기준으로 경우 나누기 *)
          begin match search_target_astates_by_vardef var current_methname current_astate_set with
          | [] -> (* Call *)
              (*L.progress "current_methname: %a, current_astate_set: %a\n" Procname.pp current_methname S.pp current_astate_set;*)
              let callee_methname = find_immediate_successor current_methname current_astate_set var in
              (*L.progress "callee_methname: %a" Procname.pp callee_methname;*)
              let new_states = search_target_astates_by_vardef var callee_methname (remove_duplicates_from @@ get_summary callee_methname) in
              (* List.iter ~f:(fun tup -> L.progress "new_states: "; L.progress "%a, " Q.pp tup; L.progress "\n") new_states; *)
              let new_state = find_earliest_astate_within new_states in
              let new_chain = (current_methname, Call (callee_methname, var))::current_chain in
              compute_chain_inner callee_methname (get_summary callee_methname) new_state new_chain
          | nonempty_list -> (* 동일 proc에서의 Define *)
              let new_state = find_earliest_astate_within @@ S.elements (remove_duplicates_from @@ S.of_list nonempty_list) in
              let new_chain = (current_methname, Define (current_methname, var)) :: current_chain in
              compute_chain_inner current_methname current_astate_set new_state new_chain end
    | _ -> raise UnexpectedSituation2 in
  List.rev @@ compute_chain_inner first_methname first_astate_set first_astate [(first_methname, Define (source_meth, var))]


let collect_all_vars () =
  let setofallstates =  Hashtbl.fold (fun _ v acc -> S.union v acc) summary_table S.empty in
  let listofallstates = S.elements setofallstates in
  let listofallvars = List.map ~f:(fun (x:T.t) -> second_of x.tuple) listofallstates in
  let listofallvar_aps = List.map ~f:(fun (var, _) -> (var, [])) listofallvars in
  A.of_list listofallvar_aps


let pp_status fmt x =
  match x with
  | Define (proc, var) -> F.fprintf fmt "Define (%a using %a)" Var.pp var Procname.pp proc
  | Call (proc, var) -> F.fprintf fmt "Call (%a with %a)" Procname.pp proc Var.pp var
  | Redefine var -> F.fprintf fmt "Redefine (%a)" Var.pp var
  | Dead -> F.fprintf fmt "Dead"
 

let pp_pair fmt (proc, v) = F.fprintf fmt "(%a, %a) ->" Procname.pp proc pp_status v


let pp_chain fmt x = Pp.seq pp_pair fmt x


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
  let xvar, _ = (List.nth_exn (A.elements setofallvars) 0) in
  add_chain xvar (compute_chain xvar);
  (* A.iter (fun var -> L.progress "Var: %a\n" Var.pp var) setofallvars; *)
  (* A.iter (fun var -> L.progress "computing chain for %a\n" Var.pp var; add_chain var (compute_chain var)) setofallvars; *)
  let out_string = F.asprintf "%s\n" (to_string chains) in
  let ch = Out_channel.create "Chain.txt" in
  Out_channel.output_string ch out_string;
  Out_channel.flush ch;
  Out_channel.close ch
