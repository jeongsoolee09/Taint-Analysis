open! IStd
open DefLocAliasSearches
open DefLocAliasPredicates
open DefLocAliasDomain
open DefLocAliasPP
open Partitioners
open SpecHunterUtils
open Yojson.Basic
open List
module Hashtbl = Caml.Hashtbl
module P = DefLocAliasDomain.AbstractPair
module S = DefLocAliasDomain.AbstractStateSetFinite
module A = DefLocAliasDomain.SetofAliases
module T = DefLocAliasDomain.AbstractState
module L = Logging
module F = Format

(* Exceptions ======================================= *)
(* ================================================== *)

exception ReturnvFindFailed of string

exception TooManyMatches

exception NoMatches

exception NoStateTupHoldingAliasTup of string

exception NoSuchElem of string

exception NotAPVar of string

exception NotADefine

exception NotACall

exception NotARedefine

exception ThisIsImpossible

(* Types ============================================ *)
(* ================================================== *)

module Status = struct
  type t =
    (* Here, the Procname.t is the callee used to define the variable. *)
    | Define of (Procname.t * MyAccessPath.t * LocationSet.t)
    (* Here, the Procname.t is the callee. *)
    | Call of (Procname.t * MyAccessPath.t * LocationSet.t * int) (* here, int is the callv's counter value *)
    | VoidCall of (Procname.t * MyAccessPath.t * LocationSet.t * int) (* here, int is the callv's counter value *)
    | Redefine of (MyAccessPath.t * LocationSet.t)
    | DeadByCycle
    | Dead
  [@@deriving equal]

  let pp fmt x =
    match x with
    | Define (proc, ap, locset) ->
        F.fprintf fmt "Define (%a using %a): %a" MyAccessPath.pp ap Procname.pp proc LocationSet.pp
          locset
    | Call (proc, ap, locset, _) ->
        (* ignore the counter value. *)
        F.fprintf fmt "Call (%a with %a): %a" Procname.pp proc MyAccessPath.pp ap LocationSet.pp
          locset
    | VoidCall (proc, ap, locset, _) ->
        (* ignore the counter value. *)
        F.fprintf fmt "VoidCall (%a with %a): %a" Procname.pp proc MyAccessPath.pp ap LocationSet.pp
          locset
    | Redefine (ap, locset) ->
        F.fprintf fmt "Redefine (%a): %a" MyAccessPath.pp ap LocationSet.pp locset
    | DeadByCycle ->
        F.fprintf fmt "DeadByCycle"
    | Dead ->
        F.fprintf fmt "Dead"


  let is_define (status : t) : bool = match status with Define _ -> true | _ -> false

  let is_call (status : t) : bool = match status with Call _ -> true | _ -> false

  let is_redefine (status : t) : bool = match status with Redefine _ -> true | _ -> false

  let is_dead (status : t) : bool = match status with Dead -> true | _ -> false

  let extract_info_from_define (status : t) =
    match status with
    | Define (callee, ap, locset) ->
        (callee, ap, locset)
    | _ ->
        F.kasprintf
          (fun msg ->
            L.progress "%s" msg ;
            raise NotADefine )
          "extract_info_from_call failed, status: %a@." pp status


  let extract_info_from_call (status : t) =
    match status with
    | Call (callee, ap, locset, counter) ->
        (callee, ap, locset, counter)
    | _ ->
        F.kasprintf
          (fun msg ->
            L.progress "%s" msg ;
            raise NotACall )
          "extract_info_from_call failed, status: %a@." pp status


  let extract_info_from_redefine (status : t) =
    match status with
    | Redefine (ap, locset) ->
        (ap, locset)
    | _ ->
        F.kasprintf
          (fun msg ->
            L.progress "%s" msg ;
            raise NotARedefine )
          "extract_info_from_call failed, status: %a@." pp status
end

type json = Yojson.Basic.t

module Chain = struct
  type chain_slice = Procname.t * Status.t [@@deriving equal]

  type t = chain_slice list [@@deriving equal]
end

module type Stype = module type of S

(* Domain 과 Summary의 쌍 *)
module Pair (Domain1 : module type of Procname) (Domain2 : Stype) = struct
  type t = Domain1.t * Domain2.t [@@deriving compare, equal]
end

(* Pair of Method and its Astate sets *)
module MyProcname = struct
  include Procname

  let hash = Hashtbl.hash
end

(*  Pretty Printers ================================= *)
(* ================================================== *)

let pp_pair fmt (proc, v) = F.fprintf fmt "(%a, %a) ->" Procname.pp proc Status.pp v

let pp_chain fmt x = Pp.seq pp_pair fmt x

let pp_chain_list fmt x = Pp.seq pp_chain fmt x

let pp_chain_list fmt (lst : Chain.t list) =
  F.fprintf fmt "[" ;
  List.iter ~f:(fun chain -> F.fprintf fmt "%a, " pp_chain chain) lst ;
  F.fprintf fmt "]"


let pp_chain_listlist fmt (lst : Chain.t list list) =
  F.fprintf fmt "[" ;
  List.iter ~f:(fun chainlist -> F.fprintf fmt "%a, " pp_chain_list chainlist) lst ;
  F.fprintf fmt "]"


let pp_MyAccessChain fmt (var, aplist) = F.fprintf fmt "(%a, %a)" Var.pp var pp_ap_list aplist

let string_of_vertex (proc, astateset) = F.asprintf "\"(%a, %a)\"" Procname.pp proc S.pp astateset

(* Ocamlgraph Definitions =========================== *)
(* ================================================== *)

module G = struct
  include Graph.Imperative.Digraph.ConcreteBidirectional (MyProcname)

  let graph_attributes _ = []

  let default_vertex_attributes _ = []

  let vertex_name = Procname.to_string

  let vertex_attributes (_ : V.t) = [`Shape `Box]

  let get_subgraph _ = None

  let default_edge_attributes _ = []

  let edge_attributes _ = []
end

module BFS = Graph.Traverse.Bfs (G)
module Dot = Graph.Graphviz.Dot (G)

(* Summary Table ==================================== *)
(* ================================================== *)

(** map from procnames to their summaries. *)
let summary_table = Hashtbl.create 777

let get_summary (key : Procname.t) : S.t = try Hashtbl.find summary_table key with _ -> S.empty

let pp_summary_table fmt hashtbl : unit =
  Hashtbl.iter (fun k v -> F.fprintf fmt "%a -> %a\n" Procname.pp k S.pp v) hashtbl


(** Print the contents of the summary table *)
let print_summary_table () =
  Hashtbl.iter
    (fun proc summary ->
      L.progress "procname: %a, " Procname.pp proc ;
      L.progress "summary: %a@." S.pp summary )
    summary_table


(* Procnames and their formal args ================== *)
(* ================================================== *)

(** map from procname to its formal args. *)
let formal_args : (Procname.t, MyAccessPath.t list) Hashtbl.t = Hashtbl.create 777

let batch_add_formal_args () =
  let procnames = Hashtbl.fold (fun k _ acc -> k :: acc) summary_table [] in
  let pname_and_pdesc_opt = procnames >>| fun pname -> (pname, Procdesc.load pname) in
  let pname_and_pdesc = catMaybes_tuplist pname_and_pdesc_opt in
  let pname_and_params_with_type =
    pname_and_pdesc >>| fun (pname, pdesc) -> (pname, Procdesc.get_pvar_formals pdesc)
  in
  let pname_and_params =
    pname_and_params_with_type
    >>| fun (pname, with_type_list) -> (pname, with_type_list >>| fun (a, _) -> (Var.of_pvar a, []))
  in
  iter ~f:(fun (pname, params) -> Hashtbl.add formal_args pname params) pname_and_params


let get_formal_args (key : Procname.t) : MyAccessPath.t list =
  match Hashtbl.find_opt formal_args key with None -> [] | Some ap_list -> ap_list


let batch_print_formal_args () =
  Hashtbl.iter
    (fun k v ->
      L.progress "procname: %a, " Procname.pp k ;
      L.progress "vars: " ;
      iter v ~f:(L.progress "%a, " MyAccessPath.pp) ;
      L.progress "\n" )
    formal_args


(* Procname and their callv counters ================ *)
(* ================================================== *)

let procname_callv_counter : (Procname.t, int) Hashtbl.t = Hashtbl.create 777

let initialize_callv_counter () =
  let procnames = Hashtbl.fold (fun k v acc -> k :: acc) summary_table [] in
  iter ~f:(fun procname -> Hashtbl.add procname_callv_counter procname (-1)) procnames


let get_counter (procname : Procname.t) = Hashtbl.find procname_callv_counter procname

let update_counter (procname : Procname.t) (new_counter : int) =
  Hashtbl.replace procname_callv_counter procname new_counter


let reset_counter (procname : Procname.t) = Hashtbl.replace procname_callv_counter procname (-1)

(* CallGraph ======================================== *)
(* ================================================== *)

(** a tabular representation of the call graph. *)
let callgraph_table = Hashtbl.create 777

let callgraph = G.create ()

let chains : (Procname.t * MyAccessPath.t * LocationSet.t, Chain.chain_slice list) Hashtbl.t =
  Hashtbl.create 777


(** Procname과 AP로부터 chain으로 가는 Hash table *)
let add_chain (key : Procname.t * MyAccessPath.t * LocationSet.t) (value : Chain.t) =
  Hashtbl.add chains key value


(** Function for debugging by exporting Ocamlgraph to Graphviz Dot *)
let graph_to_dot (graph : G.t) ?(filename = "callgraph_with_astate.dot") : unit =
  let out_channel = Out_channel.create filename in
  Dot.output_graph out_channel graph ;
  Out_channel.flush out_channel ;
  Out_channel.close out_channel


(** 해시 테이블 형태의 콜그래프를 ocamlgraph로 변환한다. *)
let callg_hash2og () : unit =
  Hashtbl.iter (fun key _ -> G.add_vertex callgraph key) summary_table ;
  Hashtbl.iter (fun key value -> G.add_edge callgraph key value) callgraph_table


let resolve_callee_superclass (caller : Procname.t) (callee : Procname.t) : Procname.t =
  let succs = G.succ callgraph caller in
  let callee_simple_string = Procname.get_method callee in
  let callee_param_type = Procname.get_parameters callee in
  let param_list_equal (plist1 : Procname.Parameter.t list) (plist2 : Procname.Parameter.t list) =
    match
      List.fold2
        ~f:(fun acc p1 p2 -> Procname.Parameter.equal p1 p2 && acc)
        plist1 plist2 ~init:true
    with
    | Ok result ->
        result
    | Unequal_lengths ->
        false
  in
  let matches =
    List.fold
      ~f:(fun acc succ ->
        let succ_simple_string = Procname.get_method succ in
        let succ_param_type = Procname.get_parameters succ in
        if
          String.equal callee_simple_string succ_simple_string
          && param_list_equal callee_param_type succ_param_type
        then succ :: acc
        else acc )
      succs ~init:[]
  in
  match matches with
  | [] ->
      F.kasprintf
        (fun msg ->
          L.progress "%s" msg ;
          raise NoMatches )
        "resolve_callee_superclass failed, caller: %a, callee: %a, matches: %a" Procname.pp caller
        Procname.pp callee pp_proc_list matches
  | [proc] ->
      L.progress "callee %a resolved to %a@." Procname.pp callee Procname.pp proc ;
      proc
  | _ ->
      F.kasprintf
        (fun msg ->
          L.progress "%s" msg ;
          raise TooManyMatches )
        "resolve_callee_superclass failed, caller: %a, callee: %a, matches: %a" Procname.pp caller
        Procname.pp callee pp_proc_list matches


(** 주어진 hashtbl의 엔트리 중에서 (callgraph_table이 쓰일 것) summary_table에 있지 않은 엔트리를 날린다. *)
let filter_callgraph_table hashtbl : unit =
  let procs = Hashtbl.fold (fun k _ acc -> k :: acc) summary_table [] in
  Hashtbl.iter
    (fun k v ->
      if (not @@ mem procs k ~equal:Procname.equal) && (not @@ mem procs v ~equal:Procname.equal)
      then Hashtbl.remove hashtbl k )
    hashtbl


(** 중복 튜플을 제거함 *)
let remove_duplicates_from (astate_set : S.t) : S.t =
  let partitioned_by_duplicates = partition_statetups_modulo_123 astate_set >>| S.elements in
  (* 위의 리스트 안의 각 리스트들 안에 들어 있는 튜플들 중 가장 alias set이 큰 놈을 남김 *)
  let leave_tuple_with_biggest_aliasset lst =
    if length lst > 1 then
      fold_left lst ~init:bottuple ~f:(fun (acc : T.t) (elem : T.t) ->
          if Int.( < ) (A.cardinal @@ fourth_of acc) (A.cardinal @@ fourth_of elem) then elem
          else acc )
    else nth_exn lst 0
  in
  let result = partitioned_by_duplicates >>| leave_tuple_with_biggest_aliasset |> S.of_list in
  S.filter
    (fun tup ->
      let var, _ = second_of tup in
      (not @@ is_placeholder_vardef var) && (not @@ Var.is_this var) )
    result


(** 디버깅 용도로 BFS 사용해서 그래프 출력하기 *)
let print_graph graph =
  L.progress "============ printing callgraph ============@." ;
  BFS.iter (fun proc -> L.progress "proc: %a@." Procname.pp proc) graph ;
  L.progress "============================================@."


(* Computing Chains ================================= *)
(* ================================================== *)

let remove_matching_callv_and_returnv ((proc, vardef, loc, aliasset) : T.t) (callv : MyAccessPath.t)
    : T.t =
  let matching_returnv = find_matching_returnv_for_callv aliasset callv in
  let removed = (proc, vardef, loc, aliasset |> A.remove callv |> A.remove matching_returnv) in
  L.progress "removed callv: %a, returne: %a, removed result: %a@." MyAccessPath.pp callv
    MyAccessPath.pp matching_returnv T.pp removed ;
  removed


let find_most_recent_locset_of_ap (target_ap : MyAccessPath.t) (astates : S.t) =
  if is_param_ap target_ap then LocationSet.bottom
  else
    let res =
      S.fold
        (fun (_, vardef, locset, _) acc ->
          if MyAccessPath.equal target_ap vardef then locset :: acc else acc )
        astates []
    in
    match res with
    | [] ->
        L.progress "find_most_recent_locset_of_ap failed. target_ap: %a, astates: %a@."
          MyAccessPath.pp target_ap S.pp astates ;
        raise NoMatches
    | otherwise ->
        List.fold
          ~f:(fun acc locset -> if acc ==> locset then locset else acc)
          otherwise
          ~init:(LocationSet.singleton Location.dummy)


(** 주어진 AccessPath ap에 있어 가장 이른 정의 state를 찾는다. *)
let find_first_occurrence_of (ap : MyAccessPath.t) : Procname.t * S.t * S.elt =
  let astate_set =
    BFS.fold
      (fun proc acc ->
        let proc_astate = get_summary proc in
        match S.exists (fun tup -> MyAccessPath.equal (second_of tup) ap) proc_astate with
        | true ->
            proc_astate
        | false ->
            acc )
      S.empty callgraph
  in
  match S.elements astate_set with
  | [] ->
      (Procname.empty_block, S.empty, bottuple) (* probably clinit *)
  | _ ->
      let astate_set_nodup = remove_duplicates_from astate_set in
      let elements = S.elements astate_set_nodup in
      let methname = first_of @@ nth_exn elements 0 in
      let targetTuples = search_target_tuples_by_vardef_ap ap methname astate_set_nodup in
      let earliest_state = find_earliest_astate_within targetTuples in
      (methname, astate_set, earliest_state)


(** alias set에서 자기 자신, ph, 직전 variable을 빼고 남은 program variable들을 리턴 *)
let collect_program_var_aps_from (aliasset : A.t) ~(self : MyAccessPath.t)
    ~(just_before : MyAccessPath.t option) : MyAccessPath.t list =
  match just_before with
  | Some just_before ->
      filter ~f:(fun x ->
          is_program_var (fst x)
          && (not @@ MyAccessPath.equal self x)
          (* not @@ Var.is_this (fst x) && *)
          && (not @@ is_placeholder_vardef (fst x))
          && (not @@ MyAccessPath.equal just_before x) )
      @@ A.elements aliasset
  | None ->
      filter ~f:(fun x ->
          is_program_var (fst x)
          && (not @@ MyAccessPath.equal self x)
          && (* not @@ Var.is_this (fst x) && *)
          (not @@ is_placeholder_vardef (fst x)) )
      @@ A.elements aliasset


(** Find the immediate callers and their summaries of the given Procname.t. *)
let find_direct_callers (target_meth : Procname.t) : Procname.t list = G.pred callgraph target_meth

(** Find the immediate callees and their summaries of the given Procname.t. *)
let find_direct_callees (target_caller : Procname.t) (target_meth : Procname.t) : Procname.t list =
  try G.succ callgraph target_meth
  with _ ->
    let retry_targetname = resolve_callee_superclass target_caller target_meth in
    G.succ callgraph retry_targetname


(** Is the Chain.chain_slice already in the given chain? *)
let have_been_before (chain_slice : Chain.chain_slice) (chain : Chain.t) : bool =
  List.mem chain chain_slice ~equal:Chain.equal_chain_slice


let is_skip_function (methname : Procname.t) : bool = Option.is_none @@ Procdesc.load methname

let save_APIs () : unit =
  let procnames =
    Hashtbl.fold
      (fun meth1 meth2 acc ->
        let meth1_is_skip = is_skip_function meth1 in
        let meth2_is_skip = is_skip_function meth2 in
        match (meth1_is_skip, meth2_is_skip) with
        | true, true ->
            Procname.Set.add meth1 acc |> Procname.Set.add meth2
        | true, false ->
            Procname.Set.add meth1 acc
        | false, true ->
            Procname.Set.add meth2 acc
        | false, false ->
            acc )
      callgraph_table Procname.Set.empty
  in
  let out_chan_unique_ids = Out_channel.create "APIs_unique_id.txt"
  and out_chan_methnames = Out_channel.create "APIs.txt" in
  let procnames_list = Procname.Set.elements procnames in
  iter
    ~f:(fun procname ->
      let func_name = F.asprintf "%a" Procname.pp_unique_id procname in
      Out_channel.output_string out_chan_unique_ids @@ func_name ^ "\n" )
    procnames_list ;
  iter
    ~f:(fun procname ->
      let func_name = F.asprintf "%s" (Procname.to_string procname) in
      Out_channel.output_string out_chan_methnames @@ func_name ^ "\n" )
    procnames_list ;
  Out_channel.close out_chan_unique_ids ;
  Out_channel.close out_chan_methnames


let extract_ap_from_chain_slice (slice : (Procname.t * Status.t) option) : MyAccessPath.t option =
  match slice with
  | Some (_, status) -> (
    match status with
    | Define (_, ap, _) ->
        Some ap
    | Call _ ->
        None
    | VoidCall _ ->
        None
    | Redefine (ap, _) ->
        Some ap
    | DeadByCycle ->
        None
    | Dead ->
        None )
  | None ->
      None


let remove_from_aliasset ~(from : T.t) ~remove:var =
  let a, b, c, aliasset = from in
  let aliasset' = A.remove var aliasset in
  (a, b, c, aliasset')


(** chain_slice가 chain 안에 들어 있다는 전제 하에 그 index를 찾아 냄 *)
let elem_is_at (chain : Chain.t) (chain_slice : Procname.t * Status.t) : int =
  fold
    ~f:(fun acc elem -> if Chain.equal_chain_slice chain_slice elem then acc + 1 else acc)
    ~init:0 chain


(** -1을 리턴할 수도 있게끔 elem_is_at을 포장 *)
let find_index_in_chain (chain : Chain.t) (chain_slice : Chain.chain_slice) : int =
  match have_been_before chain_slice chain with true -> elem_is_at chain chain_slice | false -> -1


(** chain과 chain_slice를 받아, chain_slice가 있는 지점부터 시작되는 subchain을 꺼내 온다. 실패하면 empty list. *)
let extract_subchain_from (chain : Chain.t) (chain_slice : Chain.chain_slice) : Chain.t =
  let index = find_index_in_chain chain chain_slice in
  match index with
  | -1 ->
      []
  | _ ->
      let subchain_length = length chain - index in
      sub chain ~pos:index ~len:subchain_length


(** Define에 들어 있는 Procname과 AP의 쌍을 받아서 그것이 들어 있는 chain을 리턴 *)
let find_entry_containing_chainslice (methname : Procname.t) (status : Status.t) : Chain.t list =
  let all_chains = Hashtbl.fold (fun _ v acc -> v :: acc) chains [] in
  fold
    ~f:(fun acc chain -> if have_been_before (methname, status) chain then chain :: acc else acc)
    ~init:[] all_chains


let count_vardefs_in_astateset ~(find_this : MyAccessPath.t) (astate_set : S.t)
    ~(after_than : Location.t) : int =
  S.fold
    (fun astate cnt ->
      if
        MyAccessPath.equal find_this (second_of astate)
        && Int.( = ) (Location.compare (LocationSet.min_elt (third_of astate)) after_than) 1
      then cnt + 1
      else cnt )
    astate_set 0


(** Find returnv tuples in a given aliasset *)
let find_returnv_holding_callee_aliasset (callee_name : Procname.t) (aliasset : A.t) : A.elt =
  let returnvs =
    A.fold (fun elem acc -> if is_returnv_ap elem then elem :: acc else acc) aliasset []
  in
  let rec inner (aliases : A.elt list) : A.elt =
    match aliases with
    | [] ->
        F.kasprintf
          (fun msg -> raise @@ ReturnvFindFailed msg)
          "find_returnv_holding_callee failed. callee_name: %a, aliasset: %a@." Procname.pp
          callee_name A.pp aliasset
    | ((returnv, _) as elt) :: t ->
        let returnv_content = extract_callee_from elt in
        if Procname.equal callee_name returnv_content then elt else inner t
  in
  inner returnvs


let find_returnv_holding_callee_astateset (callee_name : Procname.t) (astate_set : S.t) : A.elt =
  L.progress "find_returnv_holding_callee_astateset callee_name: %a@." Procname.pp callee_name ;
  let out =
    S.fold
      (fun statetup acc ->
        let aliasset = fourth_of statetup in
        try
          let returnv = find_returnv_holding_callee_aliasset callee_name aliasset in
          returnv :: acc
        with ReturnvFindFailed _ -> acc )
      astate_set []
  in
  match out with
  | [] ->
      L.progress "find_returnv_holding_callee_astateset failed. callee_name: %a, astate_set: %a@."
        Procname.pp callee_name S.pp astate_set ;
      raise NoMatches
  | [x] ->
      x
  | _ ->
      List.hd_exn out


(** Find any one state tuple holding the given alias tuple. Use it with care: perhaps only with
    callv or returnv *)
let find_statetup_holding_aliastup (statetupset : S.t) (aliastup : A.elt) : S.elt =
  let statetups = S.elements statetupset in
  let rec inner (statetups : S.elt list) : S.elt =
    match statetups with
    | [] ->
        F.kasprintf
          (fun msg -> raise @@ NoStateTupHoldingAliasTup msg)
          "find_statetup_holding_aliastup failed. statetupset: %a, aliastup: %a@." S.pp statetupset
          MyAccessPath.pp aliastup
    | ((_, _, _, target_aliasset) as statetup) :: t ->
        if A.mem aliastup target_aliasset then statetup else inner t
  in
  inner statetups


(** Are there any returnvs in the aliasset? *)
let alias_with_returnv (statetup : S.elt) (callee_methname : Procname.t) : bool =
  A.exists
    (fun ap ->
      is_returnv_ap ap
      &&
      let methname = extract_callee_from ap in
      Procname.equal methname callee_methname )
    (fourth_of statetup)


let compare_astate astate1 astate2 =
  let linum_set1 = third_of astate1 and linum_set2 = third_of astate2 in
  let min_linum1 = LocationSet.min_elt linum_set1 and min_linum2 = LocationSet.min_elt linum_set2 in
  Location.compare min_linum1 min_linum2


let rec next_elem_of_list (lst : S.elt list) ~(next_to : S.elt) : S.elt =
  match lst with
  | [] ->
      F.kasprintf
        (fun msg -> raise @@ NoSuchElem msg)
        "next_elem_of_list failed: lst: %a, next_to: %a@." pp_tuplelist lst T.pp next_to
  | this :: t ->
      if T.equal this next_to then hd_exn t else next_elem_of_list t ~next_to


let find_matching_param_for_callv (ap_set : A.t) (callv_ap : A.elt) : A.elt =
  let callv_methname = extract_callee_from callv_ap in
  let callee_params = get_formal_args callv_methname in
  L.progress "ap_set is empty: %a@." Bool.pp @@ A.is_empty ap_set ;
  L.progress "ap_set is: %a@." A.pp ap_set ;
  let param_aps =
    A.filter
      (fun ap ->
        let ap_methname = extract_callee_from ap in
        is_param_ap ap
        && Procname.equal ap_methname callv_methname
        &&
        let ap_linum = extract_linum_from_param_ap ap in
        let callv_linum = extract_linum_from_callv callv_ap in
        L.progress "ap_linum: %a, callv_linum: %a@." Int.pp ap_linum Int.pp callv_linum ;
        Int.( = ) ap_linum callv_linum )
      ap_set
  in
  let non_param_ap_parameters =
    if A.is_empty param_aps then
      A.filter (fun ap -> List.mem callee_params ap ~equal:MyAccessPath.equal) ap_set
    else A.empty
  in
  match (A.is_empty param_aps, A.is_empty non_param_ap_parameters) with
  | true, true ->
      L.progress "find_matching_param_for_callv failed. ap_set: %a, callv_ap: %a@." A.pp ap_set
        MyAccessPath.pp callv_ap ;
      raise ThisIsImpossible
  | true, false ->
      List.hd_exn @@ A.elements non_param_ap_parameters
  | false, true ->
      List.hd_exn @@ A.elements param_aps
  | false, false ->
      L.progress "find_matching_param_for_callv failed. ap_set: %a, callv_ap: %a@." A.pp ap_set
        MyAccessPath.pp callv_ap ;
      raise NoMatches


let is_caller ~(caller : Procname.t) ~(callee : Procname.t) =
  let direct_callers = find_direct_callers callee in
  List.mem direct_callers caller ~equal:Procname.equal


let reset_counter_recursively (current_procname : Procname.t) : unit =
  (* L.progress "recursively resetting for %a ...@." Procname.pp current_procname ; *)
  reset_counter current_procname ;
  G.iter_succ
    (fun proc ->
      (* L.progress "%a's counter reset to 0@." Procname.pp proc ; *)
      reset_counter proc )
    callgraph current_procname


(* computing chains ================================= *)
(* ================================================== *)

let rec compute_chain_inner (current_methname : Procname.t) (current_astate_set : S.t)
    (current_astate : S.elt) (current_chain : Chain.t) (current_call_stack : Procname.t list)
    (debug_chain : Chain.t) (current_chain_acc : Chain.t list) : Chain.t list =
  if
    (not @@ List.is_empty debug_chain)
    && List.mem (List.tl_exn debug_chain) (hd_exn debug_chain) ~equal:Chain.equal_chain_slice
  then (
    let completed_chain = (current_methname, Status.DeadByCycle) :: current_chain in
    reset_counter_recursively current_methname ;
    completed_chain :: current_chain_acc )
  else
    let current_aliasset = fourth_of current_astate in
    let current_aliasset_cleanedup =
      A.filter
        (fun ap ->
          (not @@ is_logical_var @@ fst ap)
          && (not @@ MyAccessPath.equal (second_of current_astate) ap) )
        current_aliasset
    in
    let current_vardef = second_of current_astate in
    (* variable extracted from astate visited right before *)
    let (just_before_procname, just_before_status) : Chain.chain_slice = hd_exn current_chain in
    let just_before_ap_opt : A.elt option = extract_ap_from_chain_slice @@ hd current_chain in
    let var_aps =
      collect_program_var_aps_from current_aliasset_cleanedup ~self:current_vardef
        ~just_before:just_before_ap_opt
      |> List.filter ~f:is_local_to_known_procname
    in
    (* is it correct to put just_before_procname here? dunno... *)
    let callees = find_direct_callees just_before_procname current_methname in
    let statetup_with_returnv_or_carriedovers =
      fold
        ~f:(fun acc callee ->
          let callee_astate_set = get_summary callee in
          acc @ find_returnv_or_carriedover_ap current_astate_set callee_astate_set )
        ~init:[] callees
    in
    let something_else =
      filter
        ~f:
          ( match just_before_ap_opt with
          | None ->
              fun ap ->
                let var = fst ap in
                (not @@ is_logical_var var)
                && (not @@ is_this_ap ap)
                && (not @@ is_placeholder_vardef_ap ap)
                && (not @@ MyAccessPath.equal ap (second_of current_astate))
                && is_local_to_known_procname ap
                && (not @@ is_returnv var)
                && (not @@ Var.is_return var)
                && (not @@ is_callv var)
                && (not @@ is_param var)
                && (not @@ mem statetup_with_returnv_or_carriedovers ~equal:MyAccessPath.equal ap)
          | Some just_before ->
              fun ap ->
                let var = fst ap in
                (not @@ is_logical_var var)
                && (not @@ is_this_ap ap)
                && (not @@ is_placeholder_vardef_ap ap)
                && (not @@ MyAccessPath.equal ap (second_of current_astate))
                && is_local_to_known_procname ap
                && (not @@ is_returnv var)
                && (not @@ Var.is_return var)
                && (not @@ is_callv var)
                && (not @@ is_param var)
                && (not @@ MyAccessPath.equal just_before ap)
                && (not @@ mem statetup_with_returnv_or_carriedovers ~equal:MyAccessPath.equal ap)
          )
        var_aps
    in
    L.progress
      "============ inner loop. current_methname: %a, current_astate: %a,@.current_chain: \
       %a@.current_chain_acc: %a@."
      Procname.pp current_methname T.pp current_astate pp_chain (rev current_chain) pp_chain_list
      current_chain_acc ;
    match something_else with
    | [] ->
        if S.is_empty current_astate_set then (
          (* This is an Library API function *)
          let just_before_astate_set = get_summary just_before_procname in
          let just_before_astate_set_has_returnv =
            S.exists
              (fun statetup -> alias_with_returnv statetup current_methname)
              just_before_astate_set
          in
          if just_before_astate_set_has_returnv then (
            (* ============ DEFINITION AT THE CALLER ============ *)
            assert (Status.is_call just_before_status) ;
            (* sanity check *)
            (* Get the linum and counter of the call *)
            let _, _, callv_locset, callv_counter =
              Status.extract_info_from_call just_before_status
            in
            let aliased_with_returnv : T.t =
              find_astate_holding_returnv just_before_astate_set current_methname callv_counter
                (locset_as_linum callv_locset)
            in
            let chain_updated =
              ( just_before_procname
              , Status.Define
                  (current_methname, second_of aliased_with_returnv, third_of aliased_with_returnv)
              )
              :: current_chain
            and debug_chain_updated =
              ( just_before_procname
              , Status.Define
                  (current_methname, second_of aliased_with_returnv, third_of aliased_with_returnv)
              )
              :: debug_chain
            and new_call_stack = List.tl_exn current_call_stack in
            reset_counter current_methname ;
            compute_chain_inner just_before_procname just_before_astate_set aliased_with_returnv
              chain_updated new_call_stack debug_chain_updated current_chain_acc )
          else
            (* ============ DEAD ============ *)
            let is_leaf = is_empty @@ G.succ callgraph current_methname in
            let completed_chain =
              if is_leaf then (current_methname, Status.Dead) :: current_chain else current_chain
            in
            reset_counter_recursively current_methname ;
            completed_chain :: current_chain_acc
          (* the following if-then-else sequences encodes
               the level of preferences among different A.elt's. *) )
        else if exists ~f:(fun (var, _) -> Var.is_return var) var_aps then (
          (* ============ DEFINITION AT THE CALLER ============ *)
          let not_enough_call_stack = Option.is_none @@ List.nth current_call_stack 1
          and popped_meth_is_not_a_caller =
            match List.nth current_call_stack 1 with
            | None ->
                false
            | Some meth ->
                not @@ is_caller ~caller:meth ~callee:current_methname
          in
          match not_enough_call_stack || popped_meth_is_not_a_caller with
          | true ->
              let callers_and_astates =
                find_direct_callers current_methname |> List.filter ~f:(not << is_lambda)
              in
              let mapfunc caller =
                let caller_astate_set = get_summary caller in
                let returnv_aliastup =
                  find_returnv_holding_callee_astateset current_methname caller_astate_set
                in
                let statetup_with_returnv =
                  find_statetup_holding_aliastup caller_astate_set returnv_aliastup
                in
                let chain_updated =
                  [ ( caller
                    , Status.Define
                        ( current_methname
                        , second_of statetup_with_returnv
                        , third_of statetup_with_returnv ) ) ]
                and debug_chain_updated =
                  ( caller
                  , Status.Define
                      ( current_methname
                      , second_of statetup_with_returnv
                      , third_of statetup_with_returnv ) )
                  :: debug_chain
                and call_stack_updated = caller :: current_call_stack in
                reset_counter current_methname ;
                (* recurse *)
                compute_chain_inner caller caller_astate_set statetup_with_returnv chain_updated
                  call_stack_updated debug_chain_updated []
              in
              let collected_subchains = callers_and_astates >>= mapfunc in
              List.map ~f:(fun subchain -> subchain @ current_chain) collected_subchains
          | false ->
              let caller = List.nth_exn current_call_stack 1 in
              let caller_astate_set = get_summary caller in
              let returnv_aliastup =
                find_returnv_holding_callee_astateset current_methname caller_astate_set
              in
              let statetup_with_returnv =
                find_statetup_holding_aliastup caller_astate_set returnv_aliastup
              in
              let chain_updated =
                ( caller
                , Status.Define
                    ( current_methname
                    , second_of statetup_with_returnv
                    , third_of statetup_with_returnv ) )
                :: current_chain
              and debug_chain_updated =
                ( caller
                , Status.Define
                    ( current_methname
                    , second_of statetup_with_returnv
                    , third_of statetup_with_returnv ) )
                :: debug_chain
              and call_stack_updated = List.tl_exn current_call_stack in
              reset_counter current_methname ;
              (* recurse *)
              compute_chain_inner caller caller_astate_set statetup_with_returnv chain_updated
                call_stack_updated debug_chain_updated current_chain_acc )
        else if exists ~f:is_callv_ap var_aps then
          (* ============ CALL or VOID CALL ============ *)
          (* Retrieve and update the callv counter. *)
          let callv_counter = get_counter current_methname in
          let callvs_partitioned_by_procname =
            filter ~f:is_callv_ap var_aps |> partition_callvs_by_procname
          in
          let earliest_callvs =
            List.fold
              ~f:(fun acc callvs ->
                try find_earliest_callv callvs ~greater_than:callv_counter :: acc with _ -> acc )
              callvs_partitioned_by_procname ~init:[]
          in
          let mapfunc callv =
            assert (Int.( <= ) callv_counter (extract_counter_from_callv callv)) ;
            let callv_counter = extract_counter_from_callv callv in
            update_counter current_methname (extract_counter_from_callv callv) ;
            L.progress "%a's counter updated to %a@." Procname.pp current_methname Int.pp
              (extract_counter_from_callv callv) ;
            let param_ap_matching_callv = find_matching_param_for_callv (A.of_list var_aps) callv in
            L.progress "param_ap_matching_callv: %a@." MyAccessPath.pp param_ap_matching_callv ;
            let callee_methname = extract_callee_from callv in
            let callee_astate_set = get_summary callee_methname in
            let param_ap_locset =
              let ap_linum =
                if is_param_ap param_ap_matching_callv then
                  extract_linum_from_param_ap param_ap_matching_callv
                else extract_linum_from_param param_ap_matching_callv callee_astate_set
              in
              let location_term : Location.t =
                {Location.line= ap_linum; Location.col= -1; Location.file= SourceFile.invalid ""}
              in
              LocationSet.singleton location_term
            in
            match return_type_is_void callee_methname (*|| is_modeled callee_methname*) with
            | true ->
                (* VOID CALL *)
                let new_chain_slice =
                  ( current_methname
                  , Status.VoidCall
                      (callee_methname, param_ap_matching_callv, param_ap_locset, callv_counter) )
                in
                let chain_updated = [new_chain_slice]
                (* and call_stack_updated = callee_methname :: current_call_stack in *)
                and debug_chain_updated = new_chain_slice :: debug_chain
                and call_stack_updated = current_call_stack in
                if is_param_ap param_ap_matching_callv then (
                  (* API Call *)
                  let current_astate_updated =
                    if
                      A.exists
                        (fun ap -> is_returnv_ap ap && callv_and_returnv_matches ~callv ~returnv:ap)
                        (fourth_of current_astate)
                    then
                      let proc, vardef, locset, aliasset =
                        remove_matching_callv_and_returnv current_astate callv
                      in
                      if
                        Int.( >= )
                          (List.count
                             ~f:(fun ap ->
                               is_callv_ap ap
                               && Procname.equal (extract_callee_from ap)
                                    (extract_callee_from callv) )
                             (A.elements (fourth_of current_astate)) )
                          2
                      then (proc, vardef, locset, aliasset)
                      else
                        ( proc
                        , vardef
                        , locset
                        , aliasset |> A.remove callv |> A.remove param_ap_matching_callv )
                    else
                      let proc, vardef, locset, aliasset = current_astate in
                      if
                        Int.( >= )
                          (List.count
                             ~f:(fun ap ->
                               is_callv_ap ap
                               && Procname.equal (extract_callee_from ap)
                                    (extract_callee_from callv) )
                             (A.elements (fourth_of current_astate)) )
                          2
                      then (proc, vardef, locset, aliasset |> A.remove callv)
                      else
                        ( proc
                        , vardef
                        , locset
                        , aliasset |> A.remove callv |> A.remove param_ap_matching_callv )
                  in
                  L.progress "current_astate_updated (1): %a@." T.pp current_astate_updated ;
                  reset_counter_recursively current_methname ;
                  compute_chain_inner current_methname current_astate_set current_astate_updated
                    chain_updated current_call_stack debug_chain_updated current_chain_acc )
                else
                  (* UDF Call *)
                  let param_statetup =
                    search_target_tuple_by_pvar_ap param_ap_matching_callv callee_methname
                      callee_astate_set
                  in
                  let param_ap_computed =
                    compute_chain_inner callee_methname callee_astate_set param_statetup
                      chain_updated call_stack_updated debug_chain_updated []
                  in
                  let current_astate_updated =
                    if
                      A.exists
                        (fun ap -> is_returnv_ap ap && callv_and_returnv_matches ~callv ~returnv:ap)
                        (fourth_of current_astate)
                    then
                      let proc, vardef, locset, aliasset =
                        remove_matching_callv_and_returnv current_astate callv
                      in
                      if
                        Int.( >= )
                          (List.count
                             ~f:(fun ap ->
                               is_callv_ap ap
                               && Procname.equal (extract_callee_from ap)
                                    (extract_callee_from callv) )
                             (A.elements (fourth_of current_astate)) )
                          2
                      then (proc, vardef, locset, aliasset)
                      else
                        ( proc
                        , vardef
                        , locset
                        , aliasset |> A.remove callv |> A.remove param_ap_matching_callv )
                    else
                      let proc, vardef, locset, aliasset = current_astate in
                      if
                        Int.( >= )
                          (List.count
                             ~f:(fun ap ->
                               is_callv_ap ap
                               && Procname.equal (extract_callee_from ap)
                                    (extract_callee_from callv) )
                             (A.elements (fourth_of current_astate)) )
                          2
                      then (proc, vardef, locset, aliasset |> A.remove callv)
                      else
                        ( proc
                        , vardef
                        , locset
                        , aliasset |> A.remove callv |> A.remove param_ap_matching_callv )
                  in
                  L.progress "current_astate_updated (2): %a@." T.pp current_astate_updated ;
                  let computed =
                    param_ap_computed
                    >>= fun chain ->
                    compute_chain_inner current_methname current_astate_set current_astate_updated
                      chain current_call_stack debug_chain_updated current_chain_acc
                  in
                  reset_counter_recursively current_methname ;
                  computed
            | false ->
                (* CALL *)
                let new_chain_slice =
                  ( current_methname
                  , Status.Call
                      (callee_methname, param_ap_matching_callv, param_ap_locset, callv_counter) )
                in
                let chain_updated = [new_chain_slice]
                and debug_chain_updated = new_chain_slice :: debug_chain
                and call_stack_updated = callee_methname :: current_call_stack in
                if is_param_ap param_ap_matching_callv then (
                  (* API Call *)
                  let computed =
                    compute_chain_inner callee_methname callee_astate_set bottuple chain_updated
                      call_stack_updated debug_chain_updated []
                  in
                  reset_counter_recursively current_methname ;
                  computed )
                else
                  (* UDF call *)
                  let param_statetup =
                    search_target_tuple_by_pvar_ap param_ap_matching_callv callee_methname
                      callee_astate_set
                  in
                  let computed =
                    compute_chain_inner callee_methname callee_astate_set param_statetup
                      chain_updated call_stack_updated debug_chain_updated []
                  in
                  reset_counter_recursively current_methname ;
                  computed
          in
          let collected_subchains = earliest_callvs >>= mapfunc in
          List.map ~f:(fun subchain -> subchain @ current_chain) collected_subchains
        else if
          (* either REDEFINITION or DEAD.
             check which one is the case by checking if there are multiple current_vardefs in the alias set *)
          (not @@ LocationSet.is_empty (third_of current_astate))
          && Int.( >= )
               (count_vardefs_in_astateset current_astate_set ~find_this:current_vardef
                  ~after_than:(LocationSet.min_elt (third_of current_astate)) )
               1
        then
          (* ============ REDEFINITION ============ *)
          (* Intuition: get to the least recently redefined variable and recurse on that *)
          let all_states_with_current_ap =
            sort ~compare:compare_astate
            @@ filter ~f:(fun astate ->
                   MyAccessPath.equal (second_of current_astate) (second_of astate) )
            @@ S.elements current_astate_set
          in
          let least_recently_redefined =
            next_elem_of_list all_states_with_current_ap ~next_to:current_astate
          in
          let current_ap, current_locset = (second_of current_astate, third_of current_astate) in
          let current_astate_set_updated = S.remove current_astate current_astate_set in
          (* remove the current_astate from current_astate_set *)
          let chain_updated =
            ( current_methname
            , Status.Redefine
                ( current_ap
                , LocationSet.map (fun loc -> {loc with line= loc.line + 1}) current_locset ) )
            :: current_chain
          and debug_chain_updated =
            ( current_methname
            , Status.Redefine
                ( current_ap
                , LocationSet.map (fun loc -> {loc with line= loc.line + 1}) current_locset ) )
            :: debug_chain
          in
          (* no need to update the call stack! *)
          (* recurse *)
          compute_chain_inner current_methname current_astate_set_updated least_recently_redefined
            chain_updated current_call_stack debug_chain_updated current_chain_acc
        else
          (* ============ DEAD ============ *)
          (* no more recursion; return *)
          let completed_chain = (current_methname, Status.Dead) :: current_chain in
          reset_counter_recursively current_methname ;
          completed_chain :: current_chain_acc
    | nonempty_aplist ->
        let local_aps =
          List.filter
            ~f:(fun ap -> Procname.equal (extract_callee_from ap) current_methname)
            var_aps
        in
        let callvs = List.filter ~f:is_callv_ap var_aps in
        let call_chains =
          if is_empty callvs then []
          else
            (* ============ CALL or VOID CALL ============ *)
            (* Retrieve and update the callv counter. *)
            let callv_counter = get_counter current_methname in
            let callvs_partitioned_by_procname = callvs |> partition_callvs_by_procname in
            let earliest_callvs =
              List.fold
                ~f:(fun acc callvs ->
                  try find_earliest_callv callvs ~greater_than:callv_counter :: acc with _ -> acc )
                callvs_partitioned_by_procname ~init:[]
            in
            L.progress "callvs: %a, callv_counter: %d@." pp_ap_list callvs callv_counter ;
            (* let earliest_callv = find_earliest_callv callvs ~greater_than:callv_counter in *)
            let mapfunc callv =
              assert (Int.( <= ) callv_counter (extract_counter_from_callv callv)) ;
              let callv_counter = extract_counter_from_callv callv in
              update_counter current_methname (extract_counter_from_callv callv) ;
              L.progress "%a's counter updated to %a@." Procname.pp current_methname Int.pp
                (extract_counter_from_callv callv) ;
              let param_ap_matching_callv =
                find_matching_param_for_callv (A.of_list var_aps) callv
              in
              L.progress "param_ap_matching_callv: %a@." MyAccessPath.pp param_ap_matching_callv ;
              let callee_methname = extract_callee_from callv in
              let callee_astate_set = get_summary callee_methname in
              let param_ap_locset =
                let ap_linum =
                  if is_param_ap param_ap_matching_callv then
                    extract_linum_from_param_ap param_ap_matching_callv
                  else extract_linum_from_param param_ap_matching_callv callee_astate_set
                in
                let location_term : Location.t =
                  {Location.line= ap_linum; Location.col= -1; Location.file= SourceFile.invalid ""}
                in
                LocationSet.singleton location_term
              in
              match return_type_is_void callee_methname (*|| is_modeled callee_methname*) with
              | true ->
                  (* VOID CALL *)
                  let new_chain_slice =
                    ( current_methname
                    , Status.VoidCall
                        (callee_methname, param_ap_matching_callv, param_ap_locset, callv_counter)
                    )
                  in
                  let chain_updated = [new_chain_slice]
                  (* and call_stack_updated = callee_methname :: current_call_stack in *)
                  and debug_chain_updated = new_chain_slice :: debug_chain
                  and call_stack_updated = current_call_stack in
                  if is_param_ap param_ap_matching_callv then (
                    (* API Call *)
                    let current_astate_updated =
                      if
                        A.exists
                          (fun ap ->
                            is_returnv_ap ap && callv_and_returnv_matches ~callv ~returnv:ap )
                          (fourth_of current_astate)
                      then
                        let proc, vardef, locset, aliasset =
                          remove_matching_callv_and_returnv current_astate callv
                        in
                        if
                          Int.( >= )
                            (List.count
                               ~f:(fun ap ->
                                 is_callv_ap ap
                                 && Procname.equal (extract_callee_from ap)
                                      (extract_callee_from callv) )
                               (A.elements (fourth_of current_astate)) )
                            2
                        then (proc, vardef, locset, aliasset)
                        else
                          ( proc
                          , vardef
                          , locset
                          , aliasset |> A.remove callv |> A.remove param_ap_matching_callv )
                      else
                        let proc, vardef, locset, aliasset = current_astate in
                        if
                          Int.( >= )
                            (List.count
                               ~f:(fun ap ->
                                 is_callv_ap ap
                                 && Procname.equal (extract_callee_from ap)
                                      (extract_callee_from callv) )
                               (A.elements (fourth_of current_astate)) )
                            2
                        then (proc, vardef, locset, aliasset |> A.remove callv)
                        else
                          ( proc
                          , vardef
                          , locset
                          , aliasset |> A.remove callv |> A.remove param_ap_matching_callv )
                    in
                    L.progress "current_astate_updated (3): %a@." T.pp current_astate_updated ;
                    compute_chain_inner current_methname current_astate_set current_astate_updated
                      chain_updated current_call_stack debug_chain_updated current_chain_acc )
                  else
                    (* UDF Call *)
                    let param_statetup =
                      search_target_tuple_by_pvar_ap param_ap_matching_callv callee_methname
                        callee_astate_set
                    in
                    let param_ap_computed =
                      compute_chain_inner callee_methname callee_astate_set param_statetup
                        chain_updated call_stack_updated debug_chain_updated []
                    in
                    let current_astate_updated =
                      if
                        A.exists
                          (fun ap ->
                            is_returnv_ap ap && callv_and_returnv_matches ~callv ~returnv:ap )
                          (fourth_of current_astate)
                      then
                        let proc, vardef, locset, aliasset =
                          remove_matching_callv_and_returnv current_astate callv
                        in
                        if
                          Int.( >= )
                            (List.count
                               ~f:(fun ap ->
                                 is_callv_ap ap
                                 && Procname.equal (extract_callee_from ap)
                                      (extract_callee_from callv) )
                               (A.elements (fourth_of current_astate)) )
                            2
                        then (proc, vardef, locset, aliasset)
                        else
                          ( proc
                          , vardef
                          , locset
                          , aliasset |> A.remove callv |> A.remove param_ap_matching_callv )
                      else
                        let proc, vardef, locset, aliasset = current_astate in
                        if
                          Int.( >= )
                            (List.count
                               ~f:(fun ap ->
                                 is_callv_ap ap
                                 && Procname.equal (extract_callee_from ap)
                                      (extract_callee_from callv) )
                               (A.elements (fourth_of current_astate)) )
                            2
                        then (proc, vardef, locset, aliasset |> A.remove callv)
                        else
                          ( proc
                          , vardef
                          , locset
                          , aliasset |> A.remove callv |> A.remove param_ap_matching_callv )
                    in
                    L.progress "current_astate_updated (4): %a@." T.pp current_astate_updated ;
                    let computed =
                      param_ap_computed
                      >>= fun chain ->
                      compute_chain_inner current_methname current_astate_set current_astate_updated
                        chain current_call_stack debug_chain_updated current_chain_acc
                    in
                    computed
              | false ->
                  (* CALL *)
                  let new_chain_slice =
                    ( current_methname
                    , Status.Call
                        (callee_methname, param_ap_matching_callv, param_ap_locset, callv_counter)
                    )
                  in
                  let chain_updated = [new_chain_slice]
                  and debug_chain_updated = new_chain_slice :: debug_chain
                  and call_stack_updated = callee_methname :: current_call_stack in
                  if is_param_ap param_ap_matching_callv then
                    (* API Call *)
                    let computed =
                      compute_chain_inner callee_methname callee_astate_set bottuple chain_updated
                        call_stack_updated debug_chain_updated []
                    in
                    computed
                  else
                    (* UDF call *)
                    let param_statetup =
                      search_target_tuple_by_pvar_ap param_ap_matching_callv callee_methname
                        callee_astate_set
                    in
                    let computed =
                      compute_chain_inner callee_methname callee_astate_set param_statetup
                        chain_updated call_stack_updated debug_chain_updated []
                    in
                    computed
            in
            let collected_subchains = earliest_callvs >>= mapfunc in
            List.map ~f:(fun subchain -> subchain @ current_chain) collected_subchains
        and define_chains =
          List.filter
            ~f:(fun local_ap ->
              (not @@ is_return_ap local_ap)
              && (not @@ is_param_ap local_ap)
              && (not @@ is_callv_ap local_ap)
              && (not @@ is_returnv_ap local_ap) )
            local_aps
          >>= fun local_ap ->
          let other_statetup =
            search_target_tuple_by_vardef_ap local_ap current_methname current_astate_set
          in
          let real_aliastup_locset = find_most_recent_locset_of_ap local_ap current_astate_set in
          let new_chain_slice =
            (current_methname, Status.Define (current_methname, local_ap, real_aliastup_locset))
          in
          let chain_updated = new_chain_slice :: current_chain
          and debug_chain_updated = new_chain_slice :: debug_chain in
          (* recurse *)
          compute_chain_inner current_methname current_astate_set other_statetup chain_updated
            current_call_stack debug_chain_updated current_chain_acc
        in
        call_chains @ define_chains


let specify_returnv_for_define_slice_using_field (first_methname : Procname.t) (aliasset : A.t) :
    MyAccessPath.t option =
  let filtered_returnvs =
    A.filter
      (fun ap ->
        is_returnv_ap ap
        && not
           @@ ( return_type_is_void (extract_callee_from ap)
              && A.exists
                   (fun callv -> is_callv_ap callv && callv_and_returnv_matches ~callv ~returnv:ap)
                   aliasset ) )
      aliasset
  in
  match A.elements filtered_returnvs with
  | [] ->
      None
  | returnvs ->
      Some (find_earliest_returnv returnvs ~greater_than:0)


(** 콜 그래프와 분석 결과를 토대로 체인 (Define -> ... -> Dead)을 계산해 낸다 *)
let compute_chain_ (ap : MyAccessPath.t) : Chain.t list =
  let first_methname, first_astate_set, first_astate = find_first_occurrence_of ap in
  let first_aliasset, first_locset = (fourth_of first_astate, third_of first_astate) in
  let returnv_opt = specify_returnv_for_define_slice_using_field first_methname first_aliasset in
  let source_meth =
    match returnv_opt with Some returnv -> extract_callee_from returnv | None -> first_methname
  in
  compute_chain_inner first_methname first_astate_set first_astate
    [(first_methname, Define (source_meth, ap, first_locset))]
    [first_methname]
    [(first_methname, Define (source_meth, ap, first_locset))]
    []
  >>| rev


(** 본체인 compute_chain_을 포장하는 함수 *)
let compute_chain (ap : MyAccessPath.t) : Chain.t list =
  initialize_callv_counter () ;
  let first_methname, first_astate_set, first_astate = find_first_occurrence_of ap in
  L.progress "============ Computing Chain for %a at %a ============@." MyAccessPath.pp ap
    Procname.pp first_methname ;
  if Procname.equal first_methname Procname.empty_block then []
  else
    let first_aliasset = fourth_of first_astate in
    match A.exists is_returnv_ap first_aliasset with
    | true -> (
        (* 이미 어떤 chain의 subchain이라면 새로 계산할 필요 없음 *)
        let ap_locset = find_most_recent_locset_of_ap ap first_astate_set in
        let initial_chain_slice = Status.Define (first_methname, ap, ap_locset) in
        match find_entry_containing_chainslice first_methname initial_chain_slice with
        | [] ->
            (* 이전에 계산해 놓은 게 없네 *)
            compute_chain_ ap
        | chains ->
            (* 이전에 계산해 놓은 게 있네! 거기서 단순 추출만 해야지 *)
            map
              ~f:(fun chain -> extract_subchain_from chain (first_methname, initial_chain_slice))
              chains )
    | false ->
        compute_chain_ ap


(* I/O stuffs ======================================= *)
(* ================================================== *)

let collect_all_proc_and_ap () =
  let setofallstates = Hashtbl.fold (fun _ v acc -> S.union v acc) summary_table S.empty in
  let listofallstates = S.elements setofallstates in
  let list_of_all_proc_and_ap =
    listofallstates >>| fun (x : T.t) -> (first_of x, second_of x, third_of x)
  in
  list_of_all_proc_and_ap


(** 파일로 call graph를 출력 *)
let save_callgraph () =
  let ch = Out_channel.create "Callgraph.txt" in
  Hashtbl.iter
    (fun k v ->
      Out_channel.output_string ch @@ Procname.to_string k ^ " -> " ^ Procname.to_string v ^ "\n" )
    callgraph_table ;
  Out_channel.flush ch ;
  Out_channel.close ch


let extract_pvar_from_var (var : Var.t) : Pvar.t =
  match var with
  | LogicalVar _ ->
      F.kasprintf
        (fun msg -> raise @@ NotAPVar msg)
        "extract_pvar_from_var failed. var: %a@." Var.pp var
  | ProgramVar pv ->
      pv


(* Method for Jsons ======================== *)
(* ========================================= *)

(** 하나의 status에 대한 representation을 만든다. *)
let represent_status (current_method : Procname.t) (status : Status.t) : json =
  match status with
  | Define (callee, ap, locset) ->
      let locset_string = F.asprintf "%a" LocationSet.pp locset in
      `Assoc
        [ ("current_method", `String (Procname.to_string current_method))
        ; ("status", `String "Define")
        ; ("access_path", `String (MyAccessPath.to_string ap))
        ; ("location", `String locset_string)
        ; ("using", `String (Procname.to_string callee)) ]
  | Call (callee, ap, locset, _) ->
      let locset_string = F.asprintf "%a" LocationSet.pp locset in
      `Assoc
        [ ("current_method", `String (Procname.to_string current_method))
        ; ("status", `String "Call")
        ; ("callee", `String (Procname.to_string callee))
        ; ("location", `String locset_string)
        ; ("with", `String (MyAccessPath.to_string ap)) ]
  | VoidCall (callee, ap, locset, _) ->
      let locset_string = F.asprintf "%a" LocationSet.pp locset in
      `Assoc
        [ ("current_method", `String (Procname.to_string current_method))
        ; ("status", `String "VoidCall")
        ; ("callee", `String (Procname.to_string callee))
        ; ("location", `String locset_string)
        ; ("with", `String (MyAccessPath.to_string ap)) ]
  | Redefine (ap, locset) ->
      let locset_string = F.asprintf "%a" LocationSet.pp locset in
      `Assoc
        [ ("current_method", `String (Procname.to_string current_method))
        ; ("status", `String "Redefine")
        ; ("location", `String locset_string)
        ; ("access_path", `String (MyAccessPath.to_string ap)) ]
  | DeadByCycle ->
      `Assoc
        [ ("current_method", `String (Procname.to_string current_method))
        ; ("status", `String "DeadByCycle") ]
  | Dead ->
      `Assoc
        [("current_method", `String (Procname.to_string current_method)); ("status", `String "Dead")]


(** chain을 수식해서 ap에 관한 완전한 정보를 나타내는 Json object를 만든다. *)
let wrap_chain_representation (defining_method : Procname.t) (ap : MyAccessPath.t)
    (ap_locset : LocationSet.t) (chain_repr : json list) : json =
  `Assoc
    [ ("defining_method", `String (Procname.to_string defining_method))
    ; ("access_path", `String (MyAccessPath.to_string ap))
    ; ("location", `String (F.asprintf "%a" LocationSet.pp ap_locset))
    ; ("chain", `List chain_repr) ]


(** 수식된 chain들의 array를 만든다. *)
let make_complete_representation (wrapped_chains : json list) : json = `List wrapped_chains

let write_json (json : json) : unit =
  let out_channel = Out_channel.create "Chain.json" in
  pretty_to_channel out_channel json ;
  Out_channel.flush out_channel ;
  Out_channel.close out_channel


(* Main Method ============================= *)
(* ========================================= *)

let main () =
  (* ============ Preliminary moves ============ *)
  (* Initialize the callgraph_table *)
  MyCallGraph.load_callgraph_from_disk_to callgraph_table ~exclude_test:true ;
  save_callgraph () ;
  (* Initialize the summary_table *)
  SummaryLoader.load_summary_from_disk_to summary_table ~exclude_test:true ;
  RefineSummaries.main summary_table ;
  (* Initialize the formal_args table *)
  batch_add_formal_args () ;
  save_APIs () ;
  (* Filter the callgraph_table *)
  filter_callgraph_table callgraph_table ;
  (* Initialize OCamlgraph *)
  callg_hash2og () ;
  graph_to_dot callgraph ~filename:"callgraph_with_astate_refined.dot" ;
  (* ============ Computing Chains ============ *)
  stable_dedup @@ collect_all_proc_and_ap ()
  |> filter ~f:(fun (proc, (var, _), _) ->
         (not @@ is_initializer proc)
         && (not @@ Var.is_this var)
         && (not @@ is_placeholder_vardef var)
         && (not @@ Pvar.is_frontend_tmp @@ extract_pvar_from_var var)
         && (not @@ is_returnv var)
         && (not @@ Var.is_return var)
         && (not @@ is_param var)
         && (not @@ is_callv var)
         && (not @@ is_inner_class_proc proc) )
  |> iter ~f:(fun (proc, ap, locset) ->
         let computed_chains = compute_chain ap in
         iter ~f:(fun chain -> add_chain (proc, ap, locset) chain) computed_chains ) ;
  (* ============ Serialize ============ *)
  let wrapped_chains =
    Hashtbl.fold
      (fun (current_meth, target_ap, target_ap_locset) chain acc ->
        wrap_chain_representation current_meth target_ap target_ap_locset
          (map ~f:(fun (proc, status) -> represent_status proc status) chain)
        :: acc )
      chains []
  in
  let complete_json_representation = make_complete_representation wrapped_chains in
  write_json complete_json_representation
