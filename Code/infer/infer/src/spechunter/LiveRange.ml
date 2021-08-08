open! IStd
open DefLocAliasSearches
open DefLocAliasPredicates
open DefLocAliasDomain
open DefLocAliasPP
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

exception CouldNotExtractCallee of string

exception ReturnvFindFailed of string

exception TooManyMatches of string

exception NoMatches of string

exception NoStateTupHoldingAliasTup of string

exception NoSuchElem of string

exception NoWitness of string

exception ChainComputeFailed of string

exception NotAPVar of string

(* Types ============================================ *)
(* ================================================== *)

module Status = struct
  type t =
    | Define of (Procname.t * MyAccessPath.t)
    | Call of (Procname.t * MyAccessPath.t)
    | Redefine of MyAccessPath.t
    | Dead
  [@@deriving equal]

  let pp fmt x =
    match x with
    | Define (proc, ap) ->
        F.fprintf fmt "Define (%a using %a)" MyAccessPath.pp ap Procname.pp proc
    | Call (proc, ap) ->
        F.fprintf fmt "Call (%a with %a)" Procname.pp proc MyAccessPath.pp ap
    | Redefine ap ->
        F.fprintf fmt "Redefine (%a)" MyAccessPath.pp ap
    | Dead ->
        F.fprintf fmt "Dead"
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
module PairOfMS = struct
  include Pair (Procname) (S)

  type t = Procname.t * S.t

  let hash = Hashtbl.hash
end

(*  Pretty Printers ================================= *)
(* ================================================== *)

let pp_pair fmt (proc, v) = F.fprintf fmt "(%a, %a) ->" Procname.pp proc Status.pp v

let pp_chain fmt x = Pp.seq pp_pair fmt x

let pp_MyAccessChain fmt (var, aplist) = F.fprintf fmt "(%a, %a)" Var.pp var pp_ap_list aplist

let string_of_vertex (proc, astateset) = F.asprintf "\"(%a, %a)\"" Procname.pp proc S.pp astateset

(** specially mangled variable to mark a value as returned from callee *)
let mk_returnv procname =
  Var.of_pvar @@ Pvar.mk (Mangled.from_string @@ "returnv: " ^ Procname.to_string procname) procname


(* Ocamlgraph Definitions =========================== *)
(* ================================================== *)

module G = struct
  include Graph.Imperative.Digraph.ConcreteBidirectional (PairOfMS)

  let graph_attributes _ = []

  let default_vertex_attributes _ = []

  let vertex_name (vertex : V.t) : string = string_of_vertex vertex

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
      L.progress "summary: %a@." S.pp summary)
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
      L.progress "\n")
    formal_args


(* Procname and their callv counters ================ *)
(* ================================================== *)

let procname_callv_counter : (Procname.t, int) Hashtbl.t = Hashtbl.create 777

let initialize_callv_counter () =
  let procnames = Hashtbl.fold (fun k v acc -> k :: acc) summary_table [] in
  iter ~f:(fun procname -> Hashtbl.add procname_callv_counter procname 0) procnames


let get_counter (procname : Procname.t) = Hashtbl.find procname_callv_counter procname

let update_counter (procname : Procname.t) (new_counter : int) =
  Hashtbl.replace procname_callv_counter procname new_counter


(* CallGraph ======================================== *)
(* ================================================== *)

(** a tabular representation of the call graph. *)
let callgraph_table = Hashtbl.create 777

let callgraph = G.create ()

let chains = Hashtbl.create 777

(** Procname과 AP로부터 chain으로 가는 Hash table *)
let add_chain (key : Procname.t * MyAccessPath.t) (value : Chain.t) = Hashtbl.add chains key value

(** Function for debugging by exporting Ocamlgraph to Graphviz Dot *)
let graph_to_dot (graph : G.t) ?(filename = "callgraph_with_astate.dot") : unit =
  let out_channel = Out_channel.create filename in
  Dot.output_graph out_channel graph ;
  Out_channel.flush out_channel ;
  Out_channel.close out_channel


(** 해시 테이블 형태의 콜그래프를 ocamlgraph로 변환한다. *)
let callg_hash2og () : unit =
  Hashtbl.iter
    (fun key value ->
      let key_astate_set = get_summary key in
      let value_astate_set = get_summary value in
      G.add_edge callgraph (key, key_astate_set) (value, value_astate_set))
    callgraph_table


(** 주어진 hashtbl의 엔트리 중에서 (callgraph_table이 쓰일 것) summary_table에 있지
    않은 엔트리를 날린다. *)
let filter_callgraph_table hashtbl : unit =
  let procs = Hashtbl.fold (fun k _ acc -> k :: acc) summary_table [] in
  Hashtbl.iter
    (fun k v ->
      if (not @@ mem procs k ~equal:Procname.equal) && (not @@ mem procs v ~equal:Procname.equal)
      then Hashtbl.remove hashtbl k)
    hashtbl


(** 중복 튜플을 제거함 *)
let remove_duplicates_from (astate_set : S.t) : S.t =
  let partitioned_by_duplicates = P.partition_tuples_modulo_123 astate_set in
  (* 위의 리스트 안의 각 리스트들 안에 들어 있는 튜플들 중 가장 alias set이 큰 놈을 남김 *)
  let leave_tuple_with_biggest_aliasset lst =
    if length lst > 1 then
      fold_left lst ~init:bottuple ~f:(fun (acc : T.t) (elem : T.t) ->
          if Int.( < ) (A.cardinal @@ fourth_of acc) (A.cardinal @@ fourth_of elem) then elem
          else acc)
    else nth_exn lst 0
  in
  let result = partitioned_by_duplicates >>| leave_tuple_with_biggest_aliasset |> S.of_list in
  S.filter
    (fun tup ->
      let var, _ = second_of tup in
      (not @@ is_placeholder_vardef var) && (not @@ Var.is_this var))
    result


(** 디버깅 용도로 BFS 사용해서 그래프 출력하기 *)
let print_graph graph =
  BFS.iter
    (fun (proc, astate_set) ->
      L.progress "proc: %a, astate_set: %a@." Procname.pp proc S.pp astate_set)
    graph


(* Computing Chains ================================= *)
(* ================================================== *)

(** 주어진 AccessPath ap에 있어 가장 이른 정의 state를 찾는다. *)
let find_first_occurrence_of (ap : MyAccessPath.t) : Procname.t * S.t * S.elt =
  let astate_set =
    BFS.fold
      (fun (_, astate) acc ->
        match S.exists (fun tup -> MyAccessPath.equal (second_of tup) ap) astate with
        | true ->
            astate
        | false ->
            acc)
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
      let earliest_state = find_earliest_astate_within targetTuples methname in
      (methname, astate_set, earliest_state)


(** alias set에서 자기 자신, ph, 직전 variable을 빼고 남은 program variable들을
    리턴 *)
let collect_program_var_aps_from (aliasset : A.t) ~(self : MyAccessPath.t)
    ~(just_before : MyAccessPath.t option) : MyAccessPath.t list =
  match just_before with
  | Some just_before ->
      filter ~f:(fun x ->
          is_program_var (fst x)
          && (not @@ MyAccessPath.equal self x)
          (* not @@ Var.is_this (fst x) && *)
          && (not @@ is_placeholder_vardef (fst x))
          && (not @@ MyAccessPath.equal just_before x))
      @@ A.elements aliasset
  | None ->
      filter ~f:(fun x ->
          is_program_var (fst x)
          && (not @@ MyAccessPath.equal self x)
          && (* not @@ Var.is_this (fst x) && *)
          (not @@ is_placeholder_vardef (fst x)))
      @@ A.elements aliasset


(** Find the immediate callers and their summaries of the given Procname.t. *)
let find_direct_callers (target_meth : Procname.t) : (Procname.t * S.t) list =
  let target_vertex = (target_meth, get_summary target_meth) in
  G.pred callgraph target_vertex


(** Find the immediate callees and their summaries of the given Procname.t. *)
let find_direct_callees (target_meth : Procname.t) : (Procname.t * S.t) list =
  let target_vertex = (target_meth, get_summary target_meth) in
  G.succ callgraph target_vertex


(** Is the Chain.chain_slice already in the given chain? *)
let have_been_before (chain_slice : Chain.chain_slice) (chain : Chain.t) : bool =
  List.mem chain chain_slice ~equal:Chain.equal_chain_slice


let is_skip_function (methname : Procname.t) : bool = Option.is_none @@ Procdesc.load methname

let save_skip_function () : unit =
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
            acc)
      callgraph_table Procname.Set.empty
  in
  let out_chan = Out_channel.create "skip_func.txt" in
  let procnames_list = Procname.Set.elements procnames in
  iter
    ~f:(fun procname ->
      let func_name = Procname.to_string procname in
      Out_channel.output_string out_chan @@ func_name ^ "\n")
    procnames_list ;
  Out_channel.close out_chan


(** Extract the callee's method name embedded in returnv, callv, or param. *)
let extract_callee_from (ap : MyAccessPath.t) =
  let special, _ = ap in
  match special with
  | LogicalVar _ ->
      F.kasprintf
        (fun msg -> raise @@ CouldNotExtractCallee msg)
        "extract_callee_from failed. ap: %a@." MyAccessPath.pp ap
  | ProgramVar pv -> (
    match Pvar.get_declaring_function pv with
    | Some procname ->
        procname
    | None ->
        F.kasprintf
          (fun msg -> raise @@ CouldNotExtractCallee msg)
          "extract_callee_from failed. ap: %a@." MyAccessPath.pp ap )


let extract_ap_from_chain_slice (slice : (Procname.t * Status.t) option) : MyAccessPath.t option =
  match slice with
  | Some (_, status) -> (
    match status with
    | Define (_, ap) ->
        Some ap
    | Call (_, ap) ->
        None
    | Redefine ap ->
        Some ap
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


(** chain과 chain_slice를 받아, chain_slice가 있는 지점부터 시작되는 subchain을
    꺼내 온다. 실패하면 empty list. *)
let extract_subchain_from (chain : Chain.t) (chain_slice : Chain.chain_slice) : Chain.t =
  let index = find_index_in_chain chain chain_slice in
  match index with
  | -1 ->
      []
  | _ ->
      let subchain_length = length chain - index in
      sub chain ~pos:index ~len:subchain_length


(** Define에 들어 있는 Procname과 AP의 쌍을 받아서 그것이 들어 있는 chain을
    리턴 *)
let find_entry_containing_chainslice (methname : Procname.t) (status : Status.t) : Chain.t option =
  let all_chains = Hashtbl.fold (fun _ v acc -> v :: acc) chains [] in
  let result_chains =
    fold
      ~f:(fun acc chain -> if have_been_before (methname, status) chain then chain :: acc else acc)
      ~init:[] all_chains
  in
  nth result_chains 0


let count_vardefs_in_astateset ~(find_this : MyAccessPath.t) (astate_set : S.t) : int =
  S.fold
    (fun astate cnt -> if MyAccessPath.equal find_this (second_of astate) then cnt + 1 else cnt)
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
  let out =
    S.fold
      (fun statetup acc ->
        let aliasset = fourth_of statetup in
        try
          let returnv = find_returnv_holding_callee_aliasset callee_name aliasset in
          returnv :: acc
        with _ -> acc)
      astate_set []
  in
  if Int.( > ) (length out) 1 then
    F.kasprintf
      (fun msg -> raise @@ TooManyMatches msg)
      "find_returnv_holding_callee_astateset failed. callee_name: %a, astate_set: %a@." Procname.pp
      callee_name S.pp astate_set
  else if Int.equal (length out) 0 then
    F.kasprintf
      (fun msg -> raise @@ NoMatches msg)
      "find_returnv_holding_callee_astateset failed. callee_name: %a, astate_set: %a@." Procname.pp
      callee_name S.pp astate_set
  else hd_exn out


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
      let methname = extract_callee_from ap in
      is_returnv_ap ap && Procname.equal methname callee_methname)
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


(** Find the *first* element to match the predicate *)
let find_witness_exn (lst : 'a list) ~(pred : 'a -> bool) : 'a =
  let opt =
    fold_left ~f:(fun acc elem -> if pred elem then Some elem else acc) ~init:None @@ rev lst
  in
  match opt with
  | None ->
      F.kasprintf (fun msg -> raise @@ NoWitness msg) "find_witness_exn failed.@."
  | Some elem ->
      elem


let get_declaring_function_ap (ap : A.elt) : Procname.t option =
  let var, _ = ap in
  match var with
  | LogicalVar _ ->
      None
  | ProgramVar pvar -> (
    match Pvar.get_declaring_function pvar with None -> None | Some procname -> Some procname )


let find_matching_param_for_callv (ap_set : A.t) (callv_ap : A.elt) : A.elt =
  let callee_methname = extract_callee_from callv_ap in
  let callee_params = get_formal_args callee_methname in
  let param_aps_in_this_set =
    if is_empty callee_params then
      A.filter
        (fun ap ->
          let methname = extract_callee_from ap in
          is_param_ap ap && Procname.equal methname callee_methname)
        ap_set
    else A.filter (fun ap -> List.mem callee_params ap ~equal:MyAccessPath.equal) ap_set
  in
  match A.elements param_aps_in_this_set with
  | [] ->
      F.kasprintf
        (fun msg -> raise @@ NoMatches msg)
        "find_matching_param_for_callv failed. ap_set: %a, callv_ap: %a@." A.pp ap_set
        MyAccessPath.pp callv_ap
  | [ap] ->
      ap
  | _ ->
      F.kasprintf
        (fun msg -> raise @@ TooManyMatches msg)
        "find_matching_param_for_callv failed. ap_set: %a, callv_ap: %a@." A.pp ap_set
        MyAccessPath.pp callv_ap


let rec compute_chain_inner (current_methname : Procname.t) (current_astate_set : S.t)
    (current_astate : S.elt) (current_chain : Chain.t) : Chain.t =
  let ap_filter tup =
    (not @@ is_logical_var @@ fst tup) && (not @@ is_frontend_tmp_var @@ fst tup)
  in
  let current_aliasset = fourth_of current_astate in
  let current_aliasset_cleanedup = A.filter ap_filter @@ current_aliasset in
  let current_vardef = second_of current_astate in
  (* 직전에 방문했던 astate에서 끄집어낸 variable *)
  let just_before_procname : Procname.t = fst @@ hd_exn current_chain in
  let just_before_ap_opt : A.elt option = extract_ap_from_chain_slice @@ hd current_chain in
  let var_aps =
    collect_program_var_aps_from current_aliasset_cleanedup ~self:current_vardef
      ~just_before:just_before_ap_opt
  in
  let callees = find_direct_callees current_methname in
  let statetup_with_returnv_or_carriedovers =
    fold
      ~f:(fun acc (_, callee_astate_set) ->
        acc @ find_returnv_or_carriedover_ap current_astate_set callee_astate_set)
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
              && (not @@ is_frontend_tmp_var var)
              && (not @@ is_returnv var)
              && (not @@ Var.is_return var)
              && (not @@ is_callv var)
              && (not @@ is_param var)
              && (not @@ mem statetup_with_returnv_or_carriedovers ~equal:MyAccessPath.equal ap)
        | Some just_before ->
            fun ap ->
              let var = fst ap in
              (not @@ is_logical_var var)
              && (not @@ is_frontend_tmp_var var)
              && (not @@ is_returnv var)
              && (not @@ Var.is_return var)
              && (not @@ is_callv var)
              && (not @@ is_param var)
              && (not @@ MyAccessPath.equal just_before ap)
              && (not @@ mem statetup_with_returnv_or_carriedovers ~equal:MyAccessPath.equal ap) )
      var_aps
  in
  L.progress "============ current_methname: %a, something_else: %a, current_chain: %a@."
    Procname.pp current_methname pp_ap_list something_else pp_chain (rev current_chain) ;
  match something_else with
  | [] ->
      if S.is_empty current_astate_set then
        (* This is an Library API function *)
        let just_before_astate_set = get_summary just_before_procname in
        let just_before_astate_set_has_returnv =
          S.exists
            (fun statetup -> alias_with_returnv statetup current_methname)
            just_before_astate_set
        in
        if just_before_astate_set_has_returnv then
          let target_returnv = (mk_returnv current_methname, []) in
          let aliased_with_returnv : S.elt =
            find_statetup_holding_aliastup just_before_astate_set target_returnv
          in
          let chain_updated =
            (just_before_procname, Status.Define (current_methname, second_of aliased_with_returnv))
            :: current_chain
          in
          compute_chain_inner just_before_procname just_before_astate_set aliased_with_returnv
            chain_updated
        else
          let current_node = (current_methname, current_astate_set) in
          let is_leaf = is_empty @@ G.succ callgraph current_node in
          if is_leaf then (current_methname, Dead) :: current_chain else current_chain
        (* (current_methname, Dead) :: current_chain *)
        (* the following if-then-else sequences encodes
           the level of preferences among different A.elt's. *)
      else if exists ~f:(fun (var, _) -> Var.is_return var) var_aps then
        let callers_and_astates = find_direct_callers current_methname in
        (* ============ DEFINITION AT THE CALLER ============ *)
        let collected =
          fold
            ~f:(fun acc (caller, caller_astate_set) ->
              let returnv_aliastup =
                find_returnv_holding_callee_astateset current_methname caller_astate_set
              in
              let statetup_with_returnv =
                find_statetup_holding_aliastup caller_astate_set returnv_aliastup
              in
              let chain_updated =
                (caller, Status.Define (current_methname, second_of statetup_with_returnv)) :: acc
              in
              (* recurse *)
              compute_chain_inner caller caller_astate_set statetup_with_returnv chain_updated)
            ~init:[] callers_and_astates
        in
        collected @ current_chain
      else if exists ~f:(fun ap -> is_callv_ap ap) var_aps then (
        (* ============ CALL ============ *)
        (* Retrieve and update the callv counter. *)
        let callv_counter = get_counter current_methname in
        let this_turn_callv_ap = find_callv_greater_than_number (A.of_list var_aps) callv_counter in
        update_counter current_methname (extract_number_from_callv this_turn_callv_ap) ;
        (* now, find the matching param_ap. *)
        let param_ap_matching_callv =
          find_matching_param_for_callv (A.of_list var_aps) this_turn_callv_ap
        in
        let callee_methname = extract_callee_from param_ap_matching_callv in
        let new_chain_slice =
          (current_methname, Status.Call (callee_methname, param_ap_matching_callv))
        in
        let chain_updated = new_chain_slice :: current_chain in
        let callee_astate_set = get_summary callee_methname in
        if is_param_ap param_ap_matching_callv then
          (* API Call *)
          compute_chain_inner callee_methname callee_astate_set bottuple chain_updated
        else
          (* UDF call *)
          let param_statetup =
            search_target_tuple_by_pvar_ap param_ap_matching_callv callee_methname callee_astate_set
          in
          compute_chain_inner callee_methname callee_astate_set param_statetup chain_updated )
      else if
        (* either REDEFINITION or DEAD.
           check which one is the case by checking if there are multiple current_vardefs in the alias set *)
        Int.( >= ) (count_vardefs_in_astateset ~find_this:current_vardef current_astate_set) 2
      then
        (* ============ REDEFINITION ============ *)
        (* Intuition: get to the least recently redefined variable and recurse on that *)
        let all_states_with_current_ap =
          sort ~compare:compare_astate
          @@ filter ~f:(fun astate ->
                 MyAccessPath.equal (second_of current_astate) (second_of astate))
          @@ S.elements current_astate_set
        in
        let least_recently_redefined =
          next_elem_of_list all_states_with_current_ap ~next_to:current_astate
        in
        let current_ap = second_of current_astate in
        let current_astate_set_updated = S.remove current_astate current_astate_set in
        (* remove the current_astate from current_astate_set *)
        let chain_updated = (current_methname, Status.Redefine current_ap) :: current_chain in
        (* recurse *)
        compute_chain_inner current_methname current_astate_set_updated least_recently_redefined
          chain_updated
      else
        (* ============ DEAD ============ *)
        (* no more recursion; return *)
        (current_methname, Dead) :: current_chain
  | [real_aliastup] ->
      let declaring_function = option_get @@ get_declaring_function_ap real_aliastup in
      let callees_and_astates = find_direct_callees current_methname in
      if not @@ Procname.equal declaring_function current_methname then
        (* ============ CALL ============ *)
        (* TODO: 여기 보강 *)
        let collected =
          fold
            ~f:(fun acc (callee, callee_astate) ->
              try
                let landing_pad =
                  search_target_tuple_by_vardef_ap real_aliastup callee callee_astate
                in
                let chain_updated =
                  (current_methname, Status.Call (callee, real_aliastup)) :: acc
                in
                compute_chain_inner callee callee_astate landing_pad chain_updated
              with SearchAstateByPVarFailed _ -> acc)
            ~init:[] callees_and_astates
        in
        collected @ current_chain
      else
        (* ============ SIMPLE DEFINITION ============ *)
        let other_statetup =
          search_target_tuple_by_pvar_ap real_aliastup current_methname current_astate_set
        in
        let chain_updated =
          (current_methname, Status.Define (current_methname, real_aliastup)) :: current_chain
        in
        (* recurse *)
        compute_chain_inner current_methname current_astate_set other_statetup chain_updated
  | otherwise ->
      F.kasprintf
        (fun msg -> raise @@ ChainComputeFailed msg)
        {|computer_chain_inner failed:
          current_methname: %a,
          current_astate_set: %a,
          current_astate: %a,
          current_chain: %a|}
        Procname.pp current_methname S.pp current_astate_set T.pp current_astate pp_chain
        current_chain


(** 콜 그래프와 분석 결과를 토대로 체인 (Define -> ... -> Dead)을 계산해 낸다 *)
let compute_chain_ (ap : MyAccessPath.t) : Chain.t =
  let first_methname, first_astate_set, first_astate = find_first_occurrence_of ap in
  let first_aliasset = fourth_of first_astate in
  let returnv_opt = A.find_first_opt is_returnv_ap first_aliasset in
  let source_meth =
    match returnv_opt with Some returnv -> extract_callee_from returnv | None -> first_methname
  in
  rev
  @@ compute_chain_inner first_methname first_astate_set first_astate
       [(first_methname, Define (source_meth, ap))]


(** 본체인 compute_chain_을 포장하는 함수 *)
let compute_chain (ap : MyAccessPath.t) : Chain.t =
  initialize_callv_counter () ;
  let first_methname, _, first_astate = find_first_occurrence_of ap in
  if Procname.equal first_methname Procname.empty_block then []
  else
    let first_aliasset = fourth_of first_astate in
    match A.exists is_returnv_ap first_aliasset with
    | true -> (
        (* 이미 어떤 chain의 subchain이라면 새로 계산할 필요 없음 *)
        let initial_chain_slice = Status.Define (first_methname, ap) in
        match find_entry_containing_chainslice first_methname initial_chain_slice with
        | None ->
            (* 이전에 계산해 놓은 게 없네 *)
            compute_chain_ ap
        | Some chain ->
            (* 이전에 계산해 놓은 게 있네! 거기서 단순 추출만 해야지 *)
            extract_subchain_from chain (first_methname, initial_chain_slice) )
    | false ->
        compute_chain_ ap


let collect_all_proc_and_ap () =
  let setofallstates = Hashtbl.fold (fun _ v acc -> S.union v acc) summary_table S.empty in
  let listofallstates = S.elements setofallstates in
  let list_of_all_proc_and_ap = listofallstates >>| fun (x : T.t) -> (first_of x, second_of x) in
  list_of_all_proc_and_ap


(** 파일로 call graph를 출력 *)
let save_callgraph () =
  let ch = Out_channel.create "Callgraph.txt" in
  Hashtbl.iter
    (fun k v ->
      Out_channel.output_string ch @@ Procname.to_string k ^ " -> " ^ Procname.to_string v ^ "\n")
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
  | Define (callee, ap) ->
      `Assoc
        [ ("current_method", `String (Procname.to_string current_method))
        ; ("status", `String "Define")
        ; ("access_path", `String (MyAccessPath.to_string ap))
        ; ("using", `String (Procname.to_string callee)) ]
  | Call (callee, ap) ->
      `Assoc
        [ ("current_method", `String (Procname.to_string current_method))
        ; ("status", `String "Call")
        ; ("callee", `String (Procname.to_string callee))
        ; ("with", `String (MyAccessPath.to_string ap)) ]
  | Redefine ap ->
      `Assoc
        [ ("current_method", `String (Procname.to_string current_method))
        ; ("status", `String "Redefine")
        ; ("access_path", `String (MyAccessPath.to_string ap)) ]
  | Dead ->
      `Assoc
        [("current_method", `String (Procname.to_string current_method)); ("status", `String "Dead")]


(** chain을 수식해서 ap에 관한 완전한 정보를 나타내는 Json object를 만든다. *)
let wrap_chain_representation defining_method ap (chain_repr : json list) : json =
  `Assoc
    [ ("defining_method", `String (Procname.to_string defining_method))
    ; ("access_path", `String (MyAccessPath.to_string ap))
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
  MyCallGraph.load_callgraph_from_disk_to callgraph_table ;
  save_callgraph () ;
  (* Initialize the summary_table *)
  SummaryLoader.load_summary_from_disk_to summary_table ;
  RefineSummaries.main summary_table ;
  (* Initialize the formal_args table *)
  batch_add_formal_args () ;
  save_skip_function () ;
  (* Filter the callgraph_table *)
  filter_callgraph_table callgraph_table ;
  (* Initialize OCamlgraph *)
  callg_hash2og () ;
  graph_to_dot callgraph ~filename:"callgraph_with_astate_refined.dot" ;
  (* ============ Computing Chains ============ *)
  stable_dedup @@ collect_all_proc_and_ap ()
  |> filter ~f:(fun (_, (var, _)) ->
         let pv = extract_pvar_from_var var in
         (not @@ Var.is_this var)
         && (not @@ is_placeholder_vardef var)
         && (not @@ Pvar.is_frontend_tmp pv)
         && (not @@ is_returnv var)
         && (not @@ Var.is_return var)
         && (not @@ is_param var)
         && (not @@ is_callv var))
  |> iter ~f:(fun (proc, ap) -> add_chain (proc, ap) @@ compute_chain ap) ;
  (* |> iter ~f:(fun (proc, ap) ->
   *        if
   *          String.equal (Procname.to_string proc) "void WhatIWantExample.f()"
   *          && String.equal (F.asprintf "%a" Var.pp (fst ap)) "x"
   *        then add_chain (proc, ap) @@ compute_chain ap) ; *)
  (* ============ Serialize ============ *)
  let wrapped_chains =
    Hashtbl.fold
      (fun (current_meth, target_ap) chain acc ->
        wrap_chain_representation current_meth target_ap
          (map ~f:(fun (proc, status) -> represent_status proc status) chain)
        :: acc)
      chains []
  in
  let complete_json_representation = make_complete_representation wrapped_chains in
  write_json complete_json_representation
