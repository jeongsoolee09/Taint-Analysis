(** Domain for Interprocedural DFA. *)
open! IStd

module F = Format
module L = Logging

(** astate_set = Set of (defined variable, location of definition, Aliased Variables including both
    logical and program variables) *)

(** An tuple (element of an astate_set) represents a single data definition *)

module MyAccessPath = struct
  type t = Var.t * AccessPath.access list [@@deriving equal, compare]

  let pp fmt (x : t) =
    let var, list = x in
    F.fprintf fmt "(%a, [" Var.pp var ;
    List.iter list ~f:(fun access -> F.fprintf fmt "%a, " AccessPath.pp_access access) ;
    F.fprintf fmt "])"


  let equal (x : t) (y : t) : bool =
    let xvar, xlist = x in
    let yvar, ylist = y in
    Var.equal xvar yvar && List.equal AccessPath.equal_access xlist ylist


  let to_string (x : t) : string = F.asprintf "%a" pp x
end

(** set of locations (source-code level) where pieces of data are defined. *)
module LocationSet = AbstractDomain.FiniteSet (Location)

(** Set of AccessPath (with either Logical or Programs Vars) in an alias relationship. *)
module SetofAliases = struct
  include AbstractDomain.FiniteSet (MyAccessPath)

  let strong_update (set : t) (old : elt) (fresh : elt) : t =
    let set_rmvd = remove old set in
    add fresh set_rmvd
end

let doubleton (a : SetofAliases.elt) (b : SetofAliases.elt) : SetofAliases.t =
  let aset = SetofAliases.singleton a in
  let bset = SetofAliases.singleton b in
  SetofAliases.union aset bset


(** The Quadruple of the above four. *)
module Quadruple
    (Domain1 : module type of Procname)
    (Domain2 : module type of MyAccessPath)
    (Domain3 : module type of LocationSet)
    (Domain4 : module type of SetofAliases) =
struct
  type t = Domain1.t * Domain2.t * Domain3.t * Domain4.t [@@deriving equal, compare]
end

module QuadrupleWithPP = struct
  include Quadruple (Procname) (MyAccessPath) (LocationSet) (SetofAliases)

  let pp : F.formatter -> t -> unit =
   fun fmt (methname, vardefs, defloc, aliasset) ->
    F.fprintf fmt "(%a, %a, %a, %a)" Procname.pp methname MyAccessPath.pp vardefs LocationSet.pp
      defloc SetofAliases.pp aliasset
end

(** Pair of Procname.t and MyAccessPath.t *)
module ProcAccess = struct
  type t = Procname.t * MyAccessPath.t [@@deriving compare]

  let pp fmt (proc, ap) = F.fprintf fmt "(%a, %a)" Procname.pp proc MyAccessPath.pp ap
end

(** A map from ProcAccess.t to LocationSet.t. *)
module HistoryMap = struct
  include AbstractDomain.WeakMap (ProcAccess) (LocationSet)

  let add_to_history (key : Procname.t * MyAccessPath.t) (value : LocationSet.t) (history : t) : t =
    add key value history


  let batch_add_to_history (keys : (Procname.t * MyAccessPath.t) list) (loc : LocationSet.t)
      (history : t) : t =
    let rec batch_add_to_history_inner (keys : (Procname.t * MyAccessPath.t) list)
        (loc : LocationSet.t) (current_map : t) : t =
      match keys with
      | [] ->
          current_map
      | h :: t ->
          batch_add_to_history_inner t loc (add_to_history h loc current_map)
    in
    batch_add_to_history_inner keys loc history


  (** find the most recent location of the given key in the map of a T.t *)
  let get_most_recent_loc (key : Procname.t * MyAccessPath.t) (history : t) : LocationSet.t =
    find key history


  let batch_add_to_history2 (keys_and_loc : ((Procname.t * MyAccessPath.t) * LocationSet.t) list)
      (history : t) : t =
    let rec batch_add_to_history2_inner
        (keys_and_loc : ((Procname.t * MyAccessPath.t) * LocationSet.t) list) (current_map : t) =
      match keys_and_loc with
      | [] ->
          current_map
      | (keys, locset) :: t ->
          batch_add_to_history2_inner t (add_to_history keys locset current_map)
    in
    batch_add_to_history2_inner keys_and_loc history
end

(* An Abtract State is just a quadruple. *)
module AbstractState = QuadrupleWithPP

(** A set of Abstract States. *)
module AbstractStateSetFinite = struct
  include AbstractDomain.FiniteSet (AbstractState)

  let strong_update (set : t) (old : elt) (fresh : elt) : t =
    let set_rmvd = remove old set in
    add fresh set_rmvd
end

(* The pair of 1) set of abstract states and 2) the history map *)
module AbstractPair = struct
  include AbstractDomain.Pair (AbstractStateSetFinite) (HistoryMap)

  let pp fmt (a, b) = F.fprintf fmt "(%a, %a)" AbstractStateSetFinite.pp a HistoryMap.pp b

  module S = AbstractStateSetFinite
  module T = AbstractState
  module A = SetofAliases

  let placeholder_vardef (pid : Procname.t) : Var.t =
    let mangled = Mangled.from_string "ph" in
    let ph_vardef = Pvar.mk mangled pid in
    Var.of_pvar ph_vardef


  let bottuple =
    ( Procname.empty_block
    , (placeholder_vardef Procname.empty_block, [])
    , LocationSet.empty
    , SetofAliases.empty )


  let get_declaring_function_ap_exn (ap : A.elt) : Procname.t =
    let var, _ = ap in
    match var with
    | LogicalVar _ ->
        L.die InternalError "get_declaring_function_ap_exn failed: %a@." MyAccessPath.pp ap
    | ProgramVar pvar -> (
      match Pvar.get_declaring_function pvar with
      | None ->
          L.die InternalError "get_declaring_function_ap_exn failed: %a@." MyAccessPath.pp ap
      | Some procname ->
          procname )


  let leq ~lhs:(a, _) ~rhs:(b, _) =
    let is_callv_ap (ap : A.elt) : bool =
      let var, _ = ap in
      match var with
      | LogicalVar _ ->
          false
      | ProgramVar pv ->
          String.is_substring (Pvar.to_string pv) ~substring:"callv"
    in
    let is_returnv_ap (ap : A.elt) : bool =
      let var, _ = ap in
      match var with
      | LogicalVar _ ->
          false
      | ProgramVar pv ->
          String.is_substring (Pvar.to_string pv) ~substring:"returnv"
    in
    let if_callv_then_remove_number (ap : MyAccessPath.t) : MyAccessPath.t =
      if is_callv_ap ap then
        let callee_name = get_declaring_function_ap_exn ap in
        let var =
          Var.of_pvar
          @@ Pvar.mk
               (Mangled.from_string @@ F.asprintf "callv: %a" Procname.pp callee_name)
               callee_name
        in
        (var, [])
      else ap
    in
    let if_returnv_then_remove_number (ap : MyAccessPath.t) : MyAccessPath.t =
      if is_returnv_ap ap then
        let callee_name = get_declaring_function_ap_exn ap in
        let var =
          Var.of_pvar
          @@ Pvar.mk
               (Mangled.from_string @@ F.asprintf "returnv: %a" Procname.pp callee_name)
               callee_name
        in
        (var, [])
      else ap
    in
    let preprocess_astate_set (astate_set : S.t) : S.t =
      S.map
        (fun (proc, vardef, locset, aliasset) ->
          (proc, vardef, locset, A.map (fun ap ->
                                         if_returnv_then_remove_number @@
                                           if_callv_then_remove_number ap) aliasset))
        astate_set
    in
    let new_a, new_b = (preprocess_astate_set a, preprocess_astate_set b) in
    S.subset new_a new_b


  (* Utility Functions *)
  let first_of (a, _, _, _) = a

  let second_of (_, b, _, _) = b

  let third_of (_, _, c, _) = c

  let fourth_of (_, _, _, d) = d

  let double_equal (tup1 : T.t) (tup2 : T.t) =
    Procname.equal (first_of tup1) (first_of tup2)
    && MyAccessPath.equal (second_of tup1) (second_of tup2)


  (** finds state tuples with same methname and AP in s1 and s2 *)
  let find_duplicate_keys (s1: S.t) (s2: S.t) : S.t =
    let s1_elements = S.elements s1 in
    let s2_elements = S.elements s2 in
    let list_intersection_modulo_firstsecond l1 l2 =
      let l1_elems_in_l2 =
        S.of_list
        @@ List.fold
             ~f:(fun acc elem -> if List.mem l2 elem ~equal:double_equal then elem :: acc else acc)
             ~init:[] l1
      in
      let l2_elems_in_l1 =
        S.of_list
        @@ List.fold
             ~f:(fun acc elem -> if List.mem l1 elem ~equal:double_equal then elem :: acc else acc)
             ~init:[] l2
      in
      S.union l1_elems_in_l2 l2_elems_in_l1
    in
    list_intersection_modulo_firstsecond s1_elements s2_elements


  let double_equal (proc1, ap1) (proc2, ap2) =
    Procname.equal proc1 proc2 && MyAccessPath.equal ap1 ap2


  let triple_equal (proc1, ap1, locset1) (proc2, ap2, locset2) =
    Procname.equal proc1 proc2 && MyAccessPath.equal ap1 ap2 && LocationSet.equal locset1 locset2


  (** astate로부터 (procname, vardef, location) 쌍을 중복 없이 만든다. *)
  let get_keys astate_set =
    let elements = S.elements astate_set in
    let rec enum_nodup (tuplelist : T.t list)
        (current : (Procname.t * MyAccessPath.t * LocationSet.t) list) =
      match tuplelist with
      | [] ->
          current
      | (a, b, c, _) :: t ->
          if not (List.mem current (a, b, c) ~equal:triple_equal) then
            enum_nodup t ((a, b, c) :: current)
          else enum_nodup t current
    in
    enum_nodup elements []


  let partition_statetups_by_vardef (statetups : S.t) : S.t list =
    let vardefs =
      List.stable_dedup
      @@ S.fold
           (fun astate acc ->
             let vardef = second_of astate in
             vardef :: acc)
           statetups []
    in
    List.fold
      ~f:(fun acc vardef ->
        let matches =
          S.fold
            (fun statetup acc' ->
              if MyAccessPath.equal vardef (second_of statetup) then S.add statetup acc' else acc')
            statetups S.empty
        in
        matches :: acc)
      ~init:[] vardefs


  let join_those_tuples (dups : S.t) : S.t =
    (* is there an efficient way of doing this? *)
    let partitioned_tuples = partition_statetups_by_vardef dups in
    S.of_list
    @@ List.map
         ~f:(fun partition ->
           S.fold
             (fun (proc, vardef, loc1, aliasset1) (_, _, loc2, aliasset2) ->
               (proc, vardef, LocationSet.union loc1 loc2, A.union aliasset1 aliasset2))
             partition bottuple)
         partitioned_tuples


  (** S.diff의 커스텀 버전: (Procname.t * MyAccessPath.t * LocationSet.t) 이 같으면 제거 *)
  let my_diff (s1 : S.t) (s2 : S.t) : S.t =
    let triple_equal ((p1, v1, l1, _) : T.t) ((p2, v2, l2, _) : T.t) : bool =
      Procname.equal p1 p2 && MyAccessPath.equal v1 v2 && LocationSet.equal l1 l2
    in
    let s1_elements = S.elements s1 in
    let s2_elements = S.elements s2 in
    let s1_minus_s2_modulo_123 =
      List.fold
        ~f:(fun acc tup -> if List.mem s2_elements tup ~equal:triple_equal then acc else tup :: acc)
        ~init:[] s1_elements
    in
    S.of_list s1_minus_s2_modulo_123


  let join (lhs_pair: t) (rhs_pair: t) : t =
    let lhs, lhs_map = lhs_pair in
    let rhs, rhs_map = rhs_pair in
    let lhs_minus_rhs = S.diff lhs rhs in
    let rhs_minus_lhs = S.diff rhs lhs in
    let tuples_with_dup_keys = find_duplicate_keys lhs_minus_rhs rhs_minus_lhs in
    let there_are_duplicate_keys = not @@ S.is_empty tuples_with_dup_keys in
    if there_are_duplicate_keys then
      let joined_tuples = join_those_tuples tuples_with_dup_keys in
      let duplicate_keys_in_lhs_minus_rhs = S.inter tuples_with_dup_keys lhs_minus_rhs in
      let duplicate_keys_in_rhs_minus_lhs = S.inter tuples_with_dup_keys rhs_minus_lhs in
      let lhs_minus_duplicate_keys = S.diff lhs duplicate_keys_in_lhs_minus_rhs in
      let rhs_minus_duplicate_keys = S.diff rhs duplicate_keys_in_rhs_minus_lhs in
      let newset =
        S.union joined_tuples @@ S.union lhs_minus_duplicate_keys rhs_minus_duplicate_keys in
      let keys_and_loc =
        List.map
          ~f:(fun tup -> ((first_of tup, second_of tup), third_of tup))
          (S.elements joined_tuples) in
      let newmap =
        HistoryMap.batch_add_to_history2 keys_and_loc (HistoryMap.join lhs_map rhs_map) in
      (newset, newmap)
    else
      let newset = S.union lhs rhs in
      (newset, HistoryMap.join lhs_map rhs_map)


  let widen ~prev ~next ~num_iters:_ = join prev next
end

let pp = AbstractPair.pp

type t = AbstractPair.t

type summary = t (* used in Payloads.ml *)

let initial = (AbstractStateSetFinite.empty, HistoryMap.empty)

let placeholder_vardef (pid : Procname.t) : Var.t =
  let mangled = Mangled.from_string "ph" in
  let ph_vardef = Pvar.mk mangled pid in
  Var.of_pvar ph_vardef


let bottuple =
  ( Procname.empty_block
  , (placeholder_vardef Procname.empty_block, [])
  , LocationSet.empty
  , SetofAliases.empty )


(* Utility Functions *)
let first_of (a, _, _, _) = a

let second_of (_, b, _, _) = b

let third_of (_, _, c, _) = c

let fourth_of (_, _, _, d) = d

let ( >> ) f g x = g (f x)

let ( << ) f g x = f (g x)
