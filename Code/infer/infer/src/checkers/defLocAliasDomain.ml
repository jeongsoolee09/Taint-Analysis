(** Domain for Interprocedural DFA. *)
open! IStd

module F = Format

(** astate_set = Set of (defined variable, location of definition, Aliased Variables including both logical and program variables) *)

(** An tuple (element of an astate_set) represents a single data definition *)

module Methname = Procname
module type Methname = module type of Procname

module MyAccessPath = struct
  type t = Var.t * AccessPath.access list [@@deriving compare]

  let pp fmt (x:t) =
    let var, list = x in
      F.fprintf fmt "(%a, [" Var.pp var;
      List.iter list ~f:(fun access -> F.fprintf fmt "%a, " AccessPath.pp_access access);
      F.fprintf fmt "])"

  let equal (x:t) (y:t) =
    let xvar, xlist = x in
    let yvar, ylist = y in
    Var.equal xvar yvar && List.equal AccessPath.equal_access xlist ylist
end

(** AccessPath (with either Logical or Program Vars) Definitions. *)
module type MAtype = module type of MyAccessPath

(** set of locations (source-code level) where pieces of data are defined. *)
module LocationSet = AbstractDomain.FiniteSet (Location)

module type LocSetType = module type of LocationSet

(** Set of AccessPath (with either Logical or Programs Vars) in an alias relationship. *)
module SetofAliases = AbstractDomain.FiniteSet (MyAccessPath)
module type SetofAliases = AbstractDomain.FiniteSetS with type elt = Var.t * AccessPath.access list

let doubleton (a:SetofAliases.elt) (b:SetofAliases.elt) : SetofAliases.t =
  let aset = SetofAliases.singleton a in
  let bset = SetofAliases.singleton b in
  SetofAliases.union aset bset

(** The Quadruple of the above four. *)
module Quadruple (Domain1:Methname) (Domain2:MAtype) (Domain3:LocSetType) (Domain4:SetofAliases) = struct
  type t = Domain1.t * Domain2.t * Domain3.t * Domain4.t [@@deriving compare]
end

module QuadrupleWithPP = struct
  include Quadruple (Methname) (MyAccessPath) (LocationSet) (SetofAliases)

  let pp : F.formatter -> t -> unit = fun fmt (methname, vardefs, defloc, aliasset) ->
    F.fprintf fmt "(%a, %a, %a, %a)" Methname.pp methname MyAccessPath.pp vardefs LocationSet.pp defloc SetofAliases.pp aliasset
end

(** Pair of Procname.t and MyAccessPath.t *)
module ProcAccess = struct
  type t = Procname.t * MyAccessPath.t [@@deriving compare]

  let pp fmt (proc, ap) = F.fprintf fmt "(%a, %a)" Procname.pp proc MyAccessPath.pp ap
end

(** A map from ProcAccess.t to LocationSet.t. *)
module HistoryMap = AbstractDomain.WeakMap (ProcAccess) (LocationSet)

(* An Abtract State is just a quadruple. *)
module AbstractState = QuadrupleWithPP

(** A set of Abstract States. *)
module AbstractStateSetFinite = AbstractDomain.FiniteSet (AbstractState)

module type AbstractStateSetFinite = module type of AbstractStateSetFinite

module type HistoryMap = module type of HistoryMap

(* The pair of 1) set of abstract states and 2) the history map *)
module AbstractPair = struct
  include AbstractDomain.Pair(AbstractStateSetFinite) (HistoryMap)

  let pp fmt (a, b) = F.fprintf fmt "(%a, %a)" AbstractStateSetFinite.pp a HistoryMap.pp b

  module S = AbstractStateSetFinite
  module T = AbstractState
  module A = SetofAliases

  let placeholder_vardef (pid:Procname.t) : Var.t =
    let mangled = Mangled.from_string "ph" in
    let ph_vardef = Pvar.mk mangled pid in
    Var.of_pvar ph_vardef

  let bottuple = (Procname.empty_block, (placeholder_vardef (Procname.empty_block), []), LocationSet.empty, SetofAliases.empty)

  let leq ~lhs:(a, _) ~rhs:(b, _) = S.subset a b

  (* Utility Functions *)
  let first_of (a,_,_,_) = a

  let second_of (_,b,_,_) = b

  let third_of (_,_,c,_) = c

  let fourth_of (_,_,_,d) = d

  let double_equal (tup1:T.t) (tup2:T.t) =
    Procname.equal (first_of tup1) (first_of tup2) &&
    MyAccessPath.equal (second_of tup1) (second_of tup2)

  (** finds state tuples with same methname and AP in s1 and s2 *)
  let find_duplicate_keys (s1:S.t) (s2:S.t) =
    let s1_elements = S.elements s1 in
    let s2_elements = S.elements s2 in
    let list_intersection_modulo_firstsecond l1 l2 =
      let l1_elems_in_l2 = S.of_list @@ List.fold ~f:(fun acc elem -> if List.mem l2 elem ~equal:double_equal then elem::acc else acc) ~init:[] l1 in
      let l2_elems_in_l1 = S.of_list @@ List.fold ~f:(fun acc elem -> if List.mem l1 elem ~equal:double_equal then elem::acc else acc) ~init:[] l2 in
      S.union l1_elems_in_l2 l2_elems_in_l1 in
    list_intersection_modulo_firstsecond s1_elements s2_elements

  let double_equal = fun (proc1, ap1) (proc2, ap2) -> Procname.equal proc1 proc2 && MyAccessPath.equal ap1 ap2

  (** astate로부터 (procname, vardef, location) 쌍을 중복 없이 만든다. *)
  let get_keys astate_set =
    let elements = S.elements astate_set in
    let rec enum_nodup (tuplelist:T.t list) (current:(Procname.t*MyAccessPath.t) list) =
      match tuplelist with
      | [] -> current
      | (a,b,_,_)::t ->
        if not (List.mem current (a,b) ~equal:double_equal)
          then enum_nodup t ((a,b)::current)
          else enum_nodup t current in
    enum_nodup elements []

  (** 실행이 끝난 astate_set에서 중복된 튜플들 (proc, vardef, loc가 같음)끼리 묶여 있는 list of list를 만든다. *)
  let partition_tuples_modulo_123 (astate_set:S.t) : T.t list list = 
    let keys = get_keys astate_set in
    let rec get_tuple_by_key tuplelist key =
      match tuplelist with
      | [] -> []
      | (proc, name, _, _) as targetTuple::t ->
          if double_equal key (proc, name)
          then ((*L.progress "generating key: %a, targetTuple: %a\n" Var.pp name QuadrupleWithPP.pp targetTuple;*) targetTuple::get_tuple_by_key t key) 
          else get_tuple_by_key t key in
    let get_tuples_by_keys tuplelist keys = List.map ~f:(get_tuple_by_key tuplelist) keys in
    let elements = S.elements astate_set in
    get_tuples_by_keys elements keys

  let rec reduce_partitioned_tuples (lstlst:T.t list list) : T.t list =
    match lstlst with
    | [] -> []
    | lst::t ->
        let reduced_tuple =  List.fold_left ~f:(fun (_, _, loc1, aliasset1) (proc, vardef, loc2, aliasset2) -> (proc, vardef, LocationSet.union loc1 loc2, A.union aliasset1 aliasset2)) ~init:bottuple lst in
        reduced_tuple::(reduce_partitioned_tuples t)

  let join_those_tuples (dups:S.t) : S.t =
    (* is there an efficient way of doing this? *)
    let partitioned_tuples = partition_tuples_modulo_123 dups in
    S.of_list @@ reduce_partitioned_tuples partitioned_tuples

  let join (lhs_pair:t) (rhs_pair:t) : t =
    let lhs, lhs_map = lhs_pair in
    let rhs, rhs_map = rhs_pair in
    let lhs_minus_rhs = S.diff lhs rhs in
    let rhs_minus_lhs = S.diff rhs lhs in
    let tuples_with_dup_keys = find_duplicate_keys lhs_minus_rhs rhs_minus_lhs in
    let there_are_duplicate_keys = not @@ S.is_empty tuples_with_dup_keys in
    if there_are_duplicate_keys
    then
      let joined_tuples = join_those_tuples tuples_with_dup_keys in
      let duplicate_keys_in_lhs_minus_rhs = S.inter tuples_with_dup_keys lhs_minus_rhs in
      let duplicate_keys_in_rhs_minus_lhs = S.inter tuples_with_dup_keys rhs_minus_lhs in
      let lhs_minus_duplicate_keys = S.diff lhs duplicate_keys_in_lhs_minus_rhs in
      let rhs_minus_duplicate_keys = S.diff rhs duplicate_keys_in_rhs_minus_lhs in
      let newset = S.union joined_tuples @@ S.union lhs_minus_duplicate_keys rhs_minus_duplicate_keys in
      (newset, HistoryMap.join lhs_map rhs_map)
    else 
      let newset = S.union lhs rhs in
      (newset, HistoryMap.join lhs_map rhs_map)

  let widen ~prev:prev ~next:next ~num_iters:_ = join prev next
end

let pp = AbstractPair.pp

type t = AbstractPair.t

type summary = t (* used in Payloads.ml *)

let initial = (AbstractStateSetFinite.empty, HistoryMap.empty)

let placeholder_vardef (pid:Procname.t) : Var.t =
  let mangled = Mangled.from_string "ph" in
  let ph_vardef = Pvar.mk mangled pid in
  Var.of_pvar ph_vardef

let bottuple = (Procname.empty_block, (placeholder_vardef (Procname.empty_block), []), LocationSet.empty, SetofAliases.empty)


(* Utility Functions *)
let first_of (a,_,_,_) = a

let second_of (_,b,_,_) = b

let third_of (_,_,c,_) = c

let fourth_of (_,_,_,d) = d

let ( >> ) f g = fun x -> g (f x)