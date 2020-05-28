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

(* An Abtract State is a record comprising a quadruple and a history map. *)
module AbstractState = struct
  type t = {tuple: QuadrupleWithPP.t; history: HistoryMap.t [@compare.ignore]} [@@deriving compare]

  let pp fmt {tuple; history} =
    F.fprintf fmt "{";
    F.fprintf fmt "%a" QuadrupleWithPP.pp tuple;
    F.fprintf fmt "; ";
    F.fprintf fmt "%a" HistoryMap.pp history;
    F.fprintf fmt "}"
end

(** A set of Abstract States. *)
module AbstractStateSetFinite = AbstractDomain.FiniteSet (AbstractState)

(* FiniteSet or TopLifted? *)
module AbstractStateSet = struct
  include AbstractStateSetFinite
end

let pp = AbstractStateSet.pp

type t = AbstractStateSet.t

type summary = t (* used in Payloads.ml *)

let initial = AbstractStateSet.empty

let placeholder_vardef (pid:Procname.t) : Var.t =
  let mangled = Mangled.from_string "ph" in
  let ph_vardef = Pvar.mk mangled pid in
  Var.of_pvar ph_vardef

let bottuple = (Procname.empty_block, (placeholder_vardef (Procname.empty_block), []), LocationSet.singleton Location.dummy, SetofAliases.empty)

let botstate = {AbstractState.tuple=bottuple; history=HistoryMap.empty}

(* Utility Functions *)
let first_of (a,_,_,_) = a

let second_of (_,b,_,_) = b

let third_of (_,_,c,_) = c

let fourth_of (_,_,_,d) = d

let ( >> ) f g = fun x -> g (f x)
