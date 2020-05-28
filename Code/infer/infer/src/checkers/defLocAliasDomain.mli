(** Domain for Interprocedural DFA. *)
open! IStd

module F = Format

(** astate_set = Set of (defined variable, location of definition, Aliased Variables including both logical and program variables) *)

(** An tuple (element of an astate_set) represents a single data definition *)

module Methname = Procname
module type Methname = module type of Procname

module MyAccessPath : sig
  type t = Var.t * AccessPath.access list [@@deriving compare]
  val pp: F.formatter -> t -> unit
  val equal: t -> t -> bool
end

(** AccessPath (with either Logical or Program Vars) Definitions. **)
module type MAtype = module type of MyAccessPath

(** set of locations (source-code level) where pieces of data are defined. **)
module LocationSet : module type of AbstractDomain.FiniteSet (Location)

module type LocSetType = module type of LocationSet

(** Set of AccessPath (with either Logical or Programs Vars) in an alias relationship. **)
module SetofAliases : AbstractDomain.FiniteSetS with type elt = Var.t * AccessPath.access list
module type SetofAliases = AbstractDomain.FiniteSetS with type elt = Var.t * AccessPath.access list

val doubleton : SetofAliases.elt -> SetofAliases.elt -> SetofAliases.t

(** The Quadruple of the above four. **)
module Quadruple (Domain1:Methname) (Domain2:MAtype) (Domain3:LocSetType) (Domain4:SetofAliases) : sig
  type t = Domain1.t * Domain2.t * Domain3.t * Domain4.t [@@deriving compare]
end

module QuadrupleWithPP : sig
  include module type of Quadruple (Methname) (MyAccessPath) (LocationSet) (SetofAliases)

  val pp : F.formatter -> t -> unit 
end

(** Pair of Procname.t and MyAccessPath.t *)
module ProcAccess : sig
  type t = Procname.t * MyAccessPath.t [@@deriving compare]

  val pp : F.formatter -> t -> unit
end

module HistoryMap : module type of AbstractDomain.WeakMap (ProcAccess) (LocationSet)

module AbstractState : sig
  type t = {tuple: QuadrupleWithPP.t; history: HistoryMap.t [@compare.ignore]} [@@deriving compare]

  val pp : F.formatter -> t -> unit
end

module AbstractStateSetFinite : AbstractDomain.FiniteSetS with type elt = AbstractState.t

module AbstractStateSet : sig
  include module type of AbstractStateSetFinite
end

val pp : F.formatter -> AbstractStateSet.t -> unit

type t = AbstractStateSet.t

type summary = t (* used in Payloads.ml *)

val initial : AbstractStateSet.t

val placeholder_vardef : Procname.t -> Var.t

val bottuple : QuadrupleWithPP.t

val botstate : AbstractState.t

(* Utility Functions *)

val first_of : 'a*'b*'c*'d -> 'a

val second_of : 'a*'b*'c*'d -> 'b

val third_of : 'a*'b*'c*'d -> 'c

val fourth_of : 'a*'b*'c*'d -> 'd

val ( >> ) : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c
