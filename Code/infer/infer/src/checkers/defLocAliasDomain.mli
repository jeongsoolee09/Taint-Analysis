(** Domain for Interprocedural DFA. *)
open! IStd

module F = Format

(** astate_set = Set of (defined variable, location of definition, Aliased Variables including both
    logical and program variables) *)

(** An tuple (element of an astate_set) represents a single data definition *)

module MyAccessPath : sig
  type t = Var.t * AccessPath.access list [@@deriving equal, compare]

  val pp : F.formatter -> t -> unit

  val equal : t -> t -> bool

  val to_string : t -> string
end

(* module LocationSet : AbstractDomain.FiniteSetS with type elt = Location.t *)

(** set of locations (source-code level) where pieces of data are defined. *)
module LocationSet : module type of AbstractDomain.FiniteSet (Location)

(** Set of AccessPath (with either Logical or Programs Vars) in an alias relationship. **)
module SetofAliases : module type of AbstractDomain.FiniteSet (MyAccessPath)

val doubleton : SetofAliases.elt -> SetofAliases.elt -> SetofAliases.t

(** The Quadruple of the above four. **)
module Quadruple
    (Domain1 : module type of Procname)
    (Domain2 : module type of MyAccessPath)
    (Domain3 : module type of LocationSet)
    (Domain4 : module type of SetofAliases) : sig
  type t = Domain1.t * Domain2.t * Domain3.t * Domain4.t [@@deriving equal, compare]
end

module QuadrupleWithPP : sig
  include module type of Quadruple (Procname) (MyAccessPath) (LocationSet) (SetofAliases)

  val pp : F.formatter -> t -> unit
end

(** Pair of Procname.t and MyAccessPath.t *)
module ProcAccess : sig
  type t = Procname.t * MyAccessPath.t [@@deriving compare]

  val pp : F.formatter -> t -> unit
end

module HistoryMap : sig
  include module type of AbstractDomain.WeakMap (ProcAccess) (LocationSet)

  val add_to_history : Procname.t * MyAccessPath.t -> LocationSet.t -> t -> t

  val batch_add_to_history : (Procname.t * MyAccessPath.t) list -> LocationSet.t -> t -> t

  val get_most_recent_loc : Procname.t * MyAccessPath.t -> t -> LocationSet.t
end

module AbstractState : module type of QuadrupleWithPP

module AbstractStateSetFinite : AbstractDomain.FiniteSetS with type elt = AbstractState.t

module AbstractPair : sig
  include module type of AbstractDomain.Pair (AbstractStateSetFinite) (HistoryMap)

  val leq : lhs:t -> rhs:t -> bool

  val join : t -> t -> t

  val widen : prev:t -> next:t -> num_iters:int -> t

  val pp : F.formatter -> t -> unit

  val double_equal : Procname.t * SetofAliases.elt -> Procname.t * SetofAliases.elt -> bool

  val partition_tuples_modulo_123 : AbstractStateSetFinite.t -> AbstractState.t list list
end

val pp : F.formatter -> AbstractPair.t -> unit

type t = AbstractPair.t

type summary = t (* used in Payloads.ml *)

val initial : AbstractPair.t

val placeholder_vardef : Procname.t -> Var.t

val bottuple : QuadrupleWithPP.t

(* Utility Functions *)

val first_of : 'a * 'b * 'c * 'd -> 'a

val second_of : 'a * 'b * 'c * 'd -> 'b

val third_of : 'a * 'b * 'c * 'd -> 'c

val fourth_of : 'a * 'b * 'c * 'd -> 'd

val ( >> ) : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c
