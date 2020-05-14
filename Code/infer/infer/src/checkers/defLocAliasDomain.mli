open! IStd

module F = Format

(** astate = Set of (defined variable, location of definition, Aliased Variables including both logical and program variables) *)

(** An tuple (element of an astate) represents a single data definition *)

module Methname = Procname
module type Methname = module type of Procname

(** The Set of Variable (either Logical or Program) Definitions. **)
module type Vartype = module type of Var

(** The Set of Locations where pieces of data are defined. **)
(* Should this be a source-code-level location or a Sil-level one? **)
module type Loctype = module type of Location

(** The Set of Set of (either Logical or Program) Variables in an alias relation. **)
module SetofAliases : AbstractDomain.FiniteSetS with type elt = Var.t * AccessPath.access list
module type SetofAliases = AbstractDomain.FiniteSetS with type elt = Var.t * AccessPath.access list

val doubleton : SetofAliases.elt -> SetofAliases.elt -> SetofAliases.t

(** The Quadruple of the above three. **)
module Quadruple (Domain1:Methname) (Domain2:Vartype) (Domain3:Loctype) (Domain4:SetofAliases) : sig
  type t = Domain1.t * Domain2.t * Domain3.t * Domain4.t [@@deriving compare]
end

(** An Abstract State is a set of triples of the above kind. **)

module QuadrupleWithPP : (sig
  include module type of Quadruple (Methname) (Var) (Location) (SetofAliases)
  val pp : F.formatter -> t -> unit 
end)

module AbstractStateFinite : AbstractDomain.FiniteSetS with type elt = QuadrupleWithPP.t

(** An Abstract State is a set of triples of the above kind. **)
module AbstractState : sig
  include module type of AbstractStateFinite
end

type t = AbstractState.t

type summary = t (* used in Payloads.ml *)

val initial : AbstractState.t

val pp : F.formatter -> AbstractState.t -> unit

val bottuple : QuadrupleWithPP.t

val first_of : 'a*'b*'c*'d -> 'a

val second_of : 'a*'b*'c*'d -> 'b

val third_of : 'a*'b*'c*'d -> 'c

val fourth_of : 'a*'b*'c*'d -> 'd

val ( >> ) : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c
