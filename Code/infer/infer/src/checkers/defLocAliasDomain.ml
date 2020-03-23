(** Interprocedural Liveness Checker. *)

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
module SetofAliases = AbstractDomain.FiniteSet (struct
    include Var
    let pp fmt x = Var.pp fmt x
end)

let doubleton (a:SetofAliases.elt) (b:SetofAliases.elt) : SetofAliases.t =
  let aset = SetofAliases.singleton a in
  let bset = SetofAliases.singleton b in
  SetofAliases.union aset bset

module type SetofAliases = AbstractDomain.FiniteSetS with type elt = Var.t

(** The Quadruple of the above three. **)
module Quadruple (Domain1:Methname) (Domain2:Vartype) (Domain3:Loctype) (Domain4:SetofAliases) = struct
  type t = Domain1.t * Domain2.t * Domain3.t * Domain4.t [@@deriving compare]
end

module QuadrupleWithPP = (struct
  include Quadruple (Methname) (Var) (Location) (SetofAliases)

  let pp : F.formatter -> t -> unit = fun fmt (methname, vardefs, defloc, aliasset) ->
    F.fprintf fmt "(%a, %a, %a, %a)" Methname.pp methname Var.pp vardefs
      Location.pp defloc SetofAliases.pp aliasset
  
end)

(** An Abstract State is a set of quadruples of the above kind. *)
module AbstractStateFinite = AbstractDomain.FiniteSet (QuadrupleWithPP)

(*FiniteSet or TopLifted?*)
module AbstractState = struct
  include AbstractStateFinite
end

let pp = AbstractState.pp

type t = AbstractState.t

type summary = t (* used in Payloads.ml *)

let initial = AbstractState.empty

let placeholder_vardef (pid:Procname.t) : Var.t =
  let mangled = Mangled.from_string "ph" in
  let ph_vardef = Pvar.mk mangled pid in
  Var.of_pvar ph_vardef

let bottuple = (Procname.empty_block, placeholder_vardef (Procname.empty_block), Location.dummy, SetofAliases.empty)
