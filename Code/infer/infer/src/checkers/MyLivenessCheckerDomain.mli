open! IStd

(* include AbstractDomain.S (\* Is it necessary? *\) *)

(* module NotPPSet : sig
 *   include module type of Ident.Set
 *   val pp : Format.formatter -> t -> unit
 *   (\* let pp fmt astate = Out_channel.output_char stdout '{';
 *    *   Ident.Set.iter (fun x -> Ident.pp fmt x; print_string ", ") astate;
 *    *   Out_channel.output_char stdout '}' *\)
 * end *)

(* module type NotPPSet = sig
 *   type t = Ident.t
 *   val pp : Format.formatter -> t -> unit
 *   (\* let pp fmt astate = Out_channel.output_char stdout '{';
 *    *   Ident.Set.iter (fun x -> Ident.pp fmt x; print_string ", ") astate;
 *    *   Out_channel.output_char stdout '}' *\)
 * end *)

(* module VarSet = NotPPSet *)
module F = Format

(* module VarSet : NotPPSet *)

(* module FiniteBounds : sig
 *   include module type of VarSet
 * 
 *   (\* type t = VarSet.t *\)
 * 
 *   val join : t -> t -> t
 *   (\* let join = VarSet.union *\)
 * 
 *   val emptyset : t
 *   (\* let emptyset = VarSet.empty *\)
 * 
 *   val add : Ident.t -> t -> t
 *   (\* let add elem set = VarSet.add elem set *\)
 * 
 *   val widen : prev:t -> next:t -> num_iters:int -> t
 *   (\* let widen ~prev ~next ~num_iters = join prev next *\)
 * 
 *   val leq : lhs:t -> rhs:t -> bool
 *   (\* let leq ~lhs ~rhs = VarSet.subset lhs rhs *\)
 *   (\** Set.subset s1 s2 tests whether the set s1 is a subset of the set s2. *\)
 * end *)

(* module TopLiftedDomain : sig
 *   include module type of AbstractDomain.TopLifted (FiniteBounds)
 * 
 *   val pp : F.formatter -> t -> unit
 * 
 *   val add : Ident.t -> t -> t
 *   (\* let add elem (set : t) : t =
 *    *     match set with
 *    *     | Top -> Top
 *    *     | NonTop s -> NonTop (VarSet.add elem s) *\)
 * 
 *   val emptyset : t
 *   (\* let emptyset : t = NonTop (FiniteBounds.emptyset) *\)
 * 
 *   val diff : t -> t -> t
 *   (\* let diff (s1:t) (s2:t) : t =
 *    *   match s1, s2 with
 *    *   | Top, Top -> emptyset (\\* IDK :P *\\)
 *    *   | Top, NonTop _ -> Top
 *    *   | NonTop _, Top -> emptyset
 *    *   | NonTop set1, NonTop set2 -> NonTop (VarSet.diff set1 set2) *\)
 * end *)

(* module A = AbstractDomain.FiniteSet (struct
 *     include module type of Pvar
 *     let pp fmt x = pp Pp.text fmt x
 *   end) *)

module A : AbstractDomain.FiniteSetS with type elt = Pvar.t

include module type of A

(* type t = A.t *)

type summary = t

