open! IStd
module F = Format

(* Unnecessary Things Are in the Comments Below *)

(* module NotPPSet = struct
 *   include Ident.Set
 *   let pp fmt astate = 
 *     Out_channel.output_char stdout '{';
 *     Ident.Set.iter (fun x -> Ident.pp fmt x; print_string ", ") astate;
 *     Out_channel.output_char stdout '}'
 * end *)

(* module VarSet = NotPPSet *)


(* module VarSet = PrettyPrintable.MakePPSet (NotPPSet) *)


(* module FiniteBounds = struct
 *   include VarSet
 *   let join = VarSet.union
 *   let emptyset = VarSet.empty
 *   let add elem set = VarSet.add elem set
 *   let widen ~prev ~next ~num_iters = join prev next
 *   let leq ~lhs ~rhs = VarSet.subset lhs rhs
 *   (\** Set.subset s1 s2 tests whether the set s1 is a subset of the set s2. *\)
 * end
 * 
 * module TopLiftedDomain = struct
 *   include AbstractDomain.TopLifted (FiniteBounds)
 * 
 *   let add elem (set : t) : t =
 *       match set with
 *       | Top -> Top
 *       | NonTop s -> NonTop (VarSet.add elem s)
 * 
 *   let emptyset : t = NonTop (FiniteBounds.emptyset)
 * 
 *   let diff (s1:t) (s2:t) : t =
 *     match s1, s2 with
 *     | Top, Top -> emptyset (\* IDK :P *\)
 *     | Top, NonTop _ -> Top
 *     | NonTop _, Top -> emptyset
 *     | NonTop set1, NonTop set2 -> NonTop (VarSet.diff set1 set2)
 * end
 * 
 * type t = TopLiftedDomain.t
 * 
 * let pp fmt (astate : t) : unit =
 *   match astate with
 *   | Top -> F.fprintf fmt "T"
 *   | NonTop set -> NotPPSet.pp fmt set *)

module A = AbstractDomain.FiniteSet (struct
    include Pvar
    let pp fmt x = pp Pp.text fmt x
  end)

include A

type t = A.t

type summary = t (* used in Payloads.ml *)
