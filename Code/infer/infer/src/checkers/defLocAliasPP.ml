open! IStd
open DefLocAliasDomain
module L = Logging
module F = Format
module P = DefLocAliasDomain.AbstractPair
module S = DefLocAliasDomain.AbstractStateSetFinite
module A = DefLocAliasDomain.SetofAliases
module T = DefLocAliasDomain.AbstractState

let pp_aliasset_list fmt (varsetlist : A.t list) =
  F.fprintf fmt "[" ;
  List.iter varsetlist ~f:(fun (aliasset : A.t) -> F.fprintf fmt "%a, " A.pp aliasset) ;
  F.fprintf fmt "]"


let pp_bindinglist fmt (bindinglist : (Var.t * Var.t) list) =
  F.fprintf fmt "[" ;
  List.iter bindinglist ~f:(fun (a, f) -> F.fprintf fmt "(%a, %a)" Var.pp a Var.pp f) ;
  F.fprintf fmt "]"


let pp_astatelist fmt (astatelist : T.t list) =
  F.fprintf fmt "[" ;
  List.iter astatelist ~f:(fun astate -> F.fprintf fmt "%a, " T.pp astate) ;
  F.fprintf fmt "]"


let pp_explist fmt (explist : Exp.t list) =
  F.fprintf fmt "[" ;
  List.iter explist ~f:(fun exp -> F.fprintf fmt "%a, " Exp.pp exp) ;
  F.fprintf fmt "]"


let pp_varlist fmt (varlist : Var.t list) =
  F.fprintf fmt "[" ;
  List.iter varlist ~f:(fun var -> F.fprintf fmt "%a, " Var.pp var) ;
  F.fprintf fmt "]"


let pp_pairofms fmt (proc, summ) =
  F.fprintf fmt "(" ;
  F.fprintf fmt "%a, %a" Procname.pp proc S.pp summ ;
  F.fprintf fmt ")"


let pp_pairofms_list fmt list =
  F.fprintf fmt "[" ;
  List.iter ~f:(fun x -> F.fprintf fmt "%a@." pp_pairofms x) list ;
  F.fprintf fmt "]"


let pp_ap_list fmt aplist =
  F.fprintf fmt "[" ;
  List.iter ~f:(fun ap -> F.fprintf fmt "%a, " MyAccessPath.pp ap) aplist ;
  F.fprintf fmt "]"


let pp_tuplelist fmt (lst : T.t list) =
  F.fprintf fmt "[" ;
  List.iter ~f:(fun tup -> F.fprintf fmt "%a, " T.pp tup) lst ;
  F.fprintf fmt "]"


let pp_tuplelistlist fmt (lstlst : T.t list list) =
  F.fprintf fmt "[" ;
  List.iter ~f:(fun lst -> pp_tuplelist fmt lst) lstlst ;
  F.fprintf fmt "]"
