open! IStd
open DefLocAliasDomain
module L = Logging
module F = Format
module P = DefLocAliasDomain.AbstractPair
module S = DefLocAliasDomain.AbstractStateSetFinite
module A = DefLocAliasDomain.SetofAliases
module T = DefLocAliasDomain.AbstractState

exception GetDeclaringFunctionFailed

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


let pp_idlist fmt (idlist : Ident.t list) =
  F.fprintf fmt "[" ;
  List.iter idlist ~f:(fun id -> F.fprintf fmt "%a, " Ident.pp id) ;
  F.fprintf fmt "]"


let pp_pvarlist fmt (pvarlist : Pvar.t list) =
  F.fprintf fmt "[" ;
  List.iter pvarlist ~f:(fun pvar -> F.fprintf fmt "%a, " (Pvar.pp Pp.text) pvar) ;
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


let pp_aplist_list fmt aplistlist =
  F.fprintf fmt "[" ;
  List.iter ~f:(fun aplist -> F.fprintf fmt "%a, " pp_ap_list aplist) aplistlist ;
  F.fprintf fmt "]"


let pp_proc_list fmt proclist =
  F.fprintf fmt "[" ;
  List.iter ~f:(fun proc -> F.fprintf fmt "%a, " Procname.pp proc) proclist ;
  F.fprintf fmt "]"


let pp_tuplelist fmt (lst : T.t list) =
  F.fprintf fmt "[" ;
  List.iter ~f:(fun tup -> F.fprintf fmt "%a, " T.pp tup) lst ;
  F.fprintf fmt "]"


let pp_tuplelistlist fmt (lstlst : T.t list list) =
  F.fprintf fmt "[" ;
  List.iter ~f:(fun lst -> pp_tuplelist fmt lst) lstlst ;
  F.fprintf fmt "]"


let pp_tuplesetlist fmt (lst : S.t list) =
  F.fprintf fmt "[" ;
  List.iter ~f:(fun tupset -> F.fprintf fmt "%a, " S.pp tupset) lst ;
  F.fprintf fmt "]"


let pp_locationsetlist fmt (lst : LocationSet.t list) =
  F.fprintf fmt "[" ;
  List.iter ~f:(fun locset -> F.fprintf fmt "%a, " LocationSet.pp locset) lst ;
  F.fprintf fmt "]"


let get_declaring_function_ap_exn (ap : A.elt) : Procname.t =
  let var, _ = ap in
  match var with
  | LogicalVar _ ->
      F.kasprintf
        (fun msg ->
          L.progress "%s" msg ;
          raise GetDeclaringFunctionFailed )
        "get_declaring_function_ap_exn failed: %a@." MyAccessPath.pp ap
  | ProgramVar pvar -> (
    match Pvar.get_declaring_function pvar with
    | None ->
        F.kasprintf
          (fun msg ->
            L.progress "%s" msg ;
            raise GetDeclaringFunctionFailed )
          "get_declaring_function_ap_exn failed: %a@." MyAccessPath.pp ap
    | Some procname ->
        procname )


let pp_aliasset_with_procname fmt (aliasset : A.t) =
  F.fprintf fmt "[" ;
  A.iter
    (fun ap ->
      F.fprintf fmt "%a from %a, " MyAccessPath.pp ap Procname.pp
      @@ get_declaring_function_ap_exn ap )
    aliasset ;
  F.fprintf fmt "]"


let pp_instr_list fmt (instrlist : Sil.instr list) =
  F.fprintf fmt "[" ;
  List.iter
    ~f:(fun instr -> F.fprintf fmt "%a; " (Sil.pp_instr Pp.text ~print_types:false) instr)
    instrlist ;
  F.fprintf fmt "]"
