open! IStd
open DefLocAliasDomain
module L = Logging
module P = DefLocAliasDomain.AbstractPair
module S = DefLocAliasDomain.AbstractStateSetFinite
module A = DefLocAliasDomain.SetofAliases
module T = DefLocAliasDomain.AbstractState
module String = Core_kernel.String

exception NotImplemented

exception IDontKnow

let weak_search_target_tuple_by_id (id : Ident.t) (astate_set : S.t) : T.t =
  let elements = S.elements astate_set in
  let rec inner id (elements : S.elt list) =
    match elements with
    | [] ->
        L.die InternalError "weak_search_target_tuple_by_id failed, id: %a, astate_set: %a@."
          Ident.pp id S.pp astate_set
    | target :: t ->
        let aliasset = fourth_of target in
        if A.mem (Var.of_id id, []) aliasset then target else inner id t
  in
  inner id elements


let search_target_tuple_by_id (id : Ident.t) (methname : Procname.t) (astate_set : S.t) : T.t =
  let elements = S.elements astate_set in
  let rec inner id (methname : Procname.t) elements =
    match elements with
    | [] ->
        raise IDontKnow
    | ((procname, _, _, aliasset) as target) :: t ->
        if Procname.equal procname methname && A.mem (Var.of_id id, []) aliasset then target
        else inner id methname t
  in
  inner id methname elements


let is_program_var_expr (exp : Exp.t) : bool = match exp with Lvar _ -> true | _ -> false

let is_logical_var_expr (exp : Exp.t) : bool = match exp with Var _ -> true | _ -> false

let is_logical_var (var : Var.t) : bool =
  match var with LogicalVar _ -> true | ProgramVar _ -> false


let is_program_var (var : Var.t) : bool =
  match var with LogicalVar _ -> false | ProgramVar _ -> true


let is_program_var_ap (ap : A.elt) : bool =
  let var, _ = ap in
  match var with LogicalVar _ -> false | ProgramVar _ -> true


let convert_from_mangled : Procname.t -> Mangled.t * Typ.t -> Var.t =
 fun methname (m, _) -> Pvar.mk m methname |> Var.of_pvar


let get_my_formal_args (methname : Procname.t) =
  match Procdesc.load methname with
  | Some pdesc ->
      (*L.progress "found procdesc for %a\n" Procname.pp methname;*)
      List.map ~f:(convert_from_mangled methname) (Procdesc.get_formals pdesc)
  | None ->
      L.die InternalError "get_my_formal_args failed, methname: %a@." Procname.pp methname


(* There is an alias set which contains both id and pvar <-> id belongs to pvar, because ids never get reused *)
let is_mine id pvar methname (apair : P.t) =
  try
    let _, _, _, aliasset = search_target_tuple_by_id id methname (fst apair) in
    A.mem (Var.of_id id, []) aliasset && A.mem (Var.of_pvar pvar, []) aliasset
  with _ -> false


let is_placeholder_vardef (var : Var.t) =
  match var with LogicalVar _ -> false | ProgramVar pv -> String.equal (Pvar.to_string pv) "ph"


let is_placeholder_vardef_ap (var_ap : MyAccessPath.t) =
  match fst var_ap with
  | LogicalVar _ ->
      false
  | ProgramVar pv ->
      String.equal (Pvar.to_string pv) "ph"


let is_formal (rhs : Pvar.t) (current_meth : Procname.t) : bool =
  let formallist = get_my_formal_args current_meth in
  let rhs_var = Var.of_pvar rhs in
  List.mem formallist rhs_var ~equal:Var.equal


let is_this_ap (ap : A.elt) =
  let var, _ = ap in
  Var.is_this var


let input_is_void_type (arg_ts : (Exp.t * Typ.t) list) (astate_set : S.t) : bool =
  match arg_ts with
  | [] ->
      false
  | [(Var var, _)] -> (
    try
      let _, (vardef, _), _, _ = weak_search_target_tuple_by_id var astate_set in
      if Var.is_this vardef then true else false
    with _ -> (* it's a constructor or something abnormal: We give up soundness *)
              true )
  | (Var _, _) :: _ ->
      false
  | (Lvar _, _) :: _ ->
      L.die InternalError "input_is_void_type failed, astate_set: %a@." S.pp astate_set
      (* shouldn't all non-constant actual args be pure logical vars? *)
  | (_, _) :: _ ->
      false


let is_returnv (var : Var.t) : bool =
  match var with
  | LogicalVar _ ->
      false
  | ProgramVar pv ->
      String.is_substring (Pvar.to_string pv) ~substring:"returnv"


let is_returnv_ap (ap : A.elt) : bool =
  let var, _ = ap in
  match var with
  | LogicalVar _ ->
      false
  | ProgramVar pv ->
      String.is_substring (Pvar.to_string pv) ~substring:"returnv"


let is_return_ap (ap : A.elt) : bool =
  let var, _ = ap in
  Var.is_return var


let is_callv (var : Var.t) : bool =
  match var with
  | LogicalVar _ ->
      false
  | ProgramVar pv ->
      String.is_substring (Pvar.to_string pv) ~substring:"callv"


let is_callv_ap (ap : A.elt) : bool =
  let var, _ = ap in
  match var with
  | LogicalVar _ ->
      false
  | ProgramVar pv ->
      String.is_substring (Pvar.to_string pv) ~substring:"callv"


let is_param (var : Var.t) : bool =
  match var with
  | LogicalVar _ ->
      false
  | ProgramVar pv ->
      String.is_substring (Pvar.to_string pv) ~substring:"param"


let is_param_ap (ap : A.elt) : bool =
  let var, _ = ap in
  match var with
  | LogicalVar _ ->
      false
  | ProgramVar pv ->
      String.is_substring (Pvar.to_string pv) ~substring:"param"


let is_foreign_ap (ap : A.elt) (current_methname : Procname.t) : bool =
  let var = fst ap in
  match Var.get_declaring_function var with
  | None ->
      L.die InternalError "is_foreign_ap failed, ap: %a, current_methname: %a" MyAccessPath.pp ap
        Procname.pp current_methname
  | Some declaring_proc ->
      not @@ Procname.equal current_methname declaring_proc


(** Pvar.is_frontend_tmp를 Var로 일반화하는 wrapping function *)
let is_frontend_tmp_var (var : Var.t) : bool =
  match var with LogicalVar _ -> false | ProgramVar pv -> Pvar.is_frontend_tmp pv


(** Pvar.is_frontend_tmp를 Var로 일반화하는 wrapping function *)
let is_frontend_tmp_var_ap (ap : MyAccessPath.t) : bool =
  match fst ap with LogicalVar _ -> false | ProgramVar pv -> Pvar.is_frontend_tmp pv


let is_irvar_ap (ap : A.elt) : bool =
  match fst ap with
  | LogicalVar _ ->
      false
  | ProgramVar pv ->
      String.is_substring (Pvar.to_string pv) ~substring:"irvar"


let is_initializer (procname : Procname.t) =
  let proc_string = Procname.to_string procname in
  String.is_substring proc_string ~substring:"<init>"
