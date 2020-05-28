open! IStd
open DefLocAliasSearches
open DefLocAliasDomain

module L = Logging
module A = DefLocAliasDomain.SetofAliases
module S = DefLocAliasDomain.AbstractStateSet

exception NotImplemented
exception IDontKnow

let is_pvar_expr (exp:Exp.t) : bool =
  match exp with
  | Lvar _ -> true
  | _ -> false


let is_logical_var_expr (exp:Exp.t) : bool =
  match exp with
  | Var _ -> true
  | _ -> false


let is_logical_var (var:Var.t) : bool =
  match var with
  | LogicalVar _ -> true
  | ProgramVar _ -> false


let is_program_var (var:Var.t) : bool =
  match var with
  | LogicalVar _ -> false
  | ProgramVar _ -> true


let convert_from_mangled : Procname.t -> (Mangled.t*Typ.t) -> Var.t = fun methname (m,_) -> Pvar.mk m methname |> Var.of_pvar


let get_my_formal_args (methname:Procname.t) = 
  match Procdesc.load methname with
  | Some pdesc -> (*L.progress "found procdesc for %a\n" Procname.pp methname;*) List.map ~f:(convert_from_mangled methname) (Procdesc.get_formals pdesc)
  | None -> L.die InternalError "get_my_formal_args failed, methname: %a@." Procname.pp methname


(* There is an alias set which contains both id and pvar <-> id belongs to pvar, because ids never get reused *)
let is_mine id pvar methname astate_set =
  try
    let (_, _, _, aliasset) = search_target_tuple_by_id id methname astate_set in
    A.mem (Var.of_id id, []) aliasset && A.mem (Var.of_pvar pvar, []) aliasset
  with _ ->
    false


let is_placeholder_vardef (var:Var.t) =
  match var with
  | LogicalVar _ -> false
  | ProgramVar pv -> String.equal (Pvar.to_string pv) "ph"


let is_placeholder_vardef_ap (var_ap:MyAccessPath.t) =
  match fst var_ap with
  | LogicalVar _ -> false
  | ProgramVar pv -> String.equal (Pvar.to_string pv) "ph"


let is_formal (rhs:Pvar.t) (current_meth:Procname.t) : bool =
  let formallist = get_my_formal_args current_meth in
  let rhs_var = Var.of_pvar rhs in
  List.mem formallist rhs_var ~equal:Var.equal


let is_this_ap (ap:A.elt) =
  let var, _ = ap in
  Var.is_this var


let input_is_void_type (arg_ts:(Exp.t*Typ.t) list) (astate_set:S.t) : bool =
  match arg_ts with
  | [] -> false
  | (Var var, _)::[] ->
      begin try
          let (_, (vardef, _), _, _) = weak_search_target_tuple_by_id var astate_set in
        if Var.is_this vardef then true else false
      with _ -> (* it's a constructor or something abnormal: We give up soundness *)
            true end
  | (Var _, _)::_ -> false
  | (Lvar _, _)::_ -> L.die InternalError "input_is_void_type failed, astate_set: %a@." S.pp astate_set (* shouldn't all non-constant actual args be pure logical vars? *)
  | (_, _)::_ -> false


let is_returnv (var:Var.t) : bool =
  match var with
  | LogicalVar _ -> false
  | ProgramVar pv -> String.equal (Pvar.to_string pv) "returnv"


let is_returnv_ap (ap:A.elt) : bool =
  let var, _ = ap in
  match var with
  | LogicalVar _ -> false
  | ProgramVar pv -> String.equal (Pvar.to_string pv) "returnv"
