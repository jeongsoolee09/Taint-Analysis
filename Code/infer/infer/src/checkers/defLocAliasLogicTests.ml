open! IStd
open DefLocAliasSearches

module L = Logging
module A = DefLocAliasDomain.SetofAliases
module S = DefLocAliasDomain.AbstractState

exception NotLogicalArg
exception NoSummary


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
  | Some pdesc -> L.progress "found procdesc for %a\n" Procname.pp methname; List.map ~f:(convert_from_mangled methname) (Procdesc.get_formals pdesc)
  | None -> raise NoSummary 


(* There is an alias set which contains both id and pvar <-> id belongs to pvar, because ids never get reused *)
let is_mine id pvar methname astate =
  try
    let (_, _, _, aliasset) = search_target_tuple_by_id id methname astate in
    A.mem (Var.of_id id) aliasset && A.mem (Var.of_pvar pvar) aliasset
  with _ ->
    false


let is_placeholder_vardef (var:Var.t) =
  match var with
  | LogicalVar _ -> false
  | ProgramVar pv -> String.equal (Pvar.to_string pv) "ph"


let is_formal (rhs:Pvar.t) (current_meth:Procname.t) : bool =
  let formallist = get_my_formal_args current_meth in
  let rhs_var = Var.of_pvar rhs in
  List.mem formallist rhs_var ~equal:Var.equal


let input_is_void_type (arg_ts:(Exp.t*Typ.t) list) (astate:S.t) : bool =
  match arg_ts with
  | [] -> false
  | (Var var, _)::[] ->
      begin try
        let (_, vardef, _, _) =
              weak_search_target_tuple_by_id var astate
        in
        if Var.is_this vardef then true else false
        with _ -> (* it's a constructor or something abnormal: We give up soundness *)
            true end
  | (Var _, _)::_ -> false
  | (Lvar _, _)::_ -> raise NotLogicalArg (* shouldn't all non-constant actual args be pure logical vars? *)
  | (_, _)::_ -> false

