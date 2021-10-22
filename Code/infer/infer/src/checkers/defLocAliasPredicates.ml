open! IStd
open DefLocAliasDomain
open DefLocAliasPP
module L = Logging
module P = DefLocAliasDomain.AbstractPair
module S = DefLocAliasDomain.AbstractStateSetFinite
module A = DefLocAliasDomain.SetofAliases
module T = DefLocAliasDomain.AbstractState
module String = Core_kernel.String

exception TODO

exception IDontKnow

exception NotAJavaProcname of string

exception CannotGetPackage of string

exception CouldNotExtractCallee of string

exception WeakSearchTargetTupleByIdFailed of string

exception IsForeignAPFailed

exception ParseFailed

let search_target_tuple_by_id (id : Ident.t) (methname : Procname.t) (astate_set : S.t) : T.t =
  let elements = S.elements astate_set in
  let rec inner id (methname : Procname.t) elements =
    match elements with
    | [] ->
        L.die InternalError "search_target_tuple_by_id failed, id: %a, methname: %a, tupleset: %a@."
          Ident.pp id Procname.pp methname S.pp astate_set
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


let is_placeholder_vardef (var : Var.t) =
  match var with LogicalVar _ -> false | ProgramVar pv -> String.equal (Pvar.to_string pv) "ph"


let is_placeholder_vardef_ap (var_ap : MyAccessPath.t) =
  match fst var_ap with
  | LogicalVar _ ->
      false
  | ProgramVar pv ->
      String.equal (Pvar.to_string pv) "ph"


(** get the astate holding the given id in its aliasset, with preference to ph astates if there are
    many such ones *)
let weak_search_target_tuple_by_id (id : Ident.t) (astate_set : S.t) : T.t =
  let matches =
    S.fold
      (fun astate acc -> if A.mem (Var.of_id id, []) (fourth_of astate) then astate :: acc else acc)
      astate_set []
  in
  let ph_tuples =
    List.filter ~f:(fun astate -> is_placeholder_vardef_ap @@ second_of astate) matches
  in
  if not @@ List.is_empty ph_tuples then List.hd_exn ph_tuples
  else
    let else_matches =
      List.filter ~f:(fun astate -> not @@ List.mem ph_tuples astate ~equal:T.equal) matches
    in
    try List.hd_exn else_matches
    with _ ->
      F.kasprintf
        (fun msg -> raise @@ WeakSearchTargetTupleByIdFailed msg)
        "weak_search_target_tuple_by_id failed, id: %a, astate_set: %a@." Ident.pp id S.pp
        astate_set


(* There is an alias set which contains both id and pvar <-> id belongs to pvar, because ids never get reused *)
let is_mine (id : Ident.t) (pvar_ap : MyAccessPath.t) (astate_set : S.t) =
  try
    let aliasset = fourth_of @@ weak_search_target_tuple_by_id id astate_set in
    A.mem (Var.of_id id, []) aliasset && A.mem pvar_ap aliasset
  with _ -> false


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


let is_pvar_ap (ap : MyAccessPath.t) : bool =
  match fst ap with LogicalVar _ -> false | ProgramVar _ -> true


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
  let ap_string = F.asprintf "%a" MyAccessPath.pp ap in
  String.is_substring ap_string ~substring:"callv"


let is_param (var : Var.t) : bool =
  match var with
  | LogicalVar _ ->
      false
  | ProgramVar pv ->
      String.is_substring (Pvar.to_string pv) ~substring:"param"


let is_param_ap (ap : A.elt) : bool =
  let varstring = F.asprintf "%a" Var.pp (fst ap) in
  String.is_substring varstring ~substring:"param"


let maybe_static (ap : MyAccessPath.t) =
  let field_not_empty = not @@ List.is_empty @@ snd ap in
  let dot_in_base_string =
    let base_string = F.asprintf "%a" Var.pp (fst ap) in
    String.contains base_string '.'
  in
  field_not_empty && dot_in_base_string


let is_foreign_ap (ap : A.elt) (current_methname : Procname.t) : bool =
  let var = fst ap in
  match Var.get_declaring_function var with
  | None ->
      if maybe_static ap then
        let ap_string = F.asprintf "%a" MyAccessPath.pp ap in
        let current_classname_str =
          match Procname.get_class_name current_methname with
          | Some s ->
              s
          | None ->
              F.kasprintf
                (fun msg ->
                  L.progress "%s" msg ;
                  raise IsForeignAPFailed )
                "is_foreign_ap failed, ap: %a, current_methname: %a" MyAccessPath.pp ap Procname.pp
                current_methname
        in
        let target_classname_str = List.last_exn @@ String.split ~on:'.' ap_string in
        not @@ String.( = ) current_classname_str target_classname_str
      else
        F.kasprintf
          (fun msg ->
            L.progress "%s" msg ;
            raise IsForeignAPFailed )
          "is_foreign_ap failed, ap: %a, current_methname: %a" MyAccessPath.pp ap Procname.pp
          current_methname
  | Some declaring_proc ->
      not @@ Procname.equal current_methname declaring_proc


(** Pvar.is_frontend_tmp를 Var로 일반화하는 wrapping function *)
let is_frontend_tmp_var (var : Var.t) : bool =
  match var with LogicalVar _ -> false | ProgramVar pv -> Pvar.is_frontend_tmp pv


(** Pvar.is_frontend_tmp를 Var로 일반화하는 wrapping function *)
let is_frontend_tmp_var_ap (ap : MyAccessPath.t) : bool =
  match fst ap with LogicalVar _ -> false | ProgramVar pv -> Pvar.is_frontend_tmp pv


let is_irvar (var : Var.t) : bool =
  match var with
  | LogicalVar _ ->
      false
  | ProgramVar pv ->
      String.is_substring (Pvar.to_string pv) ~substring:"irvar"


let is_bcvar (var : Var.t) : bool =
  match var with
  | LogicalVar _ ->
      false
  | ProgramVar pv ->
      String.is_substring (Pvar.to_string pv) ~substring:"bcvar"


let is_irvar_ap (ap : A.elt) : bool =
  match fst ap with
  | LogicalVar _ ->
      false
  | ProgramVar pv ->
      String.is_substring (Pvar.to_string pv) ~substring:"irvar"


let is_bcvar_ap (ap : A.elt) : bool =
  match fst ap with
  | LogicalVar _ ->
      false
  | ProgramVar pv ->
      String.is_substring (Pvar.to_string pv) ~substring:"bcvar"


let is_initializer (procname : Procname.t) =
  let proc_string = Procname.to_string procname in
  String.is_substring proc_string ~substring:"<init>"


(* x => y: y is more recent than x in a same file *)
let ( => ) (x : LocationSet.t) (y : LocationSet.t) : bool =
  let x_min = LocationSet.min_elt x in
  let y_min = LocationSet.min_elt y in
  let loc_cond = x_min.line <= y_min.line in
  (* SourceFile.equal x_min.file y_min.file && *) loc_cond


(* x ==> y: y is STRICTLY more recent than x in a same file *)
let ( ==> ) (x : LocationSet.t) (y : LocationSet.t) : bool =
  let x_min = LocationSet.min_elt x in
  let y_min = LocationSet.min_elt y in
  let loc_cond = x_min.line < y_min.line in
  (* SourceFile.equal x_min.file y_min.file && *) loc_cond


let is_test_method (proc : Procname.t) : bool =
  let procname_str = Procname.to_string proc in
  String.is_substring procname_str ~substring:"Test"


let is_ternary_frontend_ap ((var, _) : MyAccessPath.t) : bool =
  if not @@ is_frontend_tmp_var var then false
  else
    match var with
    | LogicalVar _ ->
        false
    | ProgramVar pvar ->
        let var_string = Pvar.to_string pvar in
        Char.equal (String.get var_string 1) 'T'


let is_clinit (proc : Procname.t) : bool =
  String.is_substring (Procname.to_string proc) ~substring:"<clinit>"


let is_cast (proc : Procname.t) : bool =
  String.is_substring (Procname.to_string proc) ~substring:"__cast"


let extract_ident_from_callv (callv : MyAccessPath.t) : Ident.t =
  let varname = F.asprintf "%a" Var.pp (fst callv) in
  let splitted_on_colon = String.split varname ~on:':' in
  let splitted_on_underscore = String.split (List.hd_exn splitted_on_colon) ~on:'_' in
  let stamp =
    List.last_exn splitted_on_underscore |> (fun s -> String.slice s 2 0) |> int_of_string
  in
  Ident.create_normal Ident.Name.Normal stamp


let is_call_then_store_astate (astate : T.t) (id : Ident.t) : bool =
  let aliasset = fourth_of astate in
  let id_isin_aliasset = A.mem (Var.of_id id, []) aliasset in
  let there_is_callv_with_id =
    A.exists
      (fun ap ->
        is_callv_ap ap
        &&
        let extracted_id = extract_ident_from_callv ap in
        String.equal (Ident.to_string extracted_id) (Ident.to_string id) )
      aliasset
  in
  id_isin_aliasset && there_is_callv_with_id


let is_call_then_store (astate_list : T.t list) (id : Ident.t) : int =
  (* if all has callv with the given id:  *)
  if List.for_all astate_list ~f:(fun astate -> is_call_then_store_astate astate id) then 1
  else if List.exists astate_list ~f:(fun astate -> is_call_then_store_astate astate id) then 0
  else -1


let exp_is_const (exp : Exp.t) : bool = match exp with Const _ -> true | _ -> false

let exp_is_var (exp : Exp.t) : bool = match exp with Var _ -> true | _ -> false

let exp_is_lfield (exp : Exp.t) : bool = match exp with Lfield _ -> true | _ -> false

let exp_is_lindex (exp : Exp.t) : bool = match exp with Lindex _ -> true | _ -> false

let is_modeled (procname : Procname.t) =
  let java_procname =
    match procname with
    | Java java ->
        java
    | _ ->
        F.kasprintf
          (fun msg -> raise @@ NotAJavaProcname msg)
          "is_modeled failed, procname: %a@." Procname.pp procname
  in
  match Procname.Java.get_package java_procname with
  (* TODO: handle cases where getting package for UDFs fails *)
  | None ->
      F.kasprintf
        (fun msg -> raise @@ CannotGetPackage msg)
        "is_modeled failed, procname: %a@." Procname.pp procname
  | Some package_string ->
      let package_methname_tuple = (package_string, Procname.get_method procname) in
      let double_equal (package_string1, method_string1) (package_string2, method_string2) =
        String.equal package_string1 package_string2 && String.equal method_string1 method_string2
      in
      List.mem ~equal:double_equal DefLocAliasModels.methods package_methname_tuple


let is_call (instr : Sil.instr) = match instr with Call _ -> true | _ -> false

let locset_is_singleton (locset : LocationSet.t) = Int.( = ) (LocationSet.cardinal locset) 1

let is_lambda (proc : Procname.t) =
  let simple_string = Procname.get_method proc in
  String.is_substring ~substring:"lambda" simple_string
  || String.is_substring ~substring:"Lambda" simple_string


let is_new (procname : Procname.t) =
  let proc_string = Procname.to_string procname in
  String.is_substring proc_string ~substring:"__new"
  && (not @@ String.is_substring proc_string ~substring:"__new_array")


let is_object_init (procname : Procname.t) =
  let proc_string = Procname.to_string procname in
  String.is_substring proc_string ~substring:"Object.<init>"


let is_inner_class_init (procname : Procname.t) =
  let pattern = Str.regexp "[a-zA-Z]+\\$[a-zA-Z]+\\.<init>(.*)" in
  let proc_string = Procname.to_string procname in
  Str.string_match pattern proc_string 0


let is_inner_class_proc (procname : Procname.t) =
  let class_string =
    match Procname.get_class_name procname with Some class_string -> class_string | None -> ""
  in
  String.is_substring class_string ~substring:"$"


let is_frontend_procname (procname : Procname.t) =
  let simple_name = Procname.get_method procname in
  String.is_prefix simple_name ~prefix:"__"


let return_type_is_void (procname : Procname.t) =
  let proc_string = Procname.to_string procname in
  String.is_prefix proc_string ~prefix:"void"


let extract_counter_from_callv (callv_ap : A.elt) : int =
  if not @@ is_callv_ap callv_ap then
    F.kasprintf
      (fun msg ->
        L.progress "%s" msg ;
        raise ParseFailed )
      "extract_counter_from_returnv failed, callv_ap: %a@." MyAccessPath.pp callv_ap ;
  assert (is_callv_ap callv_ap) ;
  F.asprintf "%a" Var.pp (fst callv_ap)
  |> String.split ~on:':' |> List.hd_exn |> String.split ~on:'_'
  |> (fun stringlist -> List.nth_exn stringlist 1)
  |> int_of_string


let extract_counter_from_returnv (returnv : MyAccessPath.t) : int list =
  assert (is_returnv_ap returnv) ;
  let parse_intlist (string : string) : int list =
    try
      let ( >>| ) = List.( >>| ) in
      String.strip ~drop:(fun char -> Char.( = ) '[' char || Char.( = ) ']' char) string
      |> String.split ~on:' ' >>| String.strip
      |> List.filter ~f:(not << String.is_empty)
      >>| int_of_string
    with _ ->
      F.kasprintf
        (fun msg ->
          L.progress "%s" msg ;
          raise ParseFailed )
        "parse_intlist failed, string: %s@." string
  in
  F.asprintf "%a" Var.pp (fst returnv)
  |> String.split ~on:':' |> List.hd_exn |> String.split ~on:'_'
  |> (fun stringlist -> List.nth_exn stringlist 1)
  |> parse_intlist


let extract_linum_from_callv (callv : MyAccessPath.t) : int =
  assert (is_callv_ap callv) ;
  F.asprintf "%a" Var.pp (fst callv)
  |> String.split ~on:':' |> List.hd_exn |> String.split ~on:'_'
  |> (fun stringlist -> List.nth_exn stringlist 2)
  |> int_of_string


let extract_linum_from_returnv (returnv : MyAccessPath.t) : int =
  assert (is_returnv_ap returnv) ;
  F.asprintf "%a" Var.pp (fst returnv)
  |> String.split ~on:':' |> List.hd_exn |> String.split ~on:'_'
  |> (fun stringlist -> List.nth_exn stringlist 2)
  |> int_of_string


let callv_and_returnv_matches ~(callv : MyAccessPath.t) ~(returnv : MyAccessPath.t) =
  let callv_counter = extract_counter_from_callv callv
  and callv_linum = extract_linum_from_callv callv in
  let returnv_counters = extract_counter_from_returnv returnv
  and returnv_linum = extract_linum_from_returnv returnv in
  List.mem returnv_counters callv_counter ~equal:Int.( = ) && Int.( = ) returnv_linum callv_linum


(** Extract the callee's method name embedded in returnv, callv, or param. *)
let extract_callee_from (ap : MyAccessPath.t) =
  let special, _ = ap in
  match special with
  | LogicalVar _ ->
      F.kasprintf
        (fun msg -> raise @@ CouldNotExtractCallee msg)
        "extract_callee_from failed: it's a LogicalVar. ap: %a@." MyAccessPath.pp ap
  | ProgramVar pv -> (
    match Pvar.get_declaring_function pv with
    | Some procname ->
        procname
    | None ->
        F.kasprintf
          (fun msg -> raise @@ CouldNotExtractCallee msg)
          "extract_callee_from failed. ap: %a@." MyAccessPath.pp ap )


let is_local_to_known_procname (ap : MyAccessPath.t) =
  try
    let _ = extract_callee_from ap in
    true
  with CouldNotExtractCallee _ -> false
