open! IStd
open DefLocAliasDomain

module L = Logging
module F = Format
module P = DefLocAliasDomain.AbstractPair
module S = DefLocAliasDomain.AbstractStateSetFinite
module A = DefLocAliasDomain.SetofAliases
module T = DefLocAliasDomain.AbstractState

exception NotImplemented
exception IDontKnow

let placeholder_vardef (pid:Procname.t) : Var.t =
  let mangled = Mangled.from_string "ph" in
  let ph_vardef = Pvar.mk mangled pid in
  Var.of_pvar ph_vardef


let search_target_tuple_by_pvar (pvar:Var.t) (methname:Procname.t) (astate_set:S.t) =
  let elements = S.elements astate_set in
  let rec search_target_tuple_by_pvar_inner pvar (methname:Procname.t) elements = 
    match elements with
    | [] -> L.die InternalError "search_target_tuple_by_pvar failed, pvar: %a, methname:%a, astate_set:%a@." Var.pp pvar Procname.pp methname S.pp astate_set
    | ((procname, _, _, aliasset) as target)::t ->
        if Procname.equal procname methname && A.mem (pvar, []) aliasset then target else search_target_tuple_by_pvar_inner pvar methname t in
  search_target_tuple_by_pvar_inner pvar methname elements


(* list version of the above *)
let search_target_tuples_by_pvar (pvar:Var.t) (methname:Procname.t) (tupleset:S.t) =
  let elements = S.elements tupleset in
  let rec search_target_tuples_by_pvar_inner pvar (methname:Procname.t) elements = 
    match elements with
    | [] -> []
    | ((procname, _, _, aliasset) as target)::t ->
        if Procname.equal procname methname && A.mem (pvar, []) aliasset
        then target::search_target_tuples_by_pvar_inner pvar methname t
        else search_target_tuples_by_pvar_inner pvar methname t in
  search_target_tuples_by_pvar_inner pvar methname elements


let search_target_tuple_by_id (id:Ident.t) (methname:Procname.t) (astate_set:S.t) =
  (* L.d_printfln "id: %a, methname: %a, tupleset: %a@." Ident.pp id Procname.pp methname S.pp tupleset; *)
  let elements = S.elements astate_set in
  let rec search_target_tuple_by_id_inner id (methname:Procname.t) elements = 
    match elements with
    | [] -> L.die InternalError "search_target_tuple_by_id failed, id: %a, methname: %a, tupleset: %a@." Ident.pp id Procname.pp methname S.pp astate_set
    | ((procname, _, _, aliasset) as target)::t ->
        if Procname.equal procname methname && A.mem (Var.of_id id, []) aliasset then target else search_target_tuple_by_id_inner id methname t in
  search_target_tuple_by_id_inner id methname elements


let search_target_tuples_by_id (id:Ident.t) (methname:Procname.t) (astate_set:S.t) =
  let elements = S.elements astate_set in
  let rec search_target_tuples_by_id_inner id (methname:Procname.t) elements acc = 
    match elements with
    | [] -> acc
    | ((procname, _, _, aliasset) as target)::t ->
        if Procname.equal procname methname && A.mem (Var.of_id id, []) aliasset
        then search_target_tuples_by_id_inner id methname t (target::acc)
        else search_target_tuples_by_id_inner id methname t acc in
  search_target_tuples_by_id_inner id methname elements []


let weak_search_target_tuple_by_id (id:Ident.t) (astate_set:S.t) =
  let elements = S.elements astate_set in
  let rec weak_search_target_tuple_by_id_inner id (elements:S.elt list) = 
    match elements with
    | [] -> L.die InternalError "weak_search_target_tuple_by_id failed, id: %a, astate_set: %a@." Ident.pp id S.pp astate_set
    | target::t ->
        let aliasset = fourth_of target in
        if A.mem (Var.of_id id, []) aliasset then target else weak_search_target_tuple_by_id_inner id t in
  weak_search_target_tuple_by_id_inner id elements


let is_return_ap (ap:A.elt) =
  let var, _ = ap in
  Var.is_return var


let find_tuples_with_ret (tupleset:S.t) (methname:Procname.t) =
  let elements = S.elements tupleset in
  let rec find_tuple_with_ret_inner (tuplelist:T.t list) (methname:Procname.t) (acc:T.t list) =
    match tuplelist with
    | [] -> acc
    | (procname, _, _, aliasset) as target :: t ->
        if Procname.equal procname methname && A.exists is_return_ap aliasset
        then find_tuple_with_ret_inner t methname (target::acc)
        else find_tuple_with_ret_inner t methname acc in
  find_tuple_with_ret_inner elements methname []


let search_target_tuples_by_vardef (pv:Var.t) (methname:Procname.t) (tupleset:S.t) =
  let elements = S.elements tupleset in
  let rec search_target_tuples_by_vardef_inner pv (methname:Procname.t) elements acc = 
    match elements with
    | [] -> acc
    | ((procname, (vardef, _), _, _) as target) :: t ->
        if Procname.equal procname methname && Var.equal vardef pv
        then search_target_tuples_by_vardef_inner pv methname t (target::acc)
        else search_target_tuples_by_vardef_inner pv methname t acc in
  search_target_tuples_by_vardef_inner pv methname elements []


let search_target_tuples_by_vardef_ap (pv_ap:MyAccessPath.t) (methname:Procname.t) (tupleset:S.t) =
  let elements = S.elements tupleset in
  let rec search_target_tuples_by_vardef_ap_inner pv_ap methname elements acc =
    match elements with
    | [] -> acc
    | ((procname, var_ap, _, _) as target) :: t ->
        if Procname.equal procname methname && MyAccessPath.equal pv_ap var_ap
        then search_target_tuples_by_vardef_ap_inner pv_ap methname t (target::acc)
        else search_target_tuples_by_vardef_ap_inner pv_ap methname t acc in
  search_target_tuples_by_vardef_ap_inner pv_ap methname elements []


let pp_tuplelist fmt (tuplelist:T.t list) : unit =
  F.fprintf fmt "[";
  List.iter ~f:(fun tup -> F.fprintf fmt "%a, " T.pp tup) tuplelist;
  F.fprintf fmt "]"


let rec search_tuple_by_loc (loc_set:LocationSet.t) (tuplelist:T.t list) =
  match tuplelist with
  | [] -> L.die InternalError "search_tuple_by_loc failed, loc_set: %a, tuplelist: %a@." LocationSet.pp loc_set pp_tuplelist tuplelist
  | tuple::t ->
      let l = third_of tuple in
      if LocationSet.equal loc_set l || LocationSet.subset l loc_set then tuple else search_tuple_by_loc loc_set t


let rec search_astate_by_loc (loc_set:LocationSet.t) (tuplelist:T.t list) =
  match tuplelist with
  | [] -> L.die InternalError "search_astate_by_loc failed, loc_set %a@." LocationSet.pp loc_set
  | astate::t ->
      let l = third_of astate in
      if LocationSet.equal loc_set l then astate else search_astate_by_loc loc_set t


(** List version of search_tuple_by_loc *)
let rec search_tuples_by_loc (loc_set:LocationSet.t) (tuplelist:S.elt list) =
  match tuplelist with
  | [] -> []
  | tuple::t ->
      let l = third_of tuple in
      if LocationSet.equal loc_set l
      then tuple::search_tuples_by_loc loc_set t
      else search_tuples_by_loc loc_set t


  (* x => y: y is more recent than x in a same file *)
  let (=>) (x:LocationSet.t) (y:LocationSet.t) =
    let x_min = LocationSet.min_elt x in
    let y_min = LocationSet.min_elt y in
    let loc_cond = x_min.line <= y_min.line in
    SourceFile.equal x_min.file y_min.file && loc_cond


    (* x ==> y: y is STRICTLY more recent than x in a same file *)
  let (==>) (x:LocationSet.t) (y:LocationSet.t) =
    let x_min = LocationSet.min_elt x in
    let y_min = LocationSet.min_elt y in
    let loc_cond = x_min.line < y_min.line in
    SourceFile.equal x_min.file y_min.file && loc_cond


let find_least_linenumber (statelist:T.t list) : T.t =
  let rec find_least_linenumber_inner (statelist:T.t list) (current_least:T.t) : T.t =
    match statelist with
    | [] -> current_least
    | targetState::t ->
        let snd_target = third_of targetState in
        let snd_current = third_of current_least in
        if snd_target ==> snd_current
        then find_least_linenumber_inner t targetState
        else find_least_linenumber_inner t current_least in
  find_least_linenumber_inner statelist (List.nth_exn statelist 0)


(** pick the earliest TUPLE within a list of astates *)
let find_earliest_tuple_within (astatelist:S.elt list) : T.t =
  let locations = List.sort ~compare:LocationSet.compare (List.map ~f:third_of astatelist) in
  match List.nth locations 0 with
  | Some earliest_location -> search_tuple_by_loc earliest_location astatelist
  | None -> L.die InternalError "find_earliest_tuple_within failed, astatelist: %a@." S.pp (S.of_list astatelist)


(** pick the earliest ASTATE within a list of astates *)
let find_earliest_astate_within (astatelist:S.elt list) : T.t =
  let locations = List.sort ~compare:LocationSet.compare (List.map ~f:third_of astatelist) in
  match List.nth locations 0 with
  | Some earliest_location -> search_astate_by_loc earliest_location astatelist
  | None -> L.die InternalError "find_earliest_astate_within failed, astatelist: %a@." S.pp (S.of_list astatelist)


let find_earliest_astate_of_var_within (tuplelist:S.elt list) : T.t =
  let vartuples = (* List.filter ~f:(fun tup -> Var.equal var (second_of tup)) *) tuplelist in
  find_earliest_astate_within vartuples


let is_program_var_ap (ap:A.elt) : bool =
  let var, _ = ap in
  match var with
  | LogicalVar _ -> false
  | ProgramVar _ -> true


let find_var_being_returned (aliasset:A.t) : Var.t =
  let elements = A.elements aliasset in
  let filtered = List.filter ~f:is_program_var_ap elements
                 |> List.filter ~f:(is_return_ap >> not) in
  match filtered with
  | [(var, _)] -> var
  | _ -> L.die InternalError "find_var_being_returned falied, aliasset: %a@." A.pp aliasset


let batch_search_target_tuples_by_vardef (varlist:Var.t list) (current_methname:Procname.t) (astate_set:S.t) =
  List.fold_left ~f:(fun (prev_bool, prev_list) var ->
      let search_result = search_target_tuples_by_vardef var current_methname astate_set in
      if Int.equal (List.length search_result) 0
      then (false || prev_bool, prev_list)
      else (true, search_result)) ~init:(false, [])
    varlist


let is_program_var (var:Var.t) : bool =
  match var with
  | LogicalVar _ -> false
  | ProgramVar _ -> true


(** Given a alias set, finds the tuple with a Pvar in it. *)
let find_another_pvar_vardef (varset:A.t) : A.elt =
  let varlist = A.elements varset in
  let rec find_another_pvar_vardef_inner (varlist:A.elt list) =
    match varlist with
    | [] -> L.die InternalError "find_another_pvar_vardef failed, varset: %a@." A.pp varset
    | (var, _) as target::t -> if is_program_var var then target else find_another_pvar_vardef_inner t in
  find_another_pvar_vardef_inner varlist


let extract_from_singleton (singleton:A.t) : A.elt =
  match A.elements singleton with
  | [x] -> x
  | _ -> L.die InternalError "extract_from_singleton failed, singleton: %a@." A.pp singleton


(** A.t의 aliasset 안에서 pvar 튜플을 찾아낸다. *)
let find_pvar_ap_in (aliasset:A.t) : A.elt =
  let elements = A.elements aliasset in
  let rec find_pvar_ap_in_inner (elements:A.elt list) (acc:A.elt list) =
  match elements with
  | [] -> acc
  | (var, _) as target::t ->
      if is_program_var var then target::acc else find_pvar_ap_in_inner t acc in
      let result = find_pvar_ap_in_inner elements [] in
      begin match result with
      | [] -> L.die InternalError "find_pvar_ap_in failed, aliasset: %a@." A.pp aliasset
      | [x] -> x
      | _ -> L.die InternalError "find_pvar_ap_in failed, aliasset: %a@." A.pp aliasset end


(** aliasset이 주어졌을 때 그 중에서 field를 갖고 있는 튜플을 내놓는다. *)
let find_ap_with_field (aliasset:A.t) =
  let elements = A.elements aliasset in
    let rec find_ap_with_field_inner (elements:A.elt list) =
    match elements with
    | [] -> L.die InternalError "find_ap_with_field failed, aliasset: %a@." A.pp aliasset
    | (_, aplst) as target :: t -> if List.length aplst > 0 then target else find_ap_with_field_inner t in
  find_ap_with_field_inner elements


let search_target_tuple_by_vardef_ap (ap:MyAccessPath.t) (methname:Procname.t) (astate_set:S.t) =
  let elements = S.elements astate_set in
  let rec search_target_tuple_by_ap_inner (ap:MyAccessPath.t) (methname:Procname.t) (elements:S.elt list) = 
    match elements with
    | [] -> L.die InternalError "search_target_tuple_by_ap failed, methname: %a, elements: %a" Procname.pp methname pp_tuplelist elements
    | ((procname, vardef, _, _) as target)::t ->
        if Procname.equal procname methname && MyAccessPath.equal ap vardef
        then target
        else search_target_tuple_by_ap_inner ap methname t in
  search_target_tuple_by_ap_inner ap methname elements

