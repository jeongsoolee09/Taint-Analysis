open! IStd

module L = Logging
module F = Format
module A = DefLocAliasDomain.SetofAliases
module S = DefLocAliasDomain.AbstractState

exception SearchByPvarFailed
exception SearchByIdFailed
exception WeakSearchByIdFailed
exception SearchRecentVardefFailed
exception SearchByVardefFailed
exception SearchByLocFailed


let placeholder_vardef (pid:Procname.t) : Var.t =
  let mangled = Mangled.from_string "ph" in
  let ph_vardef = Pvar.mk mangled pid in
  Var.of_pvar ph_vardef


let search_target_tuple_by_pvar (pvar:Var.t) (methname:Procname.t) (tupleset:S.t) =
  let elements = S.elements tupleset in
  let rec search_target_tuple_by_pvar_inner pvar (methname:Procname.t) elements = 
    match elements with
    | [] -> raise SearchByPvarFailed
    | ((procname, _, _, aliasset) as target)::t ->
        if Procname.equal procname methname && A.mem pvar aliasset then target else search_target_tuple_by_pvar_inner pvar methname t in
  search_target_tuple_by_pvar_inner pvar methname elements


(* 위 함수의 리스트 버전 *)
let search_target_tuples_by_pvar (pvar:Var.t) (methname:Procname.t) (tupleset:S.t) =
  let elements = S.elements tupleset in
  let rec search_target_tuples_by_pvar_inner pvar (methname:Procname.t) elements = 
    match elements with
    | [] -> []
    | ((procname, _, _, aliasset) as target)::t ->
        if Procname.equal procname methname && A.mem pvar aliasset
        then target::search_target_tuples_by_pvar_inner pvar methname t
        else search_target_tuples_by_pvar_inner pvar methname t in
  search_target_tuples_by_pvar_inner pvar methname elements


let search_target_tuple_by_id (id:Ident.t) (methname:Procname.t) (tupleset:S.t) =
  let elements = S.elements tupleset in
  let rec search_target_tuple_by_id_inner id (methname:Procname.t) elements = 
    match elements with
    | [] -> raise SearchByIdFailed
    | ((procname, _, _, aliasset) as target)::t ->
        if Procname.equal procname methname && A.mem id aliasset then target else search_target_tuple_by_id_inner id methname t in
  search_target_tuple_by_id_inner (Var.of_id id) methname elements


let weak_search_target_tuple_by_id (id:Ident.t) (tupleset:S.t) =
  let elements = S.elements tupleset in
  let rec weak_search_target_tuple_by_id_inner (id:Var.t) (elements:S.elt list) = 
    match elements with
    | [] -> raise WeakSearchByIdFailed
    | ((_, _, _, aliasset) as target)::t ->
        if A.mem id aliasset then target else weak_search_target_tuple_by_id_inner id t in
  weak_search_target_tuple_by_id_inner (Var.of_id id) elements


let search_target_tuples_by_id (id:Ident.t) (methname:Procname.t) (tupleset:S.t) =
  let elements = S.elements tupleset in
  let rec search_target_tuples_by_id_inner id (methname:Procname.t) elements acc = 
    match elements with
    | [] -> acc
    | ((procname, _, _, aliasset) as target)::t ->
        if Procname.equal procname methname && A.mem id aliasset
        then search_target_tuples_by_id_inner id methname t (target::acc)
        else search_target_tuples_by_id_inner id methname t acc in
  search_target_tuples_by_id_inner (Var.of_id id) methname elements []


let find_tuple_with_ret (tupleset:S.t) (methname:Procname.t) =
  let elements = S.elements tupleset in
  let rec find_tuple_with_ret_inner (tuplelist:S.elt list) (methname:Procname.t) (acc:S.elt list) =
    match tuplelist with
    | [] -> acc
    | (procname, _, _, aliasset) as target :: t ->
        if Procname.equal procname methname && A.exists Var.is_return aliasset
        then find_tuple_with_ret_inner t methname (target::acc)
        else find_tuple_with_ret_inner t methname acc in
  find_tuple_with_ret_inner elements methname []


let search_target_tuples_by_vardef (pv:Var.t) (methname:Procname.t) (tupleset:S.t) =
  let elements = S.elements tupleset in
  let rec search_target_tuples_by_vardef_inner pv (methname:Procname.t) elements acc = 
    match elements with
    | [] -> acc
    | ((procname, vardef, _, _) as target)::t ->
        if Procname.equal procname methname && Var.equal vardef pv
        then search_target_tuples_by_vardef_inner pv methname t (target::acc)
        else search_target_tuples_by_vardef_inner pv methname t acc in
  let result = search_target_tuples_by_vardef_inner pv methname elements [] in
  if Int.equal (List.length result) 0 then raise SearchByVardefFailed else result 


let rec search_tuple_by_loc (loc:Location.t) (tuplelist:S.elt list) =
  match tuplelist with
  | [] -> raise SearchByLocFailed
  | ((_,_,l,_) as target)::t ->
      if Location.equal loc l
      then target
      else search_tuple_by_loc loc t


  (* x ==> y: y is more recent than x in a same file *)
  let (==>) (x:Location.t) (y:Location.t) = SourceFile.equal x.file y.file && x.line < y.line


let find_least_linenumber (tuplelist:S.elt list) =
  let rec find_least_linenumber_inner (tuplelist:S.elt list) current_least =
    match tuplelist with
    | [] -> current_least
    | targetTuple::t ->
        let (_, _, snd_target, _) = targetTuple in
        let (_, _, snd_current, _) = current_least in
        if snd_target ==> snd_current
        then find_least_linenumber_inner t targetTuple
        else find_least_linenumber_inner t current_least in
  find_least_linenumber_inner tuplelist (List.nth_exn tuplelist 0)
