open! IStd
open DefLocAliasDomain

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
exception NoEarliestTupleInState
exception TooManyReturns


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


let search_target_tuple_by_id (id:Ident.t) (methname:Procname.t) (tupleset:S.t) =
  let elements = S.elements tupleset in
  let rec search_target_tuple_by_id_inner id (methname:Procname.t) elements = 
    match elements with
    | [] -> raise SearchByIdFailed
    | ((procname, _, _, aliasset) as target)::t ->
        if Procname.equal procname methname && A.mem (Var.of_id id, []) aliasset then target else search_target_tuple_by_id_inner id methname t in
  search_target_tuple_by_id_inner id methname elements


let weak_search_target_tuple_by_id (id:Ident.t) (tupleset:S.t) =
  let elements = S.elements tupleset in
  let rec weak_search_target_tuple_by_id_inner id (elements:S.elt list) = 
    match elements with
    | [] -> raise WeakSearchByIdFailed
    | ((_, _, _, aliasset) as target)::t ->
        if A.mem (Var.of_id id, []) aliasset then target else weak_search_target_tuple_by_id_inner id t in
  weak_search_target_tuple_by_id_inner id elements


let search_target_tuples_by_id (id:Ident.t) (methname:Procname.t) (tupleset:S.t) =
  let elements = S.elements tupleset in
  let rec search_target_tuples_by_id_inner id (methname:Procname.t) elements acc = 
    match elements with
    | [] -> acc
    | ((procname, _, _, aliasset) as target)::t ->
        if Procname.equal procname methname && A.mem (Var.of_id id, []) aliasset
        then search_target_tuples_by_id_inner id methname t (target::acc)
        else search_target_tuples_by_id_inner id methname t acc in
  search_target_tuples_by_id_inner id methname elements []


let is_return_ap (ap:A.elt) =
  let var, _ = ap in
  Var.is_return var


let find_tuple_with_ret (tupleset:S.t) (methname:Procname.t) =
  let elements = S.elements tupleset in
  let rec find_tuple_with_ret_inner (tuplelist:S.elt list) (methname:Procname.t) (acc:S.elt list) =
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



let rec search_tuple_by_loc (loc:Location.t) (tuplelist:S.elt list) =
  match tuplelist with
  | [] -> raise SearchByLocFailed
  | ((_,_,l,_) as target)::t ->
      if Location.equal loc l
      then target
      else search_tuple_by_loc loc t


(** List version of search_tuple_by_loc *)
let rec search_tuples_by_loc (loc:Location.t) (tuplelist:S.elt list) =
  match tuplelist with
  | [] -> []
  | ((_,_,l,_) as target)::t ->
      if Location.equal loc l
      then target::search_tuples_by_loc loc t
      else search_tuples_by_loc loc t


(* x => y: y is more recent than x in a same file *)
let (=>) (x:Location.t) (y:Location.t) =
  (* L.progress "lhs line: %d, rhs line: %d\n" x.line y.line; *)
  SourceFile.equal x.file y.file && x.line <= y.line


  (* x ==> y: y is STRICTLY more recent than x in a same file *)
let (==>) (x:Location.t) (y:Location.t) =
  (* L.progress "lhs line: %d, rhs line: %d\n" x.line y.line; *)
  SourceFile.equal x.file y.file && x.line < y.line


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


let find_earliest_tuple_within (tuplelist:S.elt list): S.elt =
  let locations = List.sort ~compare:Location.compare (List.map ~f:third_of tuplelist) in
  match List.nth locations 0 with
  | Some earliest_location -> search_tuple_by_loc earliest_location tuplelist
  | None -> raise NoEarliestTupleInState


let find_earliest_tuple_of_var_within (tuplelist:S.elt list) : S.elt =
  let vartuples = (* List.filter ~f:(fun tup -> Var.equal var (second_of tup)) *) tuplelist in
  find_earliest_tuple_within vartuples


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
  | _ -> raise TooManyReturns


let batch_search_target_tuples_by_vardef (varlist:Var.t list) (current_methname:Procname.t) (astate:S.t) =
  List.fold_left ~f:(fun (prev_bool, prev_list) var ->
      let search_result = search_target_tuples_by_vardef var current_methname astate in
      if Int.equal (List.length search_result) 0
      then (false || prev_bool, prev_list)
      else (true, search_result)) ~init:(false, [])
    varlist

