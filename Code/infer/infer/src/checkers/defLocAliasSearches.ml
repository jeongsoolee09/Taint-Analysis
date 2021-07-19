open! IStd
open DefLocAliasDomain
open DefLocAliasLogicTests
module L = Logging
module F = Format
module P = DefLocAliasDomain.AbstractPair
module S = DefLocAliasDomain.AbstractStateSetFinite
module A = DefLocAliasDomain.SetofAliases
module T = DefLocAliasDomain.AbstractState

exception TODO of string

exception IDontKnow

let pp_tuplelist fmt (lst : T.t list) =
  F.fprintf fmt "[" ;
  List.iter ~f:(fun tup -> F.fprintf fmt "%a, " T.pp tup) lst ;
  F.fprintf fmt "]"


let placeholder_vardef (pid : Procname.t) : Var.t =
  let mangled = Mangled.from_string "ph" in
  let ph_vardef = Pvar.mk mangled pid in
  Var.of_pvar ph_vardef


let search_target_tuple_by_pvar (pvar : Var.t) (methname : Procname.t) (astate_set : S.t) : T.t =
  let elements = S.elements astate_set in
  let rec inner pvar (methname : Procname.t) elements =
    match elements with
    | [] ->
        L.die InternalError
          "search_target_tuple_by_pvar failed, pvar: %a, methname:%a, astate_set:%a@." Var.pp pvar
          Procname.pp methname S.pp astate_set
    | ((procname, _, _, aliasset) as target) :: t ->
        if Procname.equal procname methname && A.mem (pvar, []) aliasset then target
        else inner pvar methname t
  in
  inner pvar methname elements


(* list version of the above *)
let search_target_tuples_by_pvar (pvar : Var.t) (methname : Procname.t) (tupleset : S.t) : T.t list
    =
  let elements = S.elements tupleset in
  let rec inner pvar (methname : Procname.t) elements =
    match elements with
    | [] ->
        []
    | ((procname, _, _, aliasset) as target) :: t ->
        if Procname.equal procname methname && A.mem (pvar, []) aliasset then
          target :: inner pvar methname t
        else inner pvar methname t
  in
  inner pvar methname elements


let search_target_tuple_by_id (id : Ident.t) (methname : Procname.t) (astate_set : S.t) : T.t =
  (* L.d_printfln "id: %a, methname: %a, tupleset: %a@." Ident.pp id Procname.pp methname S.pp tupleset; *)
  let elements = S.elements astate_set in
  let rec inner id (methname : Procname.t) elements =
    match elements with
    | [] ->
        (* L.die InternalError "search_target_tuple_by_id failed, id: %a, methname: %a, tupleset: %a@." Ident.pp id Procname.pp methname S.pp astate_set *)
        raise IDontKnow
    | ((procname, _, _, aliasset) as target) :: t ->
        if Procname.equal procname methname && A.mem (Var.of_id id, []) aliasset then target
        else inner id methname t
  in
  inner id methname elements


let search_target_tuple_by_pvar_ap (ap : MyAccessPath.t) (methname : Procname.t) (astate_set : S.t)
    : T.t =
  let elements = S.elements astate_set in
  let rec inner pvar (methname : Procname.t) elements =
    match elements with
    | [] ->
        L.die InternalError
          "search_target_tuple_by_pvar_ap failed, ap: %a, methname:%a, astate_set:%a@."
          MyAccessPath.pp pvar Procname.pp methname S.pp astate_set
    | ((procname, _, _, aliasset) as target) :: t ->
        if Procname.equal procname methname && A.mem ap aliasset then target
        else inner pvar methname t
  in
  inner ap methname elements


let search_target_tuples_by_id (id : Ident.t) (methname : Procname.t) (astate_set : S.t) : T.t list
    =
  let elements = S.elements astate_set in
  let rec inner id (methname : Procname.t) elements acc =
    match elements with
    | [] ->
        acc
    | ((procname, _, _, aliasset) as target) :: t ->
        if Procname.equal procname methname && A.mem (Var.of_id id, []) aliasset then
          inner id methname t (target :: acc)
        else inner id methname t acc
  in
  inner id methname elements []


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


let find_tuples_with_ret (tupleset : S.t) : T.t list =
  S.fold
    (fun statetup acc ->
      if A.exists is_return_ap (fourth_of statetup) then statetup :: acc else acc)
    tupleset []


let search_target_tuples_by_vardef (pv : Var.t) (methname : Procname.t) (tupleset : S.t) : T.t list
    =
  let elements = S.elements tupleset in
  let rec inner pv (methname : Procname.t) elements acc =
    match elements with
    | [] ->
        acc
    | ((procname, (vardef, _), _, _) as target) :: t ->
        if Procname.equal procname methname && Var.equal vardef pv then
          inner pv methname t (target :: acc)
        else inner pv methname t acc
  in
  inner pv methname elements []


let search_target_tuples_by_vardef_ap (pv_ap : MyAccessPath.t) (methname : Procname.t)
    (tupleset : S.t) : T.t list =
  let elements = S.elements tupleset in
  let rec inner pv_ap methname elements acc =
    match elements with
    | [] ->
        acc
    | ((procname, var_ap, _, _) as target) :: t ->
        if Procname.equal procname methname && MyAccessPath.equal pv_ap var_ap then
          inner pv_ap methname t (target :: acc)
        else inner pv_ap methname t acc
  in
  inner pv_ap methname elements []


let pp_tuplelist fmt (tuplelist : T.t list) : unit =
  F.fprintf fmt "[" ;
  List.iter ~f:(fun tup -> F.fprintf fmt "%a, " T.pp tup) tuplelist ;
  F.fprintf fmt "]"


let rec search_tuple_by_loc (loc_set : LocationSet.t) (tuplelist : T.t list) : T.t =
  match tuplelist with
  | [] ->
      (* L.die InternalError "search_tuple_by_loc failed, loc_set: %a, tuplelist: %a@." LocationSet.pp loc_set pp_tuplelist tuplelist *)
      raise IDontKnow
  | tuple :: t ->
      let l = third_of tuple in
      if LocationSet.equal loc_set l || LocationSet.subset l loc_set then tuple
      else search_tuple_by_loc loc_set t


let rec search_astate_by_loc (loc_set : LocationSet.t) (tuplelist : T.t list) : T.t =
  match tuplelist with
  | [] ->
      L.die InternalError "search_astate_by_loc failed, loc_set %a@." LocationSet.pp loc_set
  | astate :: t ->
      let l = third_of astate in
      if LocationSet.equal loc_set l then astate else search_astate_by_loc loc_set t


(** List version of search_tuple_by_loc *)
let rec search_tuples_by_loc (loc_set : LocationSet.t) (tuplelist : S.elt list) : T.t list =
  match tuplelist with
  | [] ->
      []
  | tuple :: t ->
      let l = third_of tuple in
      if LocationSet.equal loc_set l then tuple :: search_tuples_by_loc loc_set t
      else search_tuples_by_loc loc_set t


(* x => y: y is more recent than x in a same file *)
let ( => ) (x : LocationSet.t) (y : LocationSet.t) : bool =
  let x_min = LocationSet.min_elt x in
  let y_min = LocationSet.min_elt y in
  let loc_cond = x_min.line <= y_min.line in
  SourceFile.equal x_min.file y_min.file && loc_cond


(* x ==> y: y is STRICTLY more recent than x in a same file *)
let ( ==> ) (x : LocationSet.t) (y : LocationSet.t) : bool =
  let x_min = LocationSet.min_elt x in
  let y_min = LocationSet.min_elt y in
  let loc_cond = x_min.line < y_min.line in
  SourceFile.equal x_min.file y_min.file && loc_cond


let find_least_linenumber (statelist : T.t list) : T.t =
  let rec inner (statelist : T.t list) (current_least : T.t) : T.t =
    L.d_printfln "statelist: %a@." pp_tuplelist statelist ;
    match statelist with
    | [] ->
        current_least
    | targetState :: t ->
        let snd_target = third_of targetState in
        let snd_current = third_of current_least in
        if snd_target ==> snd_current then inner t targetState else inner t current_least
  in
  inner statelist (List.nth_exn statelist 0)


let find_most_linenumber (statelist : T.t list) : T.t =
  let rec inner (statelist : T.t list) (current_least : T.t) : T.t =
    L.d_printfln "statelist: %a@." pp_tuplelist statelist ;
    match statelist with
    | [] ->
        current_least
    | targetState :: t ->
        let snd_target = third_of targetState in
        let snd_current = third_of current_least in
        if snd_current ==> snd_target then inner t targetState else inner t current_least
  in
  inner statelist (List.nth_exn statelist 0)


(** pick the earliest TUPLE within a list of astates *)
let find_earliest_tuple_within (astatelist : S.elt list) : T.t =
  let locations = List.sort ~compare:LocationSet.compare (List.map ~f:third_of astatelist) in
  match List.nth locations 0 with
  | Some earliest_location ->
      search_tuple_by_loc earliest_location astatelist
  | None ->
      L.die InternalError "find_earliest_tuple_within failed, astatelist: %a@." S.pp
        (S.of_list astatelist)


(** pick the earliest ASTATE within a list of astates *)
let find_earliest_astate_within (astatelist : S.elt list) (methname : Procname.t) : T.t =
  let locations = List.sort ~compare:LocationSet.compare (List.map ~f:third_of astatelist) in
  match List.nth locations 0 with
  | Some earliest_location ->
      (* L.progress "looking for %a in %a@." LocationSet.pp earliest_location pp_tuplelist astatelist; *)
      search_astate_by_loc earliest_location astatelist
  | None ->
      raise IDontKnow


(* L.die InternalError "find_earliest_astate_within failed, astatelist: %a, Method: %a@." S.pp (S.of_list astatelist) Procname.pp methname *)

let find_earliest_astate_of_var_within (tuplelist : S.elt list) (methname : Procname.t) : T.t =
  let vartuples = (* List.filter ~f:(fun tup -> Var.equal var (second_of tup)) *) tuplelist in
  find_earliest_astate_within vartuples methname


let find_var_being_returned (aliasset : A.t) : Var.t =
  let elements = A.elements aliasset in
  let filtered =
    List.filter
      ~f:(fun ap ->
        is_program_var_ap ap && (not @@ is_return_ap ap) && (not @@ Var.is_this (fst ap)))
      elements
  in
  match filtered with
  | [(var, _)] ->
      var
  | _ ->
      L.die InternalError "find_var_being_returned falied, aliasset: %a@." A.pp aliasset


let batch_search_target_tuples_by_vardef (varlist : Var.t list) (current_methname : Procname.t)
    (astate_set : S.t) : bool * T.t list =
  List.fold_left
    ~f:(fun (prev_bool, prev_list) var ->
      let search_result = search_target_tuples_by_vardef var current_methname astate_set in
      if Int.equal (List.length search_result) 0 then (false || prev_bool, prev_list)
      else (true, search_result))
    ~init:(false, []) varlist


(** Given a alias set, finds the tuple with a Pvar in it. *)
let find_another_pvar_vardef (varset : A.t) : A.elt =
  let varlist = A.elements varset in
  let rec inner (varlist : A.elt list) =
    match varlist with
    | [] ->
        L.die InternalError "find_another_pvar_vardef failed, varset: %a@." A.pp varset
    | ((var, _) as target) :: t ->
        if is_program_var var then target else inner t
  in
  inner varlist


let extract_from_singleton (singleton : A.t) : A.elt =
  match A.elements singleton with
  | [] ->
      L.die InternalError "extract_from_singleton failed (too few), aliasset: %a@." A.pp singleton
  | [x] ->
      x
  | _ ->
      L.die InternalError "extract_from_singleton failed (too many), singleton: %a@." A.pp singleton


(** A.t의 aliasset 안에서 pvar 튜플을 찾아낸다. *)
let find_pvar_ap_in (aliasset : A.t) : A.elt =
  let elements = A.elements aliasset in
  let rec inner (elements : A.elt list) (acc : A.elt list) =
    match elements with
    | [] ->
        acc
    | ((var, _) as target) :: t ->
        if is_program_var var then target :: acc else inner t acc
  in
  let result = inner elements [] in
  match result with
  | [] ->
      L.die InternalError "find_pvar_ap_in failed (too few), aliasset: %a@." A.pp aliasset
  | [x] ->
      x
  | _ ->
      L.die InternalError "find_pvar_ap_in failed (too many), aliasset: %a@." A.pp aliasset


(** aliasset이 주어졌을 때 그 중에서 field를 갖고 있는 튜플을 내놓는다. *)
let find_ap_with_field (aliasset : A.t) : A.elt =
  let elements = A.elements aliasset in
  let rec inner (elements : A.elt list) =
    match elements with
    | [] ->
        L.die InternalError "find_ap_with_field failed, aliasset: %a@." A.pp aliasset
    | ((_, aplst) as target) :: t ->
        if List.length aplst > 0 then target else inner t
  in
  inner elements


let search_target_tuple_by_vardef_ap (ap : MyAccessPath.t) (methname : Procname.t)
    (astate_set : S.t) : T.t =
  let elements = S.elements astate_set in
  let rec inner (ap : MyAccessPath.t) (methname : Procname.t) (elements : S.elt list) =
    match elements with
    | [] ->
        raise IDontKnow
        (* L.die InternalError "search_target_tuple_by_vardef_ap failed, ap:%a, methname: %a, elements: %a" MyAccessPath.pp ap Procname.pp methname pp_tuplelist elements *)
    | ((procname, vardef, _, _) as target) :: t ->
        if Procname.equal procname methname && MyAccessPath.equal ap vardef then target
        else inner ap methname t
  in
  inner ap methname elements


let search_astate_holding_param (astate_set : S.t) (param : A.elt) : S.elt =
  let collected =
    S.fold
      (fun astate acc -> if A.mem param @@ fourth_of astate then astate :: acc else acc)
      astate_set []
  in
  assert (Int.equal (List.length collected) 1) ;
  List.hd_exn collected


let find_param_ap (aliasset : A.t) (current_methname : Procname.t) : A.elt =
  let res =
    A.fold
      (fun ap acc ->
        if is_foreign_ap ap current_methname && (not @@ is_returnv_ap ap) then ap :: acc else acc)
      aliasset []
  in
  match res with
  | [] ->
      L.die InternalError "find_param_ap failed (no match): aliasset: %a, current_methname: %a@."
        A.pp aliasset Procname.pp current_methname
  | [ap] ->
      ap
  | _ ->
      L.die InternalError
        "find_param_ap failed (too many matches): aliasset: %a, current_methname: %a@." A.pp
        aliasset Procname.pp current_methname


let find_foreign_ap (aliasset : A.t) (current_methname : Procname.t) : A.elt option =
  let res =
    A.fold (fun ap acc -> if is_foreign_ap ap current_methname then ap :: acc else acc) aliasset []
  in
  match res with [ap] -> Some ap | _ -> None


let get_declaring_function_ap_exn (ap : A.elt) : Procname.t =
  let var, _ = ap in
  match var with
  | LogicalVar _ ->
      L.die InternalError "get_declaring_function_ap_exn failed: %a@." MyAccessPath.pp ap
  | ProgramVar pvar -> (
    match Pvar.get_declaring_function pvar with
    | None ->
        L.die InternalError "get_declaring_function_ap_exn failed: %a@." MyAccessPath.pp ap
    | Some procname ->
        procname )


let find_returnv_or_carriedover_statetup (astate_set : S.t) (callee_methname : Procname.t)
    (current_methname : Procname.t) : S.elt list =
  S.fold
    (fun astate acc ->
      match find_foreign_ap (fourth_of astate) current_methname with
      | None ->
          acc
      | Some ap ->
          let declaring_function = get_declaring_function_ap_exn ap in
          if
            (not @@ is_callv_ap ap)
            && (not @@ is_param_ap ap)
            && (not @@ Var.is_this (fst ap))
            && Procname.equal declaring_function callee_methname
          then astate :: acc
          else acc)
    astate_set []


let find_returnv_or_carriedover_ap (caller_astate_set : S.t) (callee_astate_set : S.t) : A.elt list
    =
  let carried_over_vars =
    S.fold
      (fun statetup acc ->
        if A.exists is_return_ap (fourth_of statetup) then second_of statetup :: acc else acc)
      callee_astate_set []
  in
  let returnvs =
    S.fold
      (fun statetup acc ->
        let returnvs =
          A.fold
            (fun aliastup acc' -> if is_returnv_ap aliastup then aliastup :: acc' else acc')
            (fourth_of statetup) []
        in
        returnvs @ acc)
      caller_astate_set []
  in
  carried_over_vars @ returnvs
