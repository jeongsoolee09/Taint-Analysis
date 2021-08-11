open! IStd
open DefLocAliasDomain
open DefLocAliasPredicates
open DefLocAliasPP
module L = Logging
module F = Format
module P = DefLocAliasDomain.AbstractPair
module S = DefLocAliasDomain.AbstractStateSetFinite
module A = DefLocAliasDomain.SetofAliases
module T = DefLocAliasDomain.AbstractState

(* Exceptions ======================================= *)
(* ================================================== *)

exception SearchAstateByPVarFailed of string

exception SearchAstateByIdFailed of string

exception SearchAstateByLocFailed of string

exception FindEarliestAstateFailed of string

exception FindReturningVarFailed of string

exception FindAnotherPvarVardefFailed of string

exception FindPvarInAliassetFailed of string

exception FindAPWithFieldFailed of string

exception GetDeclaringFunctionFailed of string

exception ExtractLinumFromParamFailed of string

exception ExtractNumberFromCallvFailed of string

exception FindCallvGreaterThanFailed of string

(* Searching Functions ============================== *)
(* ================================================== *)

let search_target_tuple_by_pvar (pvar : Var.t) (methname : Procname.t) (astate_set : S.t) : T.t =
  let elements = S.elements astate_set in
  let rec inner pvar (methname : Procname.t) elements =
    match elements with
    | [] ->
        F.kasprintf
          (fun msg -> raise @@ SearchAstateByPVarFailed msg)
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
        F.kasprintf
          (fun msg -> raise @@ SearchAstateByIdFailed msg)
          "search_target_tuple_by_id failed, id: %a, methname: %a, tupleset: %a@." Ident.pp id
          Procname.pp methname S.pp astate_set
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
        F.kasprintf
          (fun msg -> raise @@ SearchAstateByPVarFailed msg)
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
        F.kasprintf
          (fun msg -> raise @@ SearchAstateByIdFailed msg)
          "weak_search_target_tuple_by_id failed, id: %a, astate_set: %a@." Ident.pp id S.pp
          astate_set
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


let rec search_tuple_by_loc (loc_set : LocationSet.t) (tuplelist : T.t list) : T.t =
  match tuplelist with
  | [] ->
      F.kasprintf
        (fun msg -> raise @@ SearchAstateByLocFailed msg)
        "search_tuple_by_loc failed, loc_set: %a, tuplelist: %a@." LocationSet.pp loc_set
        pp_tuplelist tuplelist
  | tuple :: t ->
      let l = third_of tuple in
      if LocationSet.equal loc_set l || LocationSet.subset l loc_set then tuple
      else search_tuple_by_loc loc_set t


let rec search_astate_by_loc (loc_set : LocationSet.t) (tuplelist : T.t list) : T.t =
  match tuplelist with
  | [] ->
      F.kasprintf
        (fun msg -> raise @@ SearchAstateByLocFailed msg)
        "search_astate_by_loc failed, loc_set: %a, tuplelist: %a@." LocationSet.pp loc_set
        pp_tuplelist tuplelist
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
  inner statelist @@ List.hd_exn statelist


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
  inner statelist @@ List.hd_exn statelist


(** pick the earliest TUPLE within a list of astates *)
let find_earliest_tuple_within (astatelist : S.elt list) : T.t =
  let locations = List.sort ~compare:LocationSet.compare (List.map ~f:third_of astatelist) in
  match List.nth locations 0 with
  | Some earliest_location ->
      search_tuple_by_loc earliest_location astatelist
  | None ->
      F.kasprintf
        (fun msg -> raise @@ FindEarliestAstateFailed msg)
        "find_earliest_tuple_within failed, astatelist: %a@." S.pp
      @@ S.of_list astatelist


(** pick the earliest ASTATE within a list of astates *)
let find_earliest_astate_within (astatelist : S.elt list) (methname : Procname.t) : T.t =
  let locations = List.sort ~compare:LocationSet.compare (List.map ~f:third_of astatelist) in
  match List.nth locations 0 with
  | Some earliest_location ->
      search_astate_by_loc earliest_location astatelist
  | None ->
      raise IDontKnow


let find_earliest_astate_of_var_within (tuplelist : S.elt list) (methname : Procname.t) : T.t =
  let vartuples = tuplelist in
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
      F.kasprintf
        (fun msg -> raise @@ FindReturningVarFailed msg)
        "find_var_being_returned falied, aliasset: %a@." A.pp aliasset


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
        F.kasprintf
          (fun msg -> raise @@ FindAnotherPvarVardefFailed msg)
          "find_another_pvar_vardef failed, varset: %a@." A.pp varset
    | ((var, _) as target) :: t ->
        if is_program_var var then target else inner t
  in
  inner varlist


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
      F.kasprintf
        (fun msg -> raise @@ FindPvarInAliassetFailed msg)
        "find_pvar_ap_in failed (no matches), aliasset: %a@." A.pp aliasset
  | [x] ->
      x
  | _ ->
      F.kasprintf
        (fun msg -> raise @@ FindPvarInAliassetFailed msg)
        "find_pvar_ap_in failed (too many matches), aliasset: %a@." A.pp aliasset


(** aliasset이 주어졌을 때 그 중에서 field를 갖고 있는 튜플을 내놓는다. *)
let find_ap_with_field (aliasset : A.t) : A.elt =
  let elements = A.elements aliasset in
  let rec inner (elements : A.elt list) =
    match elements with
    | [] ->
        F.kasprintf
          (fun msg -> raise @@ FindAPWithFieldFailed msg)
          "find_ap_with_field failed, aliasset: %a@." A.pp aliasset
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
        F.kasprintf
          (fun msg -> raise @@ SearchAstateByPVarFailed msg)
          "search_target_tuple_by_vardef_ap failed, ap:%a, methname: %a, elements: %a"
          MyAccessPath.pp ap Procname.pp methname pp_tuplelist elements
    | ((procname, vardef, _, _) as target) :: t ->
        if Procname.equal procname methname && MyAccessPath.equal ap vardef then target
        else inner ap methname t
  in
  inner ap methname elements


let find_foreign_ap (aliasset : A.t) (current_methname : Procname.t) : A.elt option =
  let res =
    A.fold (fun ap acc -> if is_foreign_ap ap current_methname then ap :: acc else acc) aliasset []
  in
  match res with [ap] -> Some ap | _ -> None


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


let extract_linum_from_param (ap : MyAccessPath.t) : int =
  match fst ap with
  | LogicalVar _ ->
      F.kasprintf
        (fun msg -> raise @@ ExtractLinumFromParamFailed msg)
        "extract_linum_from_param failed: ap: %a@." MyAccessPath.pp ap
  | ProgramVar pv -> (
    match is_param_ap ap with
    | true ->
        Pvar.to_string pv |> String.split ~on:'_'
        |> fun str_list -> List.nth_exn str_list 2 |> int_of_string
    | false ->
        F.kasprintf
          (fun msg -> raise @@ ExtractLinumFromParamFailed msg)
          "extract_linum_from_param failed: ap: %a@." MyAccessPath.pp ap )


let search_target_tuples_holding_param (location : int) (tuplelist : T.t list) : T.t list =
  List.fold
    ~f:(fun acc statetup ->
      let astateset = fourth_of statetup in
      let is_match =
        A.fold
          (fun ap acc' ->
            if is_param_ap ap then
              (is_param_ap ap && Int.equal (extract_linum_from_param ap) location) || acc'
            else acc')
          astateset false
      in
      if is_match then statetup :: acc else acc)
    ~init:[] tuplelist


let extract_number_from_callv (callv_ap : A.elt) : int =
  (* assert (is_callv_ap callv_ap) ; *)
  if not @@ is_callv_ap callv_ap then
    F.kasprintf
      (fun msg -> raise @@ ExtractNumberFromCallvFailed msg)
      "This is not a callv!: %a@." MyAccessPath.pp callv_ap ;
  let varname = F.asprintf "%a" Var.pp (fst callv_ap) in
  (* the callv naming scheme is callv_{number}: {callee_methname} *)
  let splitted = String.split varname ~on:':' in
  let callv_string = List.nth_exn splitted 0 in
  let int_string = String.slice callv_string 6 (String.length callv_string) in
  int_of_string int_string


let find_callv_greater_than_number (ap_set : A.t) (number : int) : A.elt =
  let callvs = A.elements @@ A.filter is_callv_ap ap_set in
  let greater_callvs =
    List.filter ~f:(fun callv -> Int.( > ) (extract_number_from_callv callv) number) callvs
  in
  let callvs_and_numbers =
    List.map greater_callvs ~f:(fun callv -> (callv, extract_number_from_callv callv))
  in
  let min_callv_opt =
    List.min_elt callvs_and_numbers ~compare:(fun (_, number1) (_, number2) ->
        Int.compare number1 number2)
  in
  match min_callv_opt with
  | None ->
      F.kasprintf
        (fun msg -> raise @@ FindCallvGreaterThanFailed msg)
        "find_callv_greater_than_number failed: ap_set: %a, number: %d@." A.pp ap_set number
  | Some (callv, _) ->
      callv
