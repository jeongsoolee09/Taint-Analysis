open! IStd
open DefLocAliasDomain
open DefLocAliasSearches
open DefLocAliasLogicTests

(** Interprocedural Liveness Checker with alias relations in mind. *)

exception NotImplemented
exception IDontKnow

module L = Logging
module F = Format
module Hashtbl = Caml.Hashtbl

module S = DefLocAliasDomain.AbstractStateSet
module A = DefLocAliasDomain.SetofAliases
module T = DefLocAliasDomain.AbstractState

module Payload = SummaryPayload.Make (struct
    type t = DefLocAliasDomain.t
    let field = Payloads.Fields.def_loc_alias
  end)


module TransferFunctions = struct
  module CFG = ProcCfg.OneInstrPerNode (ProcCfg.Exceptional)
  module InvariantMap = CFG.Node.IdMap
  module Domain = S
  type extras = ProcData.no_extras
  type instr = Sil.instr


  let add_to_history (key:Procname.t * MyAccessPath.t) (value:LocationSet.t) (history:HistoryMap.t) : HistoryMap.t = HistoryMap.add key value history


  let batch_add_to_history (keys:(Procname.t * MyAccessPath.t) list) (loc:LocationSet.t) (history:HistoryMap.t) : HistoryMap.t =
    let rec batch_add_to_history_inner (keys:(Procname.t * MyAccessPath.t) list) (loc:LocationSet.t) (current_map:HistoryMap.t) : HistoryMap.t = 
      match keys with
      | [] -> current_map
      | h::t -> batch_add_to_history_inner t loc (add_to_history h loc current_map) in
    batch_add_to_history_inner keys loc history


  (** find the most recent location of the given key in the map of a T.t *)
  let get_most_recent_loc (key:Procname.t * MyAccessPath.t) (history:HistoryMap.t) : LocationSet.t = HistoryMap.find key history


  let join_all_history_in (statelist:T.t list) : HistoryMap.t =
    let historylist = List.map ~f:(fun ({history}:T.t) -> history) statelist in
    List.fold_left ~f:(fun acc hist -> HistoryMap.join acc hist) ~init:HistoryMap.empty historylist


  (** specially mangled variable to mark a value as returned from callee *)
  let mk_returnv procname = Pvar.mk (Mangled.from_string "returnv") procname |> Var.of_pvar


  let rec extract_nonthisvar_from_args methname (arg_ts:(Exp.t*Typ.t) list) (astate_set:S.t) : Exp.t list =
    match arg_ts with
    | [] -> []
    | (Var var as v, _)::t ->
        let (_, _, _, aliasset) = search_target_tuple_by_id var methname astate_set in
        if not (A.exists is_this_ap aliasset)
        then v::extract_nonthisvar_from_args methname t astate_set
        else extract_nonthisvar_from_args methname t astate_set
    | (other, _)::t -> other::extract_nonthisvar_from_args methname t astate_set


  let leave_only_var_tuples (ziplist:(Exp.t*Var.t) list) =
    let leave_logical = fun (x,_) -> is_logical_var_expr x in
    let map_func = fun (exp, var) ->
      match exp, var with
      | Exp.Var id, var -> (Var.of_id id, var)
      | (_, _) -> L.die InternalError "leave_only_var_tuples/map_func failed, exp: %a, var: %a@." Exp.pp exp Var.pp var in
    List.filter ~f:leave_logical ziplist |> List.map ~f:map_func


(** id를 토대로 가장 최근의 non-ph 튜플을 찾아내고, 없으면 raise *)
let search_recent_vardef_astate (methname:Procname.t) (pvar:Var.t) (astate_set:S.t) : T.t =
  let elements = S.elements astate_set in
  let rec search_recent_vardef_astate_inner methname id astate_list =
    match astate_list with
    | [] -> L.die InternalError "search_recent_vardef_astate failed, methname: %a, pvar: %a, astate_set: %a@." Procname.pp methname Var.pp pvar S.pp astate_set
    | {T.tuple=targetTuple} as astate::t ->
        (* L.progress "methname: %a, searching: %a, loc: %a, proc: %a\n" Procname.pp methname Var.pp var Location.pp loc Procname.pp proc; *)
        let proc, (var, _), loc, aliasset = targetTuple in
        let proc_cond = Procname.equal proc methname in
        let id_cond = A.mem (id, []) aliasset in
        let var_cond = not @@ Var.equal var (placeholder_vardef proc) in
        if var_cond then 
        (let most_recent_loc = get_most_recent_loc (methname, (var, [])) astate.history in
        let loc_cond = LocationSet.equal most_recent_loc loc in
        if proc_cond && id_cond && loc_cond then
        astate else search_recent_vardef_astate_inner methname id t)
        else search_recent_vardef_astate_inner methname id t in
  search_recent_vardef_astate_inner methname pvar elements


  let pp_aliasset_list fmt (varsetlist:A.t list) =
    F.fprintf fmt "[";
    List.iter varsetlist ~f:(fun (aliasset:A.t) -> F.fprintf fmt "%a, " A.pp aliasset);
    F.fprintf fmt "]"


  (** given a doubleton set of lv and pv, extract the pv. *)
  let rec extract_another_pvar (id:Ident.t) (varsetlist:A.t list) : Var.t =
    match varsetlist with
    | [] -> L.die InternalError "extract_another_pvar failed, id: %a, varsetlist: %a@." Ident.pp id pp_aliasset_list varsetlist
    | set::t ->
        if Int.equal (A.cardinal set) 2 && A.mem (Var.of_id id, []) set
        then
          begin match set |> A.remove (Var.of_id id, []) |> A.elements with
            | [(x, _)] -> x
            | _ -> L.die InternalError "extract_another_pvar failed, id: %a, varsetlist: %a@." Ident.pp id pp_aliasset_list varsetlist end
        else extract_another_pvar id t


  let pp_bindinglist fmt (bindinglist:(Var.t * Var.t) list) =
    F.fprintf fmt "[";
    List.iter bindinglist ~f:(fun (a, f) -> F.fprintf fmt "(%a, %a)" Var.pp a Var.pp f);
    F.fprintf fmt "]"


  let pp_astatelist fmt (astatelist:T.t list) =
    F.fprintf fmt "[";
    List.iter astatelist ~f:(fun astate -> F.fprintf fmt "%a, " T.pp astate);
    F.fprintf fmt "]"


(** Takes an actual(logical)-formal binding list and adds the formals to the respective pvar tuples of the actual arguments *)
  let rec add_bindings_to_alias_of_tuples (methname:Procname.t) bindinglist (actual_astates:T.t list) =
    match bindinglist with
    | [] -> []
    | (actualvar, formalvar)::tl ->
        begin match actualvar with
        | Var.LogicalVar vl ->
            (* L.progress "Processing (%a, %a)\n" Var.pp actualvar Var.pp formalvar; *)
            (* L.progress "methname: %a, id: %a\n" Procname.pp methname Ident.pp vl; *)
            (* L.progress "Astate_set before death: @.%a@." S.pp (S.of_list actualtuples); *)
            let actual_pvar, _ = second_of @@ weak_search_target_tuple_by_id vl (S.of_list actual_astates) in
            (* possibly various definitions of the pvar in question. *)
            let candStates = 
            (* L.progress "methname: %a, var: %a\n" Procname.pp methname Var.pp actual_pvar;  *)
            search_target_astates_by_vardef actual_pvar methname (S.of_list actual_astates) in
            (* the most recent one among the definitions. *)
            let history = join_all_history_in candStates in
            let most_recent_loc = get_most_recent_loc (methname, (actual_pvar, [])) history in
            let {T.tuple=(proc,var,loc,aliasset')} as targetState = search_astate_by_loc most_recent_loc candStates in
            let newTuple = (proc, var, loc, A.add (formalvar, []) aliasset') in
            let newstate = {targetState with tuple=newTuple} in
            newstate::add_bindings_to_alias_of_tuples methname tl actual_astates
        | Var.ProgramVar _ -> L.die InternalError "add_bindings_to_alias_of_tuples failed, methname: %a, bindinglist: %a, actual_astates: %a@." Procname.pp methname pp_bindinglist bindinglist pp_astatelist actual_astates
        end


  let triple_equal = fun (proc1, var1, loc1) (proc2, var2, loc2) -> Procname.equal proc1 proc2 && Var.equal var1 var2 && LocationSet.equal loc1 loc2


  (** astate로부터 (procname, vardef) 쌍을 중복 없이 만든다. *)
  let get_keys astate_set =
    let elements = S.elements astate_set in
    let tuplelist = List.map ~f:(fun ({tuple}:T.t) -> tuple) elements in
    let rec enum_nodup (tuplelist:Q.t list) (current:(Procname.t*Var.t*LocationSet.t) list) =
      match tuplelist with
      | [] -> current
      | (a,(b, _),c,_)::t ->
        if not (List.mem current (a,b,c) ~equal:triple_equal) && not (Var.equal b (placeholder_vardef a) || Var.is_this b)
          then enum_nodup t ((a,b,c)::current)
          else enum_nodup t current in
    enum_nodup tuplelist []


  (** callee가 return c;꼴로 끝날 경우 새로 튜플을 만들고 alias set에 c를 추가 *)
  let variable_carryover astate_set callee_methname ret_id methname summ_read =
    let calleeTuples = find_tuple_with_ret summ_read callee_methname in
    (** 콜리 튜플 하나에 대해, 튜플 하나를 새로 만들어 alias set에 추가 *)
    let carryfunc tup =
      let ph = placeholder_vardef methname in
      let callee_vardef, _ = second_of tup in
      (* 여기서 returnv를 집어넣자 *)
      let aliasset = A.add (mk_returnv callee_methname, []) @@ doubleton (callee_vardef, []) (Var.of_id ret_id, []) in
      (* empty map이 맞을 지 모르겠네 *)
      {T.tuple=(methname, (ph, []), LocationSet.singleton Location.dummy, aliasset); history=HistoryMap.empty} in
    let carriedover = List.map calleeTuples ~f:carryfunc |> S.of_list in
    S.union astate_set carriedover


  (** 변수가 리턴된다면 그걸 alias set에 넣는다 (variable carryover) *)
  let apply_summary astate_set caller_summary callee_methname ret_id caller_methname : S.t =
    match Payload.read_full ~caller_summary:caller_summary ~callee_pname:callee_methname with
    | Some (_, summ) ->
        (*L.progress "Applying summary of %a\n" Procname.pp (Procdesc.get_proc_name pdesc);*)
        variable_carryover astate_set callee_methname ret_id caller_methname summ
    | None -> 
        (* Nothing to carry over! -> just make a ph tuple and end *)
        let ph = (placeholder_vardef caller_methname, []) in
        let loc = LocationSet.singleton Location.dummy in
        let alias = A.singleton (Var.of_id ret_id, []) in
        (* empty map이 맞을지 모르겠네 *)
        let newtuple = (caller_methname, ph, loc, alias) in
        let newstate = {T.tuple=newtuple; history=HistoryMap.empty} in
        S.add newstate astate_set


  let pp_explist fmt (explist:Exp.t list) =
    F.fprintf fmt "[";
    List.iter explist ~f:(fun exp -> F.fprintf fmt "%a, " Exp.pp exp);
    F.fprintf fmt "]"


  let pp_varlist fmt (varlist:Var.t list) =
    F.fprintf fmt "[";
    List.iter varlist ~f:(fun var -> F.fprintf fmt "%a, " Var.pp var);
    F.fprintf fmt "]"


  let rec zip (l1:Exp.t list) (l2:Var.t list) =
    match l1, l2 with
    | [], [] -> []
    | h1::t1, h2::t2 -> (h1, h2)::zip t1 t2
    | _, _ -> L.die InternalError "zip failed, l1: %a, l2: %a" pp_explist l1 pp_varlist l2


  let get_formal_args (caller_summary:Summary.t) (callee_methname:Procname.t) : Var.t list =
    match Payload.read_full ~caller_summary:caller_summary ~callee_pname:callee_methname with
    | Some (procdesc, _) -> Procdesc.get_formals procdesc |> List.map ~f:(convert_from_mangled callee_methname)
    | None -> (* Oops, it's a native code outside our focus *) []


  let put_fieldname (fieldname:Fieldname.t) (aliastup:A.elt) =
    let var, lst = aliastup in
    (var, lst @ [AccessPath.FieldAccess fieldname])


  let put_arrayaccess (aliastup:A.elt) =
    let var, lst = aliastup in
    (var, lst @ [AccessPath.ArrayAccess (Typ.void_star, [])])


  let merge_ph_tuples (tup1:QuadrupleWithPP.t) (tup2:QuadrupleWithPP.t) (lset:LocationSet.t) : Q.t =
    let proc1, _, _, alias1 = tup1 in
    let proc2, _, _, alias2 = tup2 in
    let pvar_vardef = find_another_pvar_vardef alias2 in
    if not @@ Procname.equal proc1 proc2 then L.die InternalError "merge_ph_tuples failed, tup1: %a, tup2: %a, location: %a" Q.pp tup1 Q.pp tup2 LocationSet.pp lset;
    let aliasset = A.add pvar_vardef @@ A.union alias1 alias2 in
    (proc1, pvar_vardef, lset, aliasset)


  let exec_store (exp1:Exp.t) (exp2:Exp.t) (methname:Procname.t) (astate_set:S.t) (node:CFG.Node.t) : S.t =
    match exp1, exp2 with
    | Lvar pv, Var id ->
        begin match Var.is_return (Var.of_pvar pv) with
        | true -> (* A variable is being returned *)
            let {T.tuple=(_, _, _, aliasset)} as targetState =
              try weak_search_target_astate_by_id id astate_set
              with _ ->
                  ((*L.progress "=== Search Failed (1): Astate before search_target_tuple at %a := %a === @.:%a@." Exp.pp exp1 Exp.pp exp2 S.pp astate ;*) botstate) in
            begin try
            let pvar_var, _ = A.find_first is_program_var_ap aliasset in
            let most_recent_loc = get_most_recent_loc (methname, (pvar_var, [])) targetState.history in
              let candStates = search_target_astates_by_vardef pvar_var methname astate_set in
              let {T.tuple=(proc,var,loc,aliasset'); history} as candState = search_astate_by_loc most_recent_loc candStates in
              let astate_rmvd = S.remove candState astate_set in
              let logicalvar = Var.of_id id in
              let programvar = Var.of_pvar pv in
              let newtuple = (proc,var,loc,A.union aliasset' (doubleton (logicalvar, []) (programvar, []))) in
              let newstate = {T.tuple=newtuple; history} in
              S.add newstate astate_rmvd
            with _ -> (* the pvar_var is not redefined in the procedure. *)
              S.remove targetState astate_set end
        | false -> (* An ordinary variable assignment. *)
            let targetState =
              begin try weak_search_target_astate_by_id id astate_set
              with _ -> ((* L.progress "id: %a" Ident.pp id ; L.progress "=== Search Failed (2): Astate before search_target_tuple at %a := %a === @.:%a@." Exp.pp exp1 Exp.pp exp2 S.pp astate ; *) botstate) end in
            let aliasset = fourth_of targetState.tuple in
            let pvar_var = Var.of_pvar pv in
            let loc = LocationSet.singleton @@ CFG.Node.loc node in
            let aliasset_new = A.add (pvar_var, []) aliasset in
            let newtuple = (methname, (pvar_var, []), loc, aliasset_new) in
            let astate_set_rmvd = S.remove targetState astate_set in
            let newmap = add_to_history (methname, (pvar_var, [])) loc targetState.history in
            let newstate = {T.tuple=newtuple; history=newmap} in
            if is_placeholder_vardef_ap (second_of targetState.tuple)
            then S.add newstate astate_set_rmvd
            else S.add newstate astate_set
        end
    | Lvar pv, Const _ when (Var.is_return (Var.of_pvar pv)) -> astate_set
    | Lvar pv, Const _ ->
        let pvar_var = Var.of_pvar pv in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let aliasset_new = A.singleton (pvar_var, []) in
        let newtuple = (methname, (pvar_var, []), loc, aliasset_new) in
        let newmap = add_to_history (methname, (pvar_var, [])) loc HistoryMap.empty in
        let newstate = {T.tuple=newtuple; history=newmap} in
        S.add newstate astate_set
    | Lvar pv, BinOp (_, Var id, Const _) | Lvar pv, BinOp (_, Const _, Var id) when is_mine id pv methname astate_set ->
        let {T.tuple=(procname, (vardef, _),  _, aliasset)} as targetState = search_target_astate_by_id id methname astate_set in
        let pvar_var = Var.of_pvar pv in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let aliasset_new = A.add (pvar_var, []) aliasset in
          if not (is_placeholder_vardef vardef)
          then let newtuple = (procname, (vardef, []), loc, aliasset_new) in
               let newmap = add_to_history (methname, (pvar_var, [])) loc targetState.history in
               let newstate = {T.tuple=newtuple; history=newmap} in
               S.add newstate astate_set
          else let newtuple = (procname, (vardef, []), loc, aliasset_new) in
               let astate_set_rmvd = S.remove targetState astate_set in
               let newmap = add_to_history (methname, (pvar_var, [])) loc targetState.history in
               let newstate = {T.tuple=newtuple; history=newmap} in
               S.add newstate astate_set_rmvd
    | Lvar pv, BinOp (_, Var _, Const _) | Lvar pv, BinOp (_, Const _, Var _) -> (* This id does not belong to pvar. *)
        let pvar_var = Var.of_pvar pv in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let aliasset_new = A.singleton (pvar_var, []) in
        let newtuple = (methname, (pvar_var, []), loc, aliasset_new) in
        let newmap = add_to_history (methname, (pvar_var, [])) loc HistoryMap.empty in
        let newstate = {T.tuple=newtuple; history=newmap} in
        (* L.progress "added pvar_var: %a\n" Var.pp pvar_var; *)
        S.add newstate astate_set
    | Lvar pv, BinOp (_, Var id1, Var id2) when not (is_mine id1 pv methname astate_set && is_mine id2 pv methname astate_set) ->
        let targetState1 = search_target_astate_by_id id1 methname astate_set in
        let targetState2 = search_target_astate_by_id id2 methname astate_set in
        let astate_rmvd = astate_set |> S.remove targetState1 |> S.remove targetState2 in
        let pvar_var = Var.of_pvar pv in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let aliasset_new = A.singleton (pvar_var, []) in
        let newtuple = (methname, (pvar_var, []), loc, aliasset_new) in
        let newmap = add_to_history (methname, (pvar_var, [])) loc HistoryMap.empty in 
        let newstate = {T.tuple=newtuple; history=newmap} in
        (* L.progress "added pvar_var: %a\n" Var.pp pvar_var; *)
        (* L.progress "current map: %a\n" (HistoryMap.pp ~pp_value:Location.pp) !history; *)
        S.add newstate astate_rmvd
    | Lvar pv, BinOp (_, Const _, Const _) ->
        let pvar_var = Var.of_pvar pv in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let aliasset_new = A.singleton (pvar_var, []) in
        let newtuple = (methname, (pvar_var, []), loc, aliasset_new) in
        let newmap = add_to_history (methname, (pvar_var, [])) loc HistoryMap.empty in 
        let newstate = {T.tuple=newtuple; history=newmap} in
        (* L.progress "added pvar_var: %a\n" Var.pp pvar_var; *)
        S.add newstate astate_set
    | Lfield (Var id1, fld, _), Var id2 ->
        (* finding the pvar tuple getting stored *)
        let {T.tuple=(proc1, var1, loc1, aliasset)} as varstate = search_target_astate_by_id id1 methname astate_set in
        let pvar_tuple : A.elt = begin try
            find_another_pvar_vardef aliasset
          with _ -> (* oops, long access path *)
            let varstate2 : T.t = search_target_astate_by_id id2 methname astate_set in
            let aliasset = fourth_of varstate2.tuple in
            find_another_pvar_vardef aliasset end in
        let pvar_tuple_updated = put_fieldname fld pvar_tuple in
        let new_aliasset = A.add pvar_tuple_updated @@ A.remove pvar_tuple aliasset in
        let newtuple = (proc1, var1, loc1, new_aliasset) in
        (* L.d_printfln "newtuple: %a@." QuadrupleWithPP.pp newtuple; *)
        (* finding the var tuple holding the value being stored *)
        (* L.d_printfln "finding: %a@." Ident.pp id2; *)
        let another_state = search_target_astate_by_id id2 methname astate_set in
        let another_tuple = another_state.tuple in
        (* L.d_printfln "another_tuple: %a@." QuadrupleWithPP.pp another_tuple; *)
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let merged_tuple = merge_ph_tuples another_tuple newtuple loc in
        (* L.progress "merged: %a@." QuadrupleWithPP.pp merged_tuple; *)
        let merged_history = HistoryMap.join varstate.history another_state.history in
        let astate_set_rmvd = S.remove another_state @@ S.remove varstate astate_set in
        let old_location = third_of newtuple in
        let new_history = add_to_history (methname, pvar_tuple_updated) loc merged_history in
        let new_state = {T.tuple=merged_tuple; history=new_history} in
        if LocationSet.equal old_location (LocationSet.singleton Location.dummy)
        then S.add new_state astate_set_rmvd
        else S.add varstate @@ S.add new_state astate_set_rmvd 
    | Lindex (Var id, _), Const _ -> (* covers both cases where offset is either const or id *)
        let {T.tuple=(proc, _, _, aliasset)} as targetState = search_target_astate_by_id id methname astate_set in
        let (var, aplist) as ap_containing_pvar = find_pvar_ap_in aliasset in
        let ap_containing_pvar_updated = (var, aplist @ [AccessPath.ArrayAccess (Typ.void_star, [])]) in
        let aliasset_rmvd = A.remove ap_containing_pvar aliasset in
        let new_aliasset = A.add ap_containing_pvar_updated aliasset_rmvd in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let newtuple = (proc, ap_containing_pvar_updated, loc, new_aliasset) in
        let astate_rmvd = S.remove targetState astate_set in
        let newmap = add_to_history (methname, ap_containing_pvar_updated) loc targetState.history in
        let newstate = {T.tuple=newtuple; T.history=newmap} in
        S.add newstate astate_rmvd
    | Lfield (Var id, fld, _), Const _ ->
        let {T.tuple=(proc, var, _, aliasset)} as targetState = search_target_astate_by_id id methname astate_set in
        let ap_containing_pvar : A.elt = find_pvar_ap_in aliasset in
        let ap_containing_pvar_updated = put_fieldname fld ap_containing_pvar in
        let aliasset_rmvd = A.remove ap_containing_pvar aliasset in
        let new_aliasset = A.add ap_containing_pvar_updated aliasset_rmvd in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let newtuple = (proc, ap_containing_pvar_updated, loc, new_aliasset) in
        let astate_set_rmvd = S.remove targetState astate_set in
        let newmap = add_to_history (methname, ap_containing_pvar_updated) loc targetState.history in
        let newstate = {T.tuple=newtuple; history=newmap} in
        if is_placeholder_vardef_ap var
        then S.add newstate astate_set_rmvd
        else S.add newstate astate_set
    | Lindex (Var id1, _), Var id2 ->
        (* finding the pvar tuple getting stored *)
        let {T.tuple=(proc1, var1, loc1, aliasset)} as varstate = search_target_astate_by_id id1 methname astate_set in
        let pvar_tuple : A.elt = begin try
            find_another_pvar_vardef aliasset
          with _ -> (* oops, long access path *)
            let varstate2 = search_target_tuple_by_id id2 methname astate_set in
            let aliasset = fourth_of varstate2 in
            find_another_pvar_vardef aliasset end in
        let pvar_tuple_updated = put_arrayaccess pvar_tuple in
        let new_aliasset = A.add pvar_tuple_updated @@ A.remove pvar_tuple aliasset in
        let newtuple = (proc1, var1, loc1, new_aliasset) in
        (* L.d_printfln "newtuple: %a@." QuadrupleWithPP.pp newtuple; *)
        (* finding the var tuple holding the value being stored *)
        let another_state = search_target_astate_by_id id2 methname astate_set in
        let another_tuple = another_state.tuple in
        (* L.d_printfln "another_tuple: %a@." QuadrupleWithPP.pp another_tuple; *)
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let merged_tuple = merge_ph_tuples another_tuple newtuple loc in
        (* L.progress "merged: %a@." QuadrupleWithPP.pp merged_tuple; *)
        let merged_history = HistoryMap.join varstate.history another_state.history in
        let astate_set_rmvd = S.remove another_state @@ S.remove varstate astate_set in
        let old_location = third_of newtuple in
        let new_history = add_to_history (methname, pvar_tuple_updated) loc merged_history in
        let new_state = {T.tuple=merged_tuple; history=new_history} in
        if LocationSet.equal old_location (LocationSet.singleton Location.dummy)
        then S.add new_state astate_set_rmvd
        else S.add varstate @@ S.add new_state astate_set_rmvd 
    | Lvar pvar, Exn _ when Var.is_return (Var.of_pvar pvar) -> 
        L.progress "Storing an Exception@."; astate_set
    | Lfield (Lvar pvar, fld, _), Const _ ->
        let pvar_ap = (Var.of_pvar pvar, [AccessPath.FieldAccess fld]) in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let aliasset_new = A.singleton pvar_ap in
        let newtuple = (methname, pvar_ap, loc, aliasset_new) in
        let newmap = add_to_history (methname, pvar_ap) loc HistoryMap.empty in
        let newstate = {T.tuple=newtuple; history=newmap} in
        S.add newstate astate_set
    | Lfield (Lvar pvar, fld, _), Var id ->
        let targetState =
          begin try weak_search_target_astate_by_id id astate_set
          with _ -> botstate end in
        let aliasset = fourth_of targetState.tuple in
        let pvar_var = Var.of_pvar pvar in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let new_pvar_ap = put_fieldname fld (pvar_var, []) in
        let aliasset_new = A.add new_pvar_ap aliasset in
        let newtuple = (methname, new_pvar_ap, loc, aliasset_new) in
        let astate_set_rmvd = S.remove targetState astate_set in
        let newmap = add_to_history (methname, new_pvar_ap) loc targetState.history in
        let newstate = {T.tuple=newtuple; history=newmap} in
        S.add newstate astate_set_rmvd
    | _, _ ->
        L.progress "Unsupported Store instruction %a := %a@." Exp.pp exp1 Exp.pp exp2; astate_set


  let exec_call (ret_id:Ident.t) (e_fun:Exp.t) (arg_ts:(Exp.t*Typ.t) list) (caller_summary:Summary.t) (astate_set:S.t) (methname:Procname.t) =
    let callee_methname =
      match e_fun with
      | Const (Cfun fn) -> fn
      | _ -> L.die InternalError "exec_call failed, ret_id: %a, e_fun: %a astate_set: %a, methname: %a" Ident.pp ret_id Exp.pp e_fun S.pp astate_set Procname.pp methname in
    match input_is_void_type arg_ts astate_set with
    | true -> (* All Arguments are Just Constants: just apply the summary, make a new tuple and end *)
        let astate_set_summary_applied = apply_summary astate_set caller_summary callee_methname ret_id methname in
        let aliasset = A.add (mk_returnv callee_methname, []) @@ A.singleton (Var.of_id ret_id, []) in
        let loc = LocationSet.singleton Location.dummy in
        let newtuple = (methname, (placeholder_vardef methname, []), loc, aliasset) in
        let newstate = {T.tuple=newtuple; history=HistoryMap.empty} in
        S.add newstate astate_set_summary_applied
    | false -> (* There is at least one argument which is a non-thisvar variable *)
        begin try
            let astate_set_summary_applied = apply_summary astate_set caller_summary callee_methname ret_id methname in
            let formals = get_formal_args caller_summary callee_methname |> List.filter ~f:(fun x -> not @@ Var.is_this x) in
            begin match formals with
              | [] -> (* Callee in Native Code! *)
                  astate_set_summary_applied
              | _ ->  (* Callee in User Code! *)
                  let actuals_logical = extract_nonthisvar_from_args methname arg_ts astate_set_summary_applied in
                  let actuallog_formal_binding = leave_only_var_tuples @@ zip actuals_logical formals in
                  (* pvar tuples transmitted as actual arguments *)
                  let mapfunc = fun exp ->
                    begin match exp with
                      | Exp.Var id ->
                          (* L.progress "id: %a, processing: %a@." Ident.pp id S.pp astate; *)
                          let pvar = search_target_tuples_by_id id methname astate_set |> List.map ~f:fourth_of |> extract_another_pvar id in (* 여기가 문제 *)
                          search_recent_vardef_astate methname pvar astate_set
                      | _ ->
                          L.die InternalError "exec_call/mapfunc failed, exp: %a" Exp.pp exp end in
                  let actuals_pvar_astates =
                    actuals_logical |> List.filter ~f:is_logical_var_expr |> List.map ~f:mapfunc in
                  let actualpvar_alias_added = add_bindings_to_alias_of_tuples methname actuallog_formal_binding actuals_pvar_astates |> S.of_list in
                  let applied_state_rmvd = S.diff astate_set_summary_applied (S.of_list actuals_pvar_astates) in
                  S.union applied_state_rmvd actualpvar_alias_added end
          with _ -> (* corner case: maybe one of actuals contains literal null *)
            astate_set end


  let exec_load (id:Ident.t) (exp:Exp.t) (astate_set:S.t) (methname:Procname.t) =
    let newmap = HistoryMap.empty in
    match exp with
    | Lvar pvar ->
        begin match is_formal pvar methname && not @@ Var.is_this (Var.of_pvar pvar) with
          | true ->
              let targetStates = search_target_astates_by_vardef (Var.of_pvar pvar) methname astate_set in
              let {T.tuple=(proc, var, loc, aliasset)} as targetState = find_least_linenumber targetStates in
              let newtuple = (proc, var, loc, A.add (Var.of_id id, []) aliasset) in
              let newstate = {T.tuple=newtuple; history=newmap} in
              let astate_rmvd = S.remove targetState astate_set in
              S.add newstate astate_rmvd
          | false ->
              begin match search_target_astates_by_vardef (Var.of_pvar pvar) methname astate_set with
                | [] -> (* 한 번도 def된 적 없음 *)
                    let double = doubleton (Var.of_id id, []) (Var.of_pvar pvar, []) in
                    let ph = placeholder_vardef methname in
                    let newtuple = (methname, (ph, []), LocationSet.singleton @@ Location.dummy, double) in
                    let newstate = {T.tuple=newtuple; history=newmap} in
                    S.add newstate astate_set
                | h::_ as astates -> (* 이전에 def된 적 있음 *)
                    let history = join_all_history_in astates in
                    let var, _ = second_of h.tuple in
                    (* L.d_printfln "finding var:%a\n" Var.pp var; *)
                    let most_recent_locset = get_most_recent_loc (methname, (var, [])) history in
                    (* L.d_printfln "methname: %a, most_recent_loc: %a@." Procname.pp methname Location.pp most_recent_loc; *)
                    (* L.progress "astate: %a@." S.pp astate; *)
                    let {T.tuple=(proc, vardef, loc, aliasset)} as most_recent_astate = search_astate_by_loc most_recent_locset astates in
                    let astate_set_rmvd = S.remove most_recent_astate astate_set in
                    let mra_updated = {most_recent_astate with tuple=(proc, vardef, loc, A.add (Var.of_id id, []) aliasset)} in
                    let double = doubleton (Var.of_id id, []) (Var.of_pvar pvar, []) in
                    let ph = placeholder_vardef methname in
                    let newstate = {T.tuple=(methname, (ph, []), LocationSet.singleton Location.dummy, double); history=HistoryMap.empty} in
                    S.add mra_updated astate_set_rmvd |> S.add newstate (* hopefully this fixes the 211 hashtbl issue *)
              end
        end
    | Lfield (Var var, fld, _) -> 
        let access_path : A.elt = (Var.of_id var, [FieldAccess fld]) in
        (* 이전에 정의된 적이 있는가 없는가로 경우 나눠야 함 (formal엔 못 옴) *)
        begin match search_target_tuples_by_vardef_ap (access_path) methname astate_set with
          | [] ->
              let ph = placeholder_vardef methname in
              let double = doubleton access_path (Var.of_id id, []) in
              let newstate = {T.tuple=(methname, (ph, []), LocationSet.singleton Location.dummy, double); history=newmap} in
              S.add newstate astate_set
          | _ -> L.die InternalError "exec_load failed, id: %a, exp: %a, astate_set: %a, methname: %a" Ident.pp id Exp.pp exp S.pp astate_set Procname.pp methname
        end
    | Lfield (Lvar pvar, fld, _) when Pvar.is_global pvar ->
        let access_path : A.elt = (Var.of_pvar pvar, [FieldAccess fld]) in
        (* 이전에 정의된 적이 있는가 없는가로 경우 나눠야 함 (formal엔 못 옴) *)
        begin match search_target_astates_by_vardef_ap access_path methname astate_set with
          | [] ->
              let ph = placeholder_vardef methname in
              let double = doubleton access_path (Var.of_id id, []) in
              let newstate = {T.tuple=(methname, (ph, []), LocationSet.singleton Location.dummy, double); history=newmap} in
              S.add newstate astate_set
          | h::_ as astates ->
              let var, fldlst = second_of h.tuple in
              let history = join_all_history_in (S.elements astate_set) in
              let most_recent_loc = get_most_recent_loc (methname, (var, fldlst)) history in
              let {T.tuple=(proc, vardef, loc, aliasset)} as most_recent_astate = search_astate_by_loc most_recent_loc astates in
              let astate_set_rmvd = S.remove most_recent_astate astate_set in
              let mra_updated = {most_recent_astate with tuple=(proc, vardef, loc, A.add (Var.of_id id, []) aliasset)} in
              let double = doubleton (Var.of_id id, []) (Var.of_pvar pvar, fldlst) in
              let ph = placeholder_vardef methname in
              let newstate = {T.tuple=(methname, (ph, []), LocationSet.singleton Location.dummy, double); history=newmap} in
              S.add mra_updated astate_set_rmvd |> S.add newstate end
    | Lindex (Var var, _) -> (* Var[const or Var] *)
        let access_path : A.elt = (Var.of_id var, [ArrayAccess (Typ.void_star, [])]) in
        (* 이전에 정의된 적이 있는가 없는가로 경우 나눠야 함 (formal엔 못 옴) *)
        begin match search_target_tuples_by_vardef_ap (access_path) methname astate_set with
          | [] ->
              let ph = placeholder_vardef methname in
              let double = doubleton access_path (Var.of_id id, []) in
              let newstate = {T.tuple=(methname, (ph, []), LocationSet.singleton Location.dummy, double); history=newmap} in
              S.add newstate astate_set
          | _ -> L.die InternalError "exec_load failed, id: %a, exp: %a, astate_set: %a, methname: %a" Ident.pp id Exp.pp exp S.pp astate_set Procname.pp methname end
    | Var _ -> (* 아직은 버리는 케이스만 있으니 e.g. _=*n$9 *)
        astate_set
    | _ ->
        L.progress "Unsupported Load Instruction %a := %a@." Ident.pp id Exp.pp exp; astate_set


  (** register tuples for formal arguments before a procedure starts. *)
  let register_formals astate_set cfg_node methname =
    let node = CFG.Node.underlying_node cfg_node in
    match Procdesc.Node.get_kind node with
    | Start_node ->
        let formals = get_my_formal_args methname in
        let formal_aps = List.map ~f:(fun var -> (var, [])) formals in 
        let proc = Procdesc.Node.get_proc_name node in
        let targetloc = Procdesc.Node.get_loc node in
        (* 파라미터 라인넘버 보정 *)
        let loc = LocationSet.singleton {Location.line=targetloc.line-1; Location.col=targetloc.col; Location.file=targetloc.file} in
        let bake_newstate = fun (var_ap:MyAccessPath.t) ->
          let newmap = add_to_history (methname, var_ap) loc HistoryMap.empty in
          let newtuple = (proc, var_ap, loc, A.singleton var_ap) in
          {T.tuple=newtuple; history=newmap} in
        let tuplelist = List.map ~f:bake_newstate formal_aps in
        let tupleset = S.of_list tuplelist in
        (* batch_add_to_history formal_aps loc ;*)
        S.union astate_set tupleset
    | _ -> astate_set


let rec catMaybes_tuplist (optlist:('a*'b option) list) : ('a*'b) list =
  match optlist with
  | [] -> []
  | (sth1, Some sth2) :: t -> (sth1, sth2)::catMaybes_tuplist t
  | (_, None)::_ -> L.die InternalError "catMaybes_tuplist failed"
  

(** 디스크에서 써머리를 읽어와서 해시테이블에 정리 *)
let load_summary_from_disk_to hashtbl =
  let all_source_files = SourceFiles.get_all ~filter:(fun _ -> true) () in
  let all_procnames_list = List.map ~f:SourceFiles.proc_names_of_source all_source_files in
  (* 아직은 파일이 하나밖에 없으니까 *)
  let all_procnames = List.concat all_procnames_list in
  let all_summaries_optlist = List.map ~f:(fun proc -> (proc, Summary.OnDisk.get proc)) all_procnames in
  let all_proc_and_summaries_opt = List.filter ~f:(fun (_, summ) -> match summ with Some _ -> true | None -> false) all_summaries_optlist in
  let all_proc_and_summaries = catMaybes_tuplist all_proc_and_summaries_opt in
  let all_proc_and_astate_sets_opt = List.map ~f:(fun (proc, summ) -> (proc, Payload.of_summary summ)) all_proc_and_summaries in
  let all_proc_and_astates = catMaybes_tuplist all_proc_and_astate_sets_opt in
  List.iter ~f:(fun (proc, astate) -> Hashtbl.add hashtbl proc astate) all_proc_and_astates


let exec_metadata (md:Sil.instr_metadata) (astate_set:S.t) =
  match md with
  | ExitScope _ -> (* S.filter (fun tup ->
       * not @@ Var.is_this @@ second_of tup &&
       * not @@ is_placeholder_vardef @@ second_of tup) *) astate_set
  | _ -> astate_set


  let exec_instr : S.t -> extras ProcData.t -> CFG.Node.t -> Sil.instr -> S.t = fun prev' {summary} node instr ->
    (* L.progress "Executing instr: %a\n" (Sil.pp_instr ~print_types:true Pp.text) instr; *)
    let my_summary = summary in
    let methname = node |> CFG.Node.underlying_node |> Procdesc.Node.get_proc_name in
    let prev = register_formals prev' node methname in
    (* let prev = prev' in *)
      match instr with
      | Load {id=id; e=exp} ->
          exec_load id exp prev methname
      | Store {e1=exp1; e2=exp2} ->
          exec_store exp1 exp2 methname prev node
      | Prune _ -> prev
      | Call ((ret_id, _), e_fun, arg_ts, _, _) ->
          exec_call ret_id e_fun arg_ts my_summary prev methname
      | Metadata md -> exec_metadata md prev


  let leq ~lhs:_ ~rhs:_ = S.subset


  (* to be evolved... *)
  let join = fun x y -> S.union x y


  let widen ~prev:prev ~next:next ~num_iters:_ = join prev next


  let pp_session_name node fmt = F.fprintf fmt "def/loc/alias %a" CFG.Node.pp_id (CFG.Node.id node)

end


module Analyzer = AbstractInterpreter.MakeRPO (TransferFunctions)

let checker {Callbacks.summary=summary; exe_env} : Summary.t =
  let proc_name = Summary.get_proc_name summary in
  let tenv = Exe_env.get_tenv exe_env proc_name in
  match Analyzer.compute_post (ProcData.make_default summary tenv) ~initial:DefLocAliasDomain.initial with
  | Some post ->
      Payload.update_summary post summary
  | None -> L.die InternalError "Checker Failed"
