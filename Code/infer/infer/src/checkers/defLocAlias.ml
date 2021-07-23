open! IStd
open DefLocAliasDomain
open DefLocAliasSearches
open DefLocAliasPredicates
open DefLocAliasPP

(** Interprocedural Liveness Checker with alias relations
    and redefinitions in mind. *)

exception NotImplemented
exception IDontKnow

module L = Logging
module F = Format
module Hashtbl = Caml.Hashtbl
module P = DefLocAliasDomain.AbstractPair
module S = DefLocAliasDomain.AbstractStateSetFinite
module A = DefLocAliasDomain.SetofAliases
module T = DefLocAliasDomain.AbstractState
module H = DefLocAliasDomain.HistoryMap
module AP = DefLocAliasDomain.MyAccessPath


module TransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  module InvariantMap = CFG.Node.IdMap
  module Domain = P
  type instr = Sil.instr

  type analysis_data = P.t InterproceduralAnalysis.t

  let choose_larger_location (locset1:LocationSet.t) (locset2:LocationSet.t) =
    let elem1 = LocationSet.min_elt locset1 in
    let elem2 = LocationSet.min_elt locset2 in
    match Location.compare elem1 elem2 with
    | -1 -> locset1
    | 0 -> if LocationSet.subset locset1 locset2 then locset1 else locset2
    | 1 -> locset2
    | _ -> L.die InternalError
             "choose_larger_location failed, locset1: %a, locset2: %a"
             LocationSet.pp locset1 LocationSet.pp locset2


  (** specially mangled variable to mark a value as returned from callee *)
  let mk_returnv procname =
    Var.of_pvar @@ Pvar.mk (Mangled.from_string @@ "returnv: "^(Procname.to_string procname)) procname


  (** specially mangled variable to mark an AP as passed to a callee *)
  let mk_callv procname =
    Var.of_pvar @@ Pvar.mk (Mangled.from_string @@ "callv: "^(Procname.to_string procname)) procname


  (** specially mangled variable to mark an AP as passed to a callee *)
  let mk_callv_pvar procname =
    Pvar.mk (Mangled.from_string @@ "callv: "^(Procname.to_string procname)) procname


  let rec extract_nonthisvar_from_args methname (arg_ts:(Exp.t*Typ.t) list)
      (astate_set:S.t) : Exp.t list =
    match arg_ts with
    | [] -> []
    | (Var var as v, _)::t ->
        let (_, _, _, aliasset) = search_target_tuple_by_id var methname astate_set in
        if not (A.exists is_this_ap aliasset)
        then v::extract_nonthisvar_from_args methname t astate_set
        else extract_nonthisvar_from_args methname t astate_set
    | (other, _)::t -> other::extract_nonthisvar_from_args methname t astate_set


  let leave_only_var_tuples (ziplist:(Var.t*Var.t) list) =
    let leave_logical = fun (x,_) -> is_logical_var x in
    let map_func = fun (var1, var2) ->
      match var1, var2 with
      | Var.LogicalVar id, var -> (Var.of_id id, var)
      | (_, _) -> L.die InternalError
                    "leave_only_var_tuples/map_func failed, exp: %a, var: %a@."
                    Var.pp var1 Var.pp var2 in
    List.filter ~f:leave_logical ziplist |> List.map ~f:map_func


  (** id를 토대로 가장 최근의 non-ph 튜플을 찾아내고, 없으면 raise *)
  let search_recent_vardef_astate (methname:Procname.t) (pvar:Var.t) (apair:P.t) : T.t =
    let elements = S.elements (fst apair) in
    let rec inner methname id astate_list =
      match astate_list with
      | [] -> L.die InternalError
                "search_recent_vardef_astate failed, methname: %a, pvar: %a, astate_set: %a@."
                Procname.pp methname Var.pp pvar P.pp apair
      | targetTuple::t ->
          let proc, (var, _), loc, aliasset = targetTuple in
          let proc_cond = Procname.equal proc methname in
          let id_cond = A.mem (id, []) aliasset in
          let var_cond = not @@ Var.equal var (placeholder_vardef proc) in
          if var_cond then
            let most_recent_loc = H.get_most_recent_loc (methname, (var, [])) (snd apair) in
            let loc_cond = LocationSet.equal most_recent_loc loc in
            begin if proc_cond && id_cond && loc_cond
              then targetTuple
              else inner methname id t end
          else inner methname id t in
    inner methname pvar elements


  (** given a doubleton set of lv and pv, extract the pv. *)
  let rec extract_another_pvar (id:Ident.t) (varsetlist:A.t list) : Var.t =
    match varsetlist with
    | [] -> L.die InternalError
              "extract_another_pvar failed, id: %a, varsetlist: %a@."
              Ident.pp id pp_aliasset_list varsetlist
    | set::t ->
        (* L.progress "sweeping set: %a@." A.pp set; *)
        if Int.equal (A.cardinal set) 2 && A.mem (Var.of_id id, []) set
        then
          begin match set
                      |> A.remove (Var.of_id id, [])
                      |> A.elements with
          | [(x, _)] -> x
          | _ -> L.die InternalError
                   "extract_another_pvar failed, id: %a, varsetlist: %a@."
                   Ident.pp id pp_aliasset_list varsetlist end
        else extract_another_pvar id t


  (** Takes an actual(logical)-formal binding list and adds the formals to the respective pvar tuples of the actual arguments *)
  let rec add_bindings_to_alias_of_tuples (methname:Procname.t) bindinglist
      (actual_astates:T.t list) (history:HistoryMap.t) =
    match bindinglist with
    | [] -> []
    | (actualvar, formalvar)::tl ->
        begin match actualvar with
          | Var.LogicalVar vl ->
              let actual_pvar, _ = second_of @@ weak_search_target_tuple_by_id vl (S.of_list actual_astates) in
              (* possibly various definitions of the pvar in question. *)
              let candTuples =
                search_target_tuples_by_vardef actual_pvar methname (S.of_list actual_astates) in
              (* the most recent one among the definitions. *)
              let most_recent_loc = H.get_most_recent_loc (methname, (actual_pvar, [])) history in
              let (proc,var,loc,aliasset') = search_astate_by_loc most_recent_loc candTuples in
              let newTuple = (proc, var, loc, A.add (formalvar, []) aliasset') in
              newTuple::add_bindings_to_alias_of_tuples methname tl actual_astates history
          | Var.ProgramVar _ -> L.die InternalError
                                  "add_bindings_to_alias_of_tuples failed, methname: %a, bindinglist: %a, actual_astates: %a@."
                                  Procname.pp methname pp_bindinglist bindinglist pp_astatelist actual_astates end


  (** callee가 return c;꼴로 끝날 경우 새로 튜플을 만들고 alias set에 c를 추가 *)
  let variable_carryover astate_set callee_methname ret_id methname summ_read =
    let calleeTuples = find_tuples_with_ret summ_read in
    (** 콜리 튜플 하나에 대해, 튜플 하나를 새로 만들어 alias set에 추가 *)
    let carryfunc (tup:T.t) =
      let ph = placeholder_vardef methname in
      let callee_vardef, _ = second_of tup in
      let aliasset =
        if Var.is_return callee_vardef
        then (* 'return' itself should not be considered a pvar that is carrried over *)
          A.add (mk_returnv callee_methname, []) @@ A.singleton (Var.of_id ret_id, [])
        else
          A.add (mk_returnv callee_methname, []) @@ doubleton (callee_vardef, []) (Var.of_id ret_id, []) in
      (methname, (ph, []), LocationSet.singleton Location.dummy, aliasset) in
    let carriedover = S.of_list @@ List.map calleeTuples ~f:carryfunc in
    S.union astate_set carriedover


  (** 변수가 리턴된다면 그걸 alias set에 넣는다 (variable carryover) *)
  let apply_summary astate_set callee_summary callee_methname ret_id caller_methname : S.t =
    variable_carryover astate_set callee_methname ret_id caller_methname (fst callee_summary)


  let rec my_zip (l1:Var.t list) (l2:Var.t list) =
    match l1, l2 with
    | [], [] -> []
    | h1::t1, h2::t2 -> (h1, h2)::my_zip t1 t2
    | _, _ -> L.die InternalError "my_zip failed, l1: %a, l2: %a" pp_varlist l1 pp_varlist l2


  (** (Var.t * Var.t) list에서 var이 들어 있는 튜플만을 삭제 *)
  let delete_vartuples (ziplist:(Var.t * Var.t) list) =
    List.fold ~f:(fun acc (v1, v2) ->
        if Var.is_this v1 || Var.is_this v2
        then acc
        else (v1, v2)::acc) ~init:[] ziplist


  let get_formal_args analyze_dependency (callee_methname:Procname.t) : Var.t list =
    match analyze_dependency callee_methname with
    | Some (procdesc, _) -> Procdesc.get_formals procdesc
                            |> List.map ~f:(convert_from_mangled callee_methname)
    | None -> (* Oops, it's a native code outside our focus *) []


  let put_fieldname (fieldname:Fieldname.t) (aliastup:A.elt) =
    let var, lst = aliastup in
    (var, lst @ [AccessPath.FieldAccess fieldname])


  let put_arrayaccess (aliastup:A.elt) =
    let var, lst = aliastup in
    (var, lst @ [AccessPath.ArrayAccess (Typ.void_star, [])])


  let merge_ph_tuples (tup1:T.t) (tup2:T.t) (lset:LocationSet.t) : T.t =
    let proc1, _, _, alias1 = tup1 in
    let proc2, _, _, alias2 = tup2 in
    let pvar_vardef = find_another_pvar_vardef alias2 in
    if not @@ Procname.equal proc1 proc2
    then L.die InternalError
        "merge_ph_tuples failed, tup1: %a, tup2: %a, location: %a"
        T.pp tup1 T.pp tup2 LocationSet.pp lset;
    let aliasset = A.add pvar_vardef @@ A.union alias1 alias2 in
    (proc1, pvar_vardef, lset, aliasset)


  let rec exec_store (exp1:Exp.t) (exp2:Exp.t) (methname:Procname.t) (apair:P.t) (node:CFG.Node.t) : P.t =
    match exp1, exp2 with
    | Lvar pv, Var id ->
        begin match Var.is_return (Var.of_pvar pv) with
          | true -> (* A variable is being returned *)
              let (_, _, _, aliasset) as targetTuple =
                try weak_search_target_tuple_by_id id (fst apair)
                with _ -> bottuple in
              begin try (* 가장 최근의 pvar를 찾아서 alias set에 return을 집어넣어 준다. *)
                  let pvar_var, _ = A.find_first is_program_var_ap aliasset in
                  let most_recent_loc = H.get_most_recent_loc (methname, (pvar_var, [])) (snd apair) in
                  let candStates = search_target_tuples_by_vardef pvar_var methname (fst apair) in
                  let (proc,var,loc,aliasset') as candState = search_astate_by_loc most_recent_loc candStates in
                  let astate_rmvd = S.remove candState (fst apair) in
                  let logicalvar = Var.of_id id in
                  let returnvar = Var.of_pvar pv in
                  let newtuple = (proc,var,loc,A.union aliasset' (doubleton (logicalvar, []) (returnvar, []))) in
                  let newset = S.add newtuple astate_rmvd in
                  (newset, snd apair)
                with _ -> (* the pvar_var is not redefined in the procedure. *)
                  let (proc, var, loc, aliasset') as candState = search_target_tuple_by_id id methname (fst apair) in
                  let astate_rmvd = S.remove candState (fst apair) in
                  let logicalvar = Var.of_id id in
                  let returnvar = Var.of_pvar pv in
                  let newtuple = (proc, var, loc, A.union aliasset' (doubleton (logicalvar, []) (returnvar, []))) in
                  let newset = S.add newtuple astate_rmvd in
                  (newset, snd apair) end
          | false -> (* An ordinary variable assignment. *)
              let targetTuple =
                try weak_search_target_tuple_by_id id (fst apair)
                with _ -> bottuple in
              let aliasset = fourth_of targetTuple in
              let pvar_var = Var.of_pvar pv in
              let loc = LocationSet.singleton @@ CFG.Node.loc node in
              let aliasset_new = A.add (pvar_var, []) aliasset in
              let newtuple = (methname, (pvar_var, []), loc, aliasset_new) in
              let astate_set_rmvd = S.remove targetTuple (fst apair) in
              let newmap = H.add_to_history (methname, (pvar_var, [])) loc (snd apair) in
              if is_placeholder_vardef_ap (second_of targetTuple)
              then
                let newset = S.add newtuple astate_set_rmvd in
                (newset, newmap)
              else
                let newset = S.add newtuple (fst apair) in
                (newset, newmap) end
    | Lvar pv, Const _ when (Var.is_return (Var.of_pvar pv)) -> apair
    | Lvar pv, Const _ ->
        let pvar_var = Var.of_pvar pv in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let aliasset_new = A.singleton (pvar_var, []) in
        let newtuple = (methname, (pvar_var, []), loc, aliasset_new) in
        let newmap = H.add_to_history (methname, (pvar_var, [])) loc (snd apair) in
        let newset = S.add newtuple (fst apair) in
        (newset, newmap)
    | Lvar pv, BinOp (_, Var id, Const _) | Lvar pv, BinOp (_, Const _, Var id) when is_mine id pv methname apair -> (* e.g. a = a + 1 *)
        let (procname, (vardef, _),  _, aliasset) as targetTuple = search_target_tuple_by_id id methname (fst apair) in
        let pvar_var = Var.of_pvar pv in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let aliasset_new = A.add (pvar_var, []) aliasset in
        if not @@ is_placeholder_vardef vardef
        then
          let newtuple = (procname, (vardef, []), loc, aliasset_new) in
          let newmap = H.add_to_history (methname, (pvar_var, [])) loc (snd apair) in
          let newset = S.add newtuple (fst apair) in
          (newset, newmap)
        else
          let newtuple = (procname, (vardef, []), loc, aliasset_new) in
          let astate_set_rmvd = S.remove targetTuple (fst apair) in
          let newmap = H.add_to_history (methname, (pvar_var, [])) loc (snd apair) in
          let newset = S.add newtuple astate_set_rmvd in
          (newset, newmap)
    | Lvar pv, BinOp (_, Var _, Const _) | Lvar pv, BinOp (_, Const _, Var _) -> (* This id does not belong to pvar. *)
        let pvar_var = Var.of_pvar pv in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let aliasset_new = A.singleton (pvar_var, []) in
        let newtuple = (methname, (pvar_var, []), loc, aliasset_new) in
        let newmap = H.add_to_history (methname, (pvar_var, [])) loc (snd apair) in
        let newset = S.add newtuple (fst apair) in
        (newset, newmap)
    | Lvar pv, BinOp (_, Var id1, Var id2) when not @@ is_mine id1 pv methname apair && is_mine id2 pv methname apair ->
        let targetState1 = search_target_tuple_by_id id1 methname (fst apair) in
        let targetState2 = search_target_tuple_by_id id2 methname (fst apair) in
        let astate_rmvd = (fst apair)
                          |> S.remove targetState1
                          |> S.remove targetState2 in
        let pvar_var = Var.of_pvar pv in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let aliasset_new = A.singleton (pvar_var, []) in
        let newtuple = (methname, (pvar_var, []), loc, aliasset_new) in
        let newmap = H.add_to_history (methname, (pvar_var, [])) loc (snd apair) in 
        let newset = S.add newtuple astate_rmvd in
        (newset, newmap)
    | Lvar pv, BinOp (_, Const _, Const _) ->
        let pvar_var = Var.of_pvar pv in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let aliasset_new = A.singleton (pvar_var, []) in
        let newtuple = (methname, (pvar_var, []), loc, aliasset_new) in
        let newmap = H.add_to_history (methname, (pvar_var, [])) loc (snd apair) in 
        let newset = S.add newtuple (fst apair) in
        (newset, newmap)
    | Lfield (Var id1, fld, _), Var id2 ->
        (* finding the pvar tuple (lhs) getting stored *)
        begin try  (* normal cases where x = new(); then x.f = ... . *)
            let (proc1, var1, loc1, aliasset) as vartuple = search_target_tuple_by_id id1 methname (fst apair) in
            let pvar_tuple : A.elt = begin try
                find_another_pvar_vardef aliasset
              with _ -> (* oops, long access path *)
                let intermed_tuple = search_target_tuple_by_id id1 methname (fst apair) in
                let intermed_aliasset = fourth_of intermed_tuple in
                let (var, aplist) = find_ap_with_field intermed_aliasset in
                begin match var with
                  | LogicalVar lv ->
                      let var_tuple = search_target_tuple_by_id lv methname (fst apair) in
                      let (pvar, _) = find_pvar_ap_in @@ fourth_of var_tuple in
                      (pvar, aplist)
                  | ProgramVar _ ->
                      L.die InternalError "Not a logical var! var: %a@." Var.pp var end end in
            let pvar_tuple_updated = put_fieldname fld pvar_tuple in
            let new_aliasset = A.add pvar_tuple_updated @@ A.remove pvar_tuple aliasset in
            let newtuple = (proc1, var1, loc1, new_aliasset) in
            (* finding the var tuple holding the value being stored *)
            let another_tuple = search_target_tuple_by_id id2 methname (fst apair) in
            let loc = LocationSet.singleton @@ CFG.Node.loc node in
            let merged_tuple = merge_ph_tuples another_tuple newtuple loc in
            let astate_set_rmvd = S.remove another_tuple @@ S.remove vartuple (fst apair) in
            let old_location = third_of newtuple in
            let new_history = H.add_to_history (methname, pvar_tuple_updated) loc (snd apair) in
            if LocationSet.equal old_location (LocationSet.singleton Location.dummy)
            then
              let newset = S.add merged_tuple astate_set_rmvd in
              (newset, new_history)
            else
              let newset = S.add another_tuple @@  S.add vartuple @@ S.add merged_tuple astate_set_rmvd in
              (newset, new_history)
          with _ -> (* abnormal cases where n$2 = new() and n$2 is not owned by any pvars *)
            (* create a new ph tuple! *)
            let ph = placeholder_vardef methname in
            let loc = LocationSet.singleton Location.dummy in
            let aliasset = doubleton (Var.of_id id1, [AccessPath.FieldAccess fld]) (Var.of_id id2, []) in
            let newset = S.add (methname, (ph, []), loc, aliasset) (fst apair) in
            (newset, snd apair) end
    | Lindex (Var id, _), Const _ -> (* covers both cases where offset is either const or id *)
        let (proc, _, _, aliasset) as targetTuple = search_target_tuple_by_id id methname (fst apair) in
        let (var, aplist) as ap_containing_pvar = find_pvar_ap_in aliasset in
        let ap_containing_pvar_updated = (var, aplist @ [AccessPath.ArrayAccess (Typ.void_star, [])]) in
        let aliasset_rmvd = A.remove ap_containing_pvar aliasset in
        let new_aliasset = A.add ap_containing_pvar_updated aliasset_rmvd in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let newtuple = (proc, ap_containing_pvar_updated, loc, new_aliasset) in
        let astate_rmvd = S.remove targetTuple (fst apair) in
        let newmap = H.add_to_history (methname, ap_containing_pvar_updated) loc (snd apair) in
        let newset = S.add newtuple astate_rmvd in
        (newset, newmap)
    | Lfield (Var id, fld, _), Const _ ->
        let (proc, var, _, aliasset) as targetState = search_target_tuple_by_id id methname (fst apair) in
        let ap_containing_pvar : A.elt = find_pvar_ap_in aliasset in
        let ap_containing_pvar_updated = put_fieldname fld ap_containing_pvar in
        let aliasset_rmvd = A.remove ap_containing_pvar aliasset in
        let new_aliasset = A.add ap_containing_pvar_updated aliasset_rmvd in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let newtuple = (proc, ap_containing_pvar_updated, loc, new_aliasset) in
        let astate_set_rmvd = S.remove targetState (fst apair) in
        let newmap = H.add_to_history (methname, ap_containing_pvar_updated) loc (snd apair) in
        if is_placeholder_vardef_ap var
        then
          let newset = S.add newtuple astate_set_rmvd in
          (newset, newmap)
        else
          let newset = S.add newtuple (fst apair) in
          (newset, newmap)
    | Lindex (Var id1, _), Var id2 ->
        (* finding the pvar tuple getting stored *)
        let (proc1, var1, loc1, aliasset) as vartuple =
          search_target_tuple_by_id id1 methname (fst apair) in
        let pvar_tuple : A.elt = begin try
            find_another_pvar_vardef aliasset (* ph를 찾으라고 할 수는 없으니까 *)
          with _ -> (* oops, long access path *)
            let varstate2 = search_target_tuple_by_id id2 methname (fst apair) in
            let aliasset = fourth_of varstate2 in
            find_another_pvar_vardef aliasset end in
        let pvar_tuple_updated = put_arrayaccess pvar_tuple in
        let new_aliasset = A.add pvar_tuple_updated @@ A.remove pvar_tuple aliasset in
        let newtuple = (proc1, var1, loc1, new_aliasset) in
        (* finding the var tuple holding the value being stored *)
        let another_tuple = search_target_tuple_by_id id2 methname (fst apair) in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let merged_tuple = merge_ph_tuples another_tuple newtuple loc in
        (* let astate_set_rmvd = S.remove another_tuple @@ S.remove vartuple (fst apair) in *)
        let old_location = third_of newtuple in
        let new_history = H.add_to_history (methname, pvar_tuple_updated) loc (snd apair) in
        if LocationSet.equal old_location (LocationSet.singleton Location.dummy)
        then
          let newset = S.add merged_tuple (* astate_set_rmvd *) (fst apair) in
          (newset, new_history)
        else
          let newset = S.add another_tuple @@ S.add vartuple @@ S.add merged_tuple (* astate_set_rmvd *) (fst apair) in
          (newset, new_history)
    | Lvar pvar, Exn _ when Var.is_return (Var.of_pvar pvar) ->
        apair
    | Lfield (Lvar pvar, fld, _), Const _ ->
        let pvar_ap = (Var.of_pvar pvar, [AccessPath.FieldAccess fld]) in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let aliasset_new = A.singleton pvar_ap in
        let newtuple = (methname, pvar_ap, loc, aliasset_new) in
        let newmap = H.add_to_history (methname, pvar_ap) loc (snd apair) in
        let newset = S.add newtuple (fst apair) in
        (newset, newmap)
    | Lfield (Lvar pvar, fld, _), Var id ->
        let targetTuple =
          try weak_search_target_tuple_by_id id (fst apair)
          with _ -> bottuple in
        let aliasset = fourth_of targetTuple in
        let pvar_var = Var.of_pvar pvar in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let new_pvar_ap = put_fieldname fld (pvar_var, []) in
        let aliasset_new = A.add new_pvar_ap aliasset in
        let newtuple = (methname, new_pvar_ap, loc, aliasset_new) in
        let astate_set_rmvd = S.remove targetTuple (fst apair) in
        let newmap = H.add_to_history (methname, new_pvar_ap) loc (snd apair) in
        let newset = S.add newtuple astate_set_rmvd in
        (newset, newmap)
    | lhs, Cast (_, exp) -> (* we ignore the cast *)
        exec_store lhs exp methname apair node
    | Lvar pv, BinOp (_, _, _) -> (* nested arithmetic expressions, lhs is pvar *)
        let pvar_var = Var.of_pvar pv in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let aliasset_new = A.singleton (Var.of_pvar pv, []) in
        let newtuple = (methname, (pvar_var, []), loc, aliasset_new) in
        let newmap = H.add_to_history (methname, (pvar_var, [])) loc (snd apair) in
        let newset = S.add newtuple (fst apair) in
        (newset, newmap)
    | Lfield (Lvar pv, fld, _), BinOp (_, _, _) -> (* arbitrarily nested (depth>=0) arithmetic expressions,
                                                      lhs is field access with a pvar base *)
        let pvar_ap = (Var.of_pvar pv, [AccessPath.FieldAccess fld]) in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let aliasset_new = A.singleton (Var.of_pvar pv, []) in
        let newtuple = (methname, pvar_ap, loc, aliasset_new) in
        let newmap = H.add_to_history (methname, pvar_ap) loc (snd apair) in
        let newset = S.add newtuple (fst apair) in
        (newset, newmap)
    | Lfield (Var var, fld, _), BinOp (_, _, _) -> (* arbitrarily nested (depth>=0) arithmetic expressions,
                                                      lhs is field access with a var base *)
        let pvar_var, _ = second_of @@ search_target_tuple_by_id var methname (fst apair) in
        let pvar_ap = (pvar_var, [AccessPath.FieldAccess fld]) in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let aliasset_new = A.singleton (pvar_var, []) in
        let newtuple : T.t = (methname, pvar_ap, loc, aliasset_new) in
        let newmap = H.add_to_history (methname, pvar_ap) loc (snd apair) in
        let newset = S.add newtuple (fst apair) in
        (newset, newmap)
    | Lindex (Var var, _), BinOp (_, _, _) -> (* arbitrarily nested (depth>=0) arithmetic expressions,
                                                 lhs is field access with a var base *)
        let pvar_var, _ = second_of @@ search_target_tuple_by_id var methname (fst apair) in
        let pvar_ap = (pvar_var, [AccessPath.ArrayAccess (Typ.void_star, [])]) in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let aliasset_new = A.singleton (pvar_var, []) in
        let newtuple : T.t = (methname, pvar_ap, loc, aliasset_new) in
        let newmap = H.add_to_history (methname, pvar_ap) loc (snd apair) in
        let newset = S.add newtuple (fst apair) in
        (newset, newmap)
    | _, _ ->
        L.progress "Unsupported Store instruction %a := %a at %a@."
          Exp.pp exp1 Exp.pp exp2 Procname.pp methname; apair


  let cdr (lst:'a list) =
    match lst with
    | [] -> L.die InternalError "cdr of an empty list is undefined"
    | _::t -> t


  (** exp를 받아서 logical var로 변환한다. *)
  let convert_exp_to_logical (exp:Exp.t) =
    match exp with
    | Var id -> id
    | _ -> Ident.create_none () (* create a dummy *)


  let exec_call (ret_id:Ident.t) (callee_methname:Procname.t) (arg_ts:(Exp.t*Typ.t) list)
      analyze_dependency (apair:P.t) (methname:Procname.t) : P.t =
    let open List in
    match analyze_dependency callee_methname with
    | Some (_, callee_summary) ->
        begin match input_is_void_type arg_ts (fst apair) with
          | true -> (* All Arguments are Just Constants: just apply the summary, make a new tuple and end *)
            let astate_set_summary_applied =
              apply_summary (fst apair) callee_summary callee_methname ret_id methname in
              let aliasset = A.add (mk_returnv callee_methname, []) @@ A.singleton (Var.of_id ret_id, []) in
              let loc = LocationSet.singleton Location.dummy in
              let newtuple = (methname, (placeholder_vardef methname, []), loc, aliasset) in
              let newset = S.add newtuple astate_set_summary_applied in
              (newset, (snd apair))
          | false -> (* There is at least one argument which is a non-thisvar variable *)
              begin try
                  let astate_set_summary_applied =
                    apply_summary (fst apair) callee_summary callee_methname ret_id methname in
                  let formals = get_formal_args analyze_dependency callee_methname in
                  begin match formals with
                    | [] -> (* Callee in Native Code! *)
                        let actuals_logical = arg_ts >>| (fst >> convert_exp_to_logical) >>| Var.of_id in
                        let mapfunc = fun (var:Var.t) ->
                          begin match var with
                            | LogicalVar id ->
                                let pvar1 = search_target_tuples_by_id id methname (fst apair) in
                                let pvar2 = map ~f:fourth_of pvar1 in
                                let pvar = extract_another_pvar id pvar2 in
                                search_recent_vardef_astate methname pvar apair
                            | _ ->
                                L.die InternalError "exec_call/mapfunc failed, var: %a" Var.pp var end in
                        let actuals_pvar_tuples = actuals_logical
                                                  |> filter ~f:is_logical_var
                                                  |> map ~f:mapfunc in
                        let mangled_callv = (mk_callv methname, []) in
                        let astate_set_callv_added =
                          S.map (fun (p, v, l, a) ->
                              let aliasset_callv_added = A.add mangled_callv a in
                              (p, v, l, aliasset_callv_added)) (S.of_list actuals_pvar_tuples) in
                        let astate_set_rmvd =
                          S.diff astate_set_summary_applied (S.of_list actuals_pvar_tuples) in
                        let astate_set_callv_added = S.union astate_set_rmvd astate_set_callv_added in
                        (astate_set_callv_added, snd apair)
                    | _ ->  (* Callee in User Code! *)
                        let actuals_logical = arg_ts >>| (fst >> convert_exp_to_logical) >>| Var.of_id in
                        let actuallog_formal_binding =
                          leave_only_var_tuples @@ my_zip actuals_logical formals in
                        (* mapfunc finds pvar tuples transmitted as actual arguments *)
                        let mapfunc = fun (var:Var.t) ->
                          begin match var with
                            | LogicalVar id ->
                                let pvar = search_target_tuples_by_id id methname (fst apair)
                                           |> map ~f:fourth_of
                                           |> extract_another_pvar id in
                                search_recent_vardef_astate methname pvar apair
                            | _ ->
                                L.die InternalError "exec_call/mapfunc failed, var: %a" Var.pp var end in
                        let actuals_pvar_tuples = actuals_logical
                                                  |> filter ~f:is_logical_var
                                                  |> map ~f:mapfunc in
                        let actualpvar_alias_added =
                          add_bindings_to_alias_of_tuples methname actuallog_formal_binding
                            actuals_pvar_tuples (snd apair)
                          |> S.of_list in
                        let mangled_callv = (mk_callv methname, []) in
                        let actualpvar_callv_added =
                          S.map (fun (p, v, l, a) ->
                              let aliasset_callv_added = A.add mangled_callv a in
                              (p, v, l, aliasset_callv_added)) actualpvar_alias_added in
                        if Int.equal (S.cardinal actualpvar_callv_added) 0
                        then (* void function call! *)
                          (astate_set_summary_applied, snd apair)
                        else
                          let applied_state_rmvd =
                            S.diff astate_set_summary_applied (S.of_list actuals_pvar_tuples) in
                          let newset = S.union applied_state_rmvd actualpvar_callv_added in
                          (newset, snd apair) end
                with _ -> (* corner case: maybe one of actuals contains literal null? *)
                  apair end end
    | None ->
        (* Nothing to carry over! -> just make a ph tuple and end *)
        let astate_set, historymap = apair in
        let ph = (placeholder_vardef methname, []) in
        let returnv = mk_returnv callee_methname in
        let loc = LocationSet.singleton Location.dummy in
        let aliasset = doubleton (Var.of_id ret_id, []) (returnv, []) in
        let newtuple = (methname, ph, loc, aliasset) in
        let newstate = newtuple in
        (S.add newstate astate_set, historymap)


  let batch_alias_assoc (astate_set:S.t) (logicals:Ident.t list)
      (pvars:Pvar.t list) : S.t =
    let (>>|) = List.(>>|) in
    let logicals_and_pvars = my_zip (logicals >>| Var.of_id) (pvars >>| Var.of_pvar) in
    let assoc_with_own_astate id =
      (id, weak_search_target_tuple_by_id id astate_set) in
    let id_and_astate = logicals >>| assoc_with_own_astate in
    let astate_tuples_to_remove = S.of_list @@ (id_and_astate >>| snd) in
    let astate_set_rmvd = S.diff astate_set astate_tuples_to_remove in
    let update_astate (id, astate) =
      let pvar =
        List.Assoc.find_exn logicals_and_pvars (Var.of_id id) ~equal:Var.equal in
      let proc, vardef, loc, aliasset = astate in
      let aliasset' = A.add (pvar, []) aliasset in
      (proc, vardef, loc, aliasset') in
    let updated_astates_set = S.of_list @@ (id_and_astate >>| update_astate) in
    S.union astate_set_rmvd updated_astates_set


  (** Handles calls to library APIs, whose Procdesc.t is empty *)
  let exec_lib_call (ret_id:Ident.t) (callee_methname:Procname.t) (arg_ts:(Exp.t*Typ.t) list)
      analyze_dependency (apair:P.t) (caller_methname:Procname.t) (node:CFG.Node.t) : P.t =
    let astate_set, histmap = apair in
    (* 1. Mangle some parameters.
       formal parameter naming schema:
            param_{callee_name_simple}_{line}_{param_index} *)
    let open Core_kernel.List in
    let callee_name_simple = Procname.get_method callee_methname in
    let loc = Int.to_string @@ (CFG.Node.loc node).line in
    let param_indices = List.init (List.length arg_ts) ~f:Int.to_string in
    let mangles : Mangled.t list =
      param_indices >>| (fun param_index ->
          Mangled.from_string @@ "param_" ^ callee_name_simple ^ "_" ^ loc ^ "_" ^ param_index) in
    let mangled_params : Pvar.t list =
      List.map ~f:(fun mangle ->
          Pvar.mk mangle callee_methname) mangles in
    (* 1-1. Associate mangled parameters and their resp. actual arguments as aliases. *)
    let actuals_logical = arg_ts >>| (fst >> convert_exp_to_logical) in
    let callvs = List.init (List.length actuals_logical)
        ~f:(fun _ -> mk_callv_pvar caller_methname) in
    let astate_set' = batch_alias_assoc astate_set actuals_logical mangled_params
                      |> (fun astate_set ->
                          batch_alias_assoc astate_set actuals_logical callvs) in

    (* 2-1. Associate ret_id and formal return variable as aliases. *)
    (* We need to create a new astate (ph tuple) here *)
    let returnv = mk_returnv callee_methname in
    let new_aliasset = A.of_list [ (Var.of_id ret_id, []); (returnv, []) ] in
    let ph = (placeholder_vardef caller_methname, []) in
    let newtuple = (caller_methname, ph, LocationSet.singleton Location.dummy, new_aliasset) in
    (S.add newtuple astate_set', histmap)


  (** Procname.Java.t를 포장한 Procname.t에서 해당 Procname.Java.t를 추출한다. *)
  let extract_java_procname (methname:Procname.t) : Procname.Java.t =
    match methname with
    | Java procname -> procname
    | _ -> L.die InternalError
             "extract_java_procname failed, methname: %a (maybe you ran this analysis on a non-Java project?)@."
             Procname.pp methname


  let exec_load (id:Ident.t) (exp:Exp.t) (apair:P.t) (methname:Procname.t) : P.t =
    let java_procname = extract_java_procname methname in
    match exp with
    | Lvar pvar ->
        begin match is_formal pvar methname && not @@ Var.is_this (Var.of_pvar pvar) with
          | true when Procname.Java.is_autogen_method java_procname ->
              (* 그냥 ph 튜플 하나 만들고 말자 *)
              let ph = (placeholder_vardef methname, []) in
              let aliasset = doubleton (Var.of_id id, []) (Var.of_pvar pvar, []) in
              let loc = LocationSet.singleton Location.dummy in
              let newtuple = (methname, ph, loc, aliasset) in
              let newset = S.add newtuple (fst apair) in
              (newset, snd apair)
          | true ->
              let targetTuples = search_target_tuples_by_vardef (Var.of_pvar pvar) methname (fst apair) in
              let (proc, var, loc, aliasset) as targetTuple = find_most_linenumber targetTuples in
              let newtuple = (proc, var, loc, A.add (Var.of_id id, []) aliasset) in
              let newstate = newtuple in
              let astate_rmvd = S.remove targetTuple (fst apair) in
              let newset = S.add newstate astate_rmvd in
              (newset, snd apair)
          | false ->
              begin match search_target_tuples_by_vardef (Var.of_pvar pvar) methname (fst apair) with
                | [] -> (* 한 번도 def된 적 없음 *)
                    let double = doubleton (Var.of_id id, []) (Var.of_pvar pvar, []) in
                    let ph = placeholder_vardef methname in
                    let newtuple = (methname, (ph, []), LocationSet.singleton @@ Location.dummy, double) in
                    let newstate = newtuple in
                    let newset = S.add newstate (fst apair) in
                    (newset, snd apair)
                | h::_ as tuples -> (* 이전에 def된 적 있음 *)
                    let vardef_tup = second_of h in
                    let most_recent_locset = H.get_most_recent_loc (methname, vardef_tup) (snd apair) in
                    let (proc, vardef, loc, aliasset) as most_recent_tuple =
                      begin try
                          search_tuple_by_loc most_recent_locset tuples
                        with _ -> (* to handle very weird corner cases
                                     where Infer is analyzing a SKIP_FUNCTION *)
                          search_tuple_by_loc most_recent_locset (S.elements (fst apair)) end in
                    let astate_set_rmvd = S.remove most_recent_tuple (fst apair) in
                    let mrt_updated = (proc, vardef, loc, A.add (Var.of_id id, []) aliasset) in
                    let double = doubleton (Var.of_id id, []) (Var.of_pvar pvar, []) in
                    let ph = placeholder_vardef methname in
                    let newstate = (methname, (ph, []), LocationSet.singleton Location.dummy, double) in
                    let newset = S.add mrt_updated astate_set_rmvd |> S.add newstate in
                    (newset, snd apair) end end
    | Lfield (Var var, fld, _) ->
        let base_pvar = fst @@ second_of @@ search_target_tuple_by_id var methname (fst apair) in
        let access_path : A.elt = (base_pvar, [FieldAccess fld]) in
        let ph = placeholder_vardef methname in
        let double = doubleton access_path (Var.of_id id, []) in
        let newstate = (methname, (ph, []), LocationSet.singleton Location.dummy, double) in
        let newset = S.add newstate (fst apair) in
        (newset, snd apair)
    | Lfield (Lvar pvar, fld, _) when Pvar.is_global pvar ->
        let access_path : A.elt = (Var.of_pvar pvar, [FieldAccess fld]) in
        (* 이전에 정의된 적이 있는가 없는가로 경우 나눠야 함 (formal엔 못 옴) *)
        begin match search_target_tuples_by_vardef_ap access_path methname (fst apair) with
          | [] ->
              let ph = placeholder_vardef methname in
              let double = doubleton access_path (Var.of_id id, []) in
              let newtuple = (methname, (ph, []), LocationSet.singleton Location.dummy, double) in
              let newset = S.add newtuple (fst apair) in
              (newset, snd apair)
          | h::_ as tuples ->
              let var, fldlst = second_of h in
              let most_recent_loc = H.get_most_recent_loc (methname, (var, fldlst)) (snd apair) in
              let (proc, vardef, loc, aliasset) as most_recent_tuple = search_astate_by_loc most_recent_loc tuples in
              let astate_set_rmvd = S.remove most_recent_tuple (fst apair) in
              let mra_updated = (proc, vardef, loc, A.add (Var.of_id id, []) aliasset) in
              let double = doubleton (Var.of_id id, []) (Var.of_pvar pvar, fldlst) in
              let ph = placeholder_vardef methname in
              let newstate = (methname, (ph, []), LocationSet.singleton Location.dummy, double) in
              let newset = S.add mra_updated astate_set_rmvd |> S.add newstate in
              (newset, snd apair) end
    | Lindex (Var var, _) -> (* Var[const or Var] *)
        let access_path : A.elt = (Var.of_id var, [ArrayAccess (Typ.void_star, [])]) in
        (* 이전에 정의된 적이 있는가 없는가로 경우 나눠야 함 (formal엔 못 옴) *)
        begin match search_target_tuples_by_vardef_ap (access_path) methname (fst apair) with
          | [] ->
              let ph = placeholder_vardef methname in
              let double = doubleton access_path (Var.of_id id, []) in
              let newtuple = (methname, (ph, []), LocationSet.singleton Location.dummy, double) in
              let newset = S.add newtuple (fst apair) in
              (newset, snd apair)
          | _ -> L.die InternalError
                   "exec_load failed, id: %a, exp: %a, astate_set: %a, methname: %a"
                   Ident.pp id Exp.pp exp S.pp (fst apair) Procname.pp methname end
    | Var _ -> (* 아직은 버리는 케이스만 있으니 e.g. _=*n$9 *)
        apair
    | _ -> L.progress "Unsupported Load Instruction %a := %a at %a@."
             Ident.pp id Exp.pp exp Procname.pp methname; apair


  (** register tuples for formal arguments before a procedure starts. *)
  let register_formals (apair:P.t) cfg_node methname : P.t =
    let node = CFG.Node.underlying_node cfg_node in
    match Procdesc.Node.get_kind node with
    | Start_node ->
        let formals = get_my_formal_args methname in
        let formal_aps = List.map ~f:(fun var -> (var, [])) formals in
        let proc = Procdesc.Node.get_proc_name node in
        let targetloc = Procdesc.Node.get_loc node in
        (* 파라미터 라인넘버 보정 *)
        let loc = LocationSet.singleton { Location.line=targetloc.line-1
                                        ; Location.col=targetloc.col
                                        ; Location.file=targetloc.file } in
        let bake_newstate = fun (var_ap:MyAccessPath.t) ->
          (proc, var_ap, loc, A.singleton var_ap) in
        let tuplelist = List.map ~f:bake_newstate formal_aps in
        let tupleset = S.of_list tuplelist in
        let formal_aps_with_methname = List.map ~f:(fun tup ->
            (methname, tup)) formal_aps in
        let newmap = H.batch_add_to_history formal_aps_with_methname loc (snd apair) in
        let newset = S.union (fst apair) tupleset in
        (newset, newmap)
    | _ -> apair


  let rec catMaybes_tuplist (optlist:('a*'b option) list) : ('a*'b) list =
    match optlist with
    | [] -> []
    | (sth1, Some sth2) :: t -> (sth1, sth2)::catMaybes_tuplist t
    | (_, None)::_ -> L.die InternalError "catMaybes_tuplist failed"


  let exec_instr (prev':P.t) ({InterproceduralAnalysis.proc_desc=_;
                               InterproceduralAnalysis.analyze_dependency})
      (node:CFG.Node.t) (instr:Sil.instr) : P.t =
    let methname = node
                   |> CFG.Node.underlying_node
                   |> Procdesc.Node.get_proc_name in
    let prev = register_formals prev' node methname in
    match instr with
    | Load {id=id; e=exp} ->
        exec_load id exp prev methname
    | Store {e1=exp1; e2=exp2} ->
        exec_store exp1 exp2 methname prev node
    | Prune _ -> prev
    | Call ((ret_id, _), e_fun, arg_ts, _, _) ->
      begin match e_fun with
        | Const (Cfun callee_methname) ->
          if Option.is_some @@ Procdesc.load callee_methname
          then exec_call ret_id callee_methname arg_ts analyze_dependency prev methname
          else begin try (exec_lib_call ret_id callee_methname arg_ts
                      analyze_dependency prev methname node)
            with _ ->
              exec_call ret_id callee_methname arg_ts analyze_dependency prev methname end
        | _ -> L.die InternalError
                 "exec_call failed, ret_id: %a, e_fun: %a astate_set: %a, methname: %a"
                 Ident.pp ret_id Exp.pp e_fun S.pp (fst prev) Procname.pp methname end
    | Metadata _ -> prev


  let pp_session_name node fmt =
    F.fprintf fmt "def/loc/alias %a" CFG.Node.pp_id (CFG.Node.id node)
end


module CFG = ProcCfg.OneInstrPerNode (ProcCfg.Normal)
module Analyzer = AbstractInterpreter.MakeRPO (TransferFunctions (CFG))


(** Postcondition computing function *)
let checker ({InterproceduralAnalysis.proc_desc} as analysis_data) =
  Analyzer.compute_post analysis_data ~initial:DefLocAliasDomain.initial proc_desc
