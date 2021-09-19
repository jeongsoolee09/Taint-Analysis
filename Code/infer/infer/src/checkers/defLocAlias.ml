open! IStd
open DefLocAliasDomain
open DefLocAliasSearches
open DefLocAliasPredicates
open DefLocAliasPP

(** Interprocedural Liveness Checker with alias relations
    and redefinitions in mind. *)

exception NotImplemented
exception IDontKnow
exception TODO
exception FindActualPvarFailed
exception InvalidExp

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
    Var.of_pvar
    @@ Pvar.mk (Mangled.from_string @@ F.asprintf "returnv: %a" Procname.pp procname) procname


  (** Ref variable to number all callv special variables *)
  let callv_number = ref (-1)

  (** specially mangled variable to mark an AP as passed to a callee *)
  let mk_callv procname ret_id =
    callv_number := !callv_number + 1 ;
    Var.of_pvar
    @@ Pvar.mk
      (Mangled.from_string @@ F.asprintf "callv_%d_%a: %a" !callv_number Ident.pp ret_id Procname.pp procname)
      procname


  (** specially mangled variable to mark an AP as passed to a callee *)
  let mk_callv_pvar procname =
    callv_number := !callv_number + 1 ;
    Pvar.mk
      (Mangled.from_string @@ F.asprintf "callv_%d: %a" !callv_number Procname.pp procname)
      procname


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


  (** Retrieve the latest pvar associated with the given id *)
  let search_recent_vardef_astate (methname:Procname.t) (id:Var.t) (apair:P.t) : T.t =
    let elements = S.elements (fst apair) in
    let rec inner methname id astate_list =
      match astate_list with
      | [] -> L.die InternalError
                "search_recent_vardef_astate failed, methname: %a, id: %a, astate_set: %a@."
                Procname.pp methname Var.pp id P.pp apair
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
    inner methname id elements


  (** given a doubleton set of lv and pv, extract the pv. *)
  let rec extract_another_pvar (id:Ident.t) (varsetlist:A.t list) : Var.t =
    match varsetlist with
    | [] -> L.die InternalError
              "extract_another_pvar failed, id: %a, varsetlist: %a@."
              Ident.pp id pp_aliasset_list varsetlist
    | set::t ->
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


  let put_fieldname (fieldname:Fieldname.t) (aliastup:MyAccessPath.t) =
    let var, lst = aliastup in
    (var, lst @ [AccessPath.FieldAccess fieldname])


  let put_arrayaccess (aliastup:A.elt) =
    let var, lst = aliastup in
    (var, lst @ [AccessPath.ArrayAccess (Typ.void_star, [])])


  let merge_ph_tuples (lhs: T.t) (rhs: T.t) (lset: LocationSet.t) : T.t =
    let proc_lhs, pvar_lhs, _, alias_lhs = lhs in
    let proc_rhs, _, _, alias_rhs = rhs in
    (* Sanity check *)
    if not @@ Procname.equal proc_lhs proc_rhs
    then L.die InternalError
        "merge_ph_tuples failed, lhs: %a, rhs: %a, location: %a"
        T.pp lhs T.pp rhs LocationSet.pp lset;
    (proc_lhs, pvar_lhs, lset, A.add pvar_lhs @@ A.union alias_lhs alias_rhs)


  let alias_propagation ((previous_proc, previous_vardef, previous_locset, previous_aliasset) as previous_tuple: T.t)
             (astate_set: S.t) (to_put_pvar: Pvar.t) (id: Ident.t) (methname: Procname.t) : S.t = 
    let open List in
    let to_put_pvar_ap = (Var.of_pvar to_put_pvar, []) in
    let previous_tuple_updated =
      (previous_proc, previous_vardef, previous_locset, A.add to_put_pvar_ap previous_aliasset) in
    (* downward propagation: look at the aliasset *)
    let pvar_vardefs_in_aliasset =
      let pvar_aps = A.filter is_pvar_ap previous_aliasset
                     |> A.elements
                     |> List.filter ~f:(fun ap -> 
                          (not @@ is_returnv_ap ap) &&
                          (not @@ is_callv_ap ap) &&
                          (not @@ is_return_ap ap) &&
                          (not @@ is_param_ap ap) &&
                          (not @@ is_this_ap ap) &&
                          (not @@ MyAccessPath.equal ap previous_vardef)) in
      fold ~f:(fun acc pvar_ap ->
                     try
                       (search_target_tuple_by_vardef_ap pvar_ap methname astate_set)::acc
                     with _ -> acc) pvar_aps ~init:[] in
      let pvar_vardefs_in_aliasset_updated = pvar_vardefs_in_aliasset
                                            >>| (fun (p, v, l, a) -> (p, v, l, A.add to_put_pvar_ap a))
                                            |> S.of_list in
    (* upward propagation: look at other vardefs aliassed with this previous_tuple *)
    let alias_with_previous_tuple = search_target_tuples_by_pvar_ap previous_vardef methname astate_set
                                    |> List.filter ~f:(fun ap -> not @@ T.equal ap previous_tuple) in
    let alias_with_previous_tuple_updated = alias_with_previous_tuple
                                            >>| (fun (p, v, l, a) -> (p, v, l, A.add to_put_pvar_ap a))
                                            |> S.of_list in
    astate_set
    |> S.remove previous_tuple
    |> S.add previous_tuple_updated    
    |> (fun set -> S.diff set @@ S.of_list pvar_vardefs_in_aliasset)
    |> (fun set -> S.diff set @@ S.of_list alias_with_previous_tuple)
    |> S.union pvar_vardefs_in_aliasset_updated
    |> S.union alias_with_previous_tuple_updated
 

  let exp_as_var (exp: Exp.t) : Ident.t =
    match exp with
    | Var id -> id
    | _ -> raise @@ Invalid_argument (Exp.to_string exp)


  let has_unowned_var (operands: Exp.t list) (pvar_ap: MyAccessPath.t) (astate_set: S.t) =
    List.exists ~f:(fun exp -> exp_is_var exp && not @@ is_mine (exp_as_var exp) pvar_ap astate_set) operands


  let rec exec_store (exp1:Exp.t) (exp2:Exp.t) (methname:Procname.t) (apair:P.t) (node:CFG.Node.t) : P.t =
    match exp1, exp2 with
    (* ============ LHS is Lvar ============ *)
    | Lvar pv, Var id ->
        ( match Var.is_return (Var.of_pvar pv) with
          | true -> ( (* A variable is being returned *)
              let target_tuples = weak_search_target_tuples_by_id id (fst apair) in
              let processed = List.fold ~f:(fun acc (_, _, _, aliasset) ->
                try (* 가장 최근의 pvar를 찾아서 alias set에 return을 집어넣어 준다. *)
                  let pvar_var, _ = A.find_first is_program_var_ap aliasset in
                  let most_recent_loc = H.get_most_recent_loc (methname, (pvar_var, [])) (snd apair) in
                  let candStates = search_target_tuples_by_vardef pvar_var methname acc in
                  let (proc, var, loc, aliasset') as candState = search_astate_by_loc most_recent_loc candStates in
                  let astate_rmvd = S.remove candState acc in
                  let logicalvar = Var.of_id id in
                  let returnvar = Var.of_pvar pv in
                  let newtuple = (proc, var, loc, A.union aliasset' (doubleton (logicalvar, []) (returnvar, []))) in
                  S.add newtuple astate_rmvd
                with _ -> (* the pvar_var is not redefined in the procedure. *)
                  let (proc, var, loc, aliasset') as candState = search_target_tuple_by_id id methname acc in
                  let astate_rmvd = S.remove candState acc in
                  let logicalvar = Var.of_id id in
                  let returnvar = Var.of_pvar pv in
                  let newtuple = (proc, var, loc, A.union aliasset' (doubleton (logicalvar, []) (returnvar, []))) in
                  S.add newtuple astate_rmvd ) target_tuples ~init:(fst apair) in
              (processed, snd apair) )
          | false -> (* An ordinary variable assignment. *)
              let pvar_ap = (Var.of_pvar pv, []) in
              (* making a new tuple for this operation *)
              let this_operation_locset = LocationSet.singleton @@ CFG.Node.loc node in
              let newtuple = (methname, pvar_ap, this_operation_locset, A.singleton pvar_ap) in
              let newtuple_added = S.add newtuple (fst apair) in
              (* updating previous tuples *)
              let previous_tuple = weak_search_target_tuple_by_id id (fst apair) in
              let alias_propagated: S.t = alias_propagation previous_tuple newtuple_added pv id methname in
              let newmap = H.add_to_history (methname, pvar_ap) this_operation_locset (snd apair) in
              let newset = S.add newtuple alias_propagated in
              (newset, newmap) )
    | Lvar pv, Const _ ->
       if (Var.is_return (Var.of_pvar pv)) then apair else
        let pvar_var = Var.of_pvar pv in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let aliasset_new = A.singleton (pvar_var, []) in
        let newtuple = (methname, (pvar_var, []), loc, aliasset_new) in
        let newmap = H.add_to_history (methname, (pvar_var, [])) loc (snd apair) in
        let newset = S.add newtuple (fst apair) in
        (newset, newmap)
    | Lvar pvar, Exn _ when Var.is_return (Var.of_pvar pvar) ->
        apair
    | Lvar pv, BinOp (_, exp1, exp2) ->
       let all_atomic_operands = List.stable_dedup @@ (collect_atomic_exps exp1) @ (collect_atomic_exps exp2) in
       let pvar_ap = (Var.of_pvar pv, []) in
       if has_unowned_var all_atomic_operands pvar_ap (fst apair) then
         (* Make a new tuple and update all most recent astates of the unowned vars *)
         (* 1. making a new tuple. *)
         let loc = LocationSet.singleton @@ CFG.Node.loc node in
         let aliasset_new = A.singleton pvar_ap in
         let newtuple = (methname, pvar_ap, loc, aliasset_new) in
         (* 2. updating all most recent astates. *)
         let all_unowned_vars_updated =
           List.fold ~f:(fun acc exp ->
               if exp_is_var exp then
                 let ident = exp_as_var exp in
                 let (proc, vardef, locset, aliasset) as target_tuple =
                   search_target_tuple_by_id ident methname acc in
                 let target_tuple_updated =
                   (proc, vardef, locset, A.add (Var.of_pvar pv, []) aliasset) in
                 acc |> S.remove target_tuple |> S.add target_tuple_updated
               else if exp_is_const exp then acc else
                 raise InvalidExp ) all_atomic_operands ~init:(fst apair) in
         (S.add newtuple all_unowned_vars_updated, snd apair) 
       else
         (* Make a new tuple and end *)
         let loc = LocationSet.singleton @@ CFG.Node.loc node in
         let aliasset_new = A.singleton pvar_ap in
         let newtuple = (methname, pvar_ap, loc, aliasset_new) in
         let newmap = H.add_to_history (methname, pvar_ap) loc (snd apair) in
         let newset = S.add newtuple (fst apair) in
         (newset, newmap)
    (* ============ LHS is Lfield ============ *)
    | Lfield (Var lhs_id, fld, _), Var rhs_id ->
        (* finding the pvar tuple (lhs) getting stored *)
        begin try  (* normal cases where x = new(); then x.f = ... . *)
            let loc = LocationSet.singleton @@ CFG.Node.loc node in
            let (lhs_proc, lhs_var, lhs_loc, lhs_aliasset) as lhs_tuple =
              search_target_tuple_by_id lhs_id methname (fst apair) in
            (* update the lhs vartuple. *)
            let lhs_var_updated = put_fieldname fld lhs_var in
            let new_lhs_aliasset = A.singleton lhs_var_updated in
            let new_tuple = (lhs_proc, lhs_var_updated, lhs_loc, new_lhs_aliasset) in
            (* find the rhs vartuple and update it. *)
            let (rhs_proc, rhs_var, rhs_loc, rhs_aliasset) as rhs_tuple =
              search_target_tuple_by_id rhs_id methname (fst apair) in
            let rhs_tuple_updated = (rhs_proc, rhs_var, rhs_loc, A.add lhs_var_updated rhs_aliasset) in
            (* update the historymap. *)
            let new_history = H.add_to_history (methname, lhs_var_updated) loc (snd apair) in
            let newset =
              (fst apair)
              |> S.remove rhs_tuple
              |> S.add rhs_tuple_updated
              |> S.add new_tuple in
            (newset, new_history)
          with _ -> (* abnormal cases where n$2 = new() and n$2 is not owned by any pvars *)
            (* create a new ph tuple! *)
            let ph = placeholder_vardef methname in
            let loc = LocationSet.singleton Location.dummy in
            let aliasset = doubleton (Var.of_id lhs_id, [AccessPath.FieldAccess fld]) (Var.of_id rhs_id, []) in
            let newset = S.add (methname, (ph, []), loc, aliasset) (fst apair) in
            (newset, snd apair) end
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
    | Lfield (Var id, fld, _), BinOp (_, exp2_1, exp2_2) ->
        let lhs_pvar_ap =
          search_target_tuple_by_id id methname (fst apair) |> second_of  |> put_fieldname fld in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let all_atomic_operands = List.stable_dedup @@ (collect_atomic_exps exp1) @ (collect_atomic_exps exp2) in
        if has_unowned_var all_atomic_operands lhs_pvar_ap (fst apair) then
          let all_unowned_vars_updated =
            List.fold ~f:(fun acc exp -> 
                if exp_is_var exp then
                  let (rhs_proc, rhs_vardef, rhs_locset, rhs_aliasset) as rhs_tuple =
                    search_target_tuple_by_id (exp_as_var exp) methname acc in
                  let rhs_tuple_updated = (rhs_proc, rhs_vardef, rhs_locset, A.add lhs_pvar_ap rhs_aliasset) in
                  acc |> S.remove rhs_tuple |> S.add rhs_tuple_updated
                else acc) all_atomic_operands ~init:(fst apair) in 
            let newtuple = (methname, lhs_pvar_ap, loc, A.singleton lhs_pvar_ap) in
            let newset = S.add newtuple all_unowned_vars_updated in
            let new_history = H.add_to_history (methname, lhs_pvar_ap) loc (snd apair) in
            (newset, new_history)
            else 
              let newtuple = (methname, lhs_pvar_ap, loc, A.singleton lhs_pvar_ap) in
              let newmap = H.add_to_history (methname, lhs_pvar_ap) loc (snd apair) in
              let newset = S.add newtuple (fst apair) in
              (newset, newmap)
    (* ============ LHS is Lindex ============ *)
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
    | Lindex (Var lhs_id, _), Var rhs_id ->
       let loc = LocationSet.singleton @@ CFG.Node.loc node in
       let (lhs_proc, lhs_var, lhs_loc, lhs_aliasset) as lhs_tuple =
         search_target_tuple_by_id lhs_id methname (fst apair) in
       (* update the lhs vartuple. *)
       let lhs_var_updated = put_arrayaccess lhs_var in
       let new_lhs_aliasset = A.singleton lhs_var_updated in
       let new_tuple = (lhs_proc, lhs_var_updated, lhs_loc, new_lhs_aliasset) in
       (* find the rhs vartuple and update it. *)
       let (rhs_proc, rhs_var, rhs_loc, rhs_aliasset) as rhs_tuple =
         search_target_tuple_by_id rhs_id methname (fst apair) in
       let rhs_tuple_updated = (rhs_proc, rhs_var, rhs_loc, A.add lhs_var_updated rhs_aliasset) in
       (* update the historymap. *)
       let new_history = H.add_to_history (methname, lhs_var_updated) loc (snd apair) in
       let newset =
         (fst apair)
         |> S.remove rhs_tuple
         |> S.add rhs_tuple_updated
         |> S.add new_tuple in
       (newset, new_history)
    | Lindex (Var id, _), BinOp (_, exp2_1, exp2_2) ->
        let lhs_pvar_ap =
          search_target_tuple_by_id id methname (fst apair) |> second_of |> put_arrayaccess in
        let loc = LocationSet.singleton @@ CFG.Node.loc node in
        let all_atomic_operands = List.stable_dedup @@ (collect_atomic_exps exp1) @ (collect_atomic_exps exp2) in
        if has_unowned_var all_atomic_operands lhs_pvar_ap (fst apair) then
          let all_unowned_vars_updated =
            List.fold ~f:(fun acc exp -> 
                if exp_is_var exp then
                  let (rhs_proc, rhs_vardef, rhs_locset, rhs_aliasset) as rhs_tuple =
                    search_target_tuple_by_id (exp_as_var exp) methname acc in
                  let rhs_tuple_updated = (rhs_proc, rhs_vardef, rhs_locset, A.add lhs_pvar_ap rhs_aliasset) in
                  acc |> S.remove rhs_tuple |> S.add rhs_tuple_updated
                else acc) all_atomic_operands ~init:(fst apair) in 
            let newtuple = (methname, lhs_pvar_ap, loc, A.singleton lhs_pvar_ap) in
            let newset = S.add newtuple all_unowned_vars_updated in
            let new_history = H.add_to_history (methname, lhs_pvar_ap) loc (snd apair) in
            (newset, new_history)
            else 
              let newtuple = (methname, lhs_pvar_ap, loc, A.singleton lhs_pvar_ap) in
              let newmap = H.add_to_history (methname, lhs_pvar_ap) loc (snd apair) in
              let newset = S.add newtuple (fst apair) in
              (newset, newmap)
    (* ============ Misc ============ *)
    | lhs, Cast (_, exp) -> (* we ignore the cast *)
        exec_store lhs exp methname apair node
    | _, _ ->
        L.progress "Unsupported Store instruction %a := %a at %a@."
          Exp.pp exp1 Exp.pp exp2 Procname.pp methname; apair


  (** exp를 받아서 logical var로 변환한다. *)
  let convert_exp_to_logical (exp:Exp.t) =
    match exp with
    | Var id -> id
    | _ -> Ident.create_none () (* create a dummy *)


  let find_actual_pvar_for_inter_id (id: Ident.t) (current_methname:Procname.t) (astate_set: S.t) =
    let statetups_alias_with_id = search_target_tuples_by_id id current_methname astate_set in
    try 
      find_most_linenumber statetups_alias_with_id
    with _ -> 
      raise FindActualPvarFailed


  let exec_call (ret_id:Ident.t) (callee_methname:Procname.t) (arg_ts:(Exp.t*Typ.t) list)
      analyze_dependency (apair:P.t) (methname:Procname.t) : P.t =
    let open List in
    match analyze_dependency callee_methname with
    | Some (_, callee_summary) ->
        ( match input_is_void_type arg_ts (fst apair) with
          | true -> (* All Arguments are Just Constants: just apply the summary, make a new tuple and end *)
            let astate_set_summary_applied =
              apply_summary (fst apair) callee_summary callee_methname ret_id methname in
              let aliasset = A.add (mk_returnv callee_methname, []) @@ A.singleton (Var.of_id ret_id, []) in
              let loc = LocationSet.singleton Location.dummy in
              let newtuple = (methname, (placeholder_vardef methname, []), loc, aliasset) in
              let newset = S.add newtuple astate_set_summary_applied in
              (newset, (snd apair))
          | false -> (* There is at least one argument which is a non-thisvar variable *)
             (let astate_set_summary_applied =
                apply_summary (fst apair) callee_summary callee_methname ret_id methname in
              let formals = get_formal_args analyze_dependency callee_methname in
              let actuals_logical_id = arg_ts >>| (fst >> convert_exp_to_logical) |> filter ~f:(not << Ident.is_none) in
              let actual_interid_param_triples = foldi ~f:(fun index acc inter_id -> 
                                                     try
                                                       let actual_pvar = fst @@ second_of @@ find_actual_pvar_for_inter_id inter_id methname astate_set_summary_applied in
                                                       let corresponding_formal = nth_exn formals index in
                                                       (actual_pvar, inter_id, corresponding_formal)::acc
                                                     with FindActualPvarFailed ->
                                                       acc) actuals_logical_id ~init:[] in
              let astate_set_updated = fold ~f:(fun acc (actual, inter_id, formal) ->
                                           L.d_printfln "actual: %a, inter_id: %a, formal: %a@." Var.pp actual Ident.pp inter_id Var.pp formal;
                                           let actual_vardef_astates = search_target_tuples_by_vardef actual methname acc in
                                           let (proc, vardef, locset, aliasset) as most_recent_vardef_astate =
                                             find_most_linenumber actual_vardef_astates in
                                           let acc_rmvd = S.remove most_recent_vardef_astate acc in
                                           let mangled_callv = (mk_callv callee_methname ret_id, []) in
                                           let actual_vardef_astate_updated = (proc, vardef, locset,
                                                                               aliasset
                                                                               |> A.add (formal, [])
                                                                               |> A.add mangled_callv) in
                                           let returnv = mk_returnv callee_methname in
                                           let ph_tuple = (methname, (placeholder_vardef methname, []), 
                                                           LocationSet.singleton Location.dummy, SetofAliases.empty
                                                                                                 |> A.add (Var.of_id ret_id, [])
                                                                                                 |> A.add (returnv, [])) in
                                           acc_rmvd
                                           |> (fun acc -> S.add actual_vardef_astate_updated acc)
                                           |> (fun acc -> S.add ph_tuple acc)
                                         ) actual_interid_param_triples ~init:astate_set_summary_applied in
              (astate_set_updated, snd apair) ) )
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
      analyze_dependency ((astate_set, histmap): P.t) (caller_methname:Procname.t) (node:CFG.Node.t) : P.t =
    let open List in
    match is_cast callee_methname with
    | true ->
       let actuals_logical = arg_ts >>| (fst >> convert_exp_to_logical) |> filter ~f:(not << Ident.is_none) in
       (* assert (Int.equal (length actuals_logical) 1) ; *)
       let before_cast_tuple =
         weak_search_target_tuple_by_id (List.hd_exn actuals_logical) astate_set in
       let (proc, vardef, locset, aliasset) = before_cast_tuple in
       let after_cast_tuple = (proc, vardef, locset, (A.add (Var.of_id ret_id, [])) aliasset) in
       (astate_set |> S.remove before_cast_tuple |> S.add after_cast_tuple, histmap)
    | false -> 
        (* 1. Mangle some parameters.
        formal parameter naming schema:
                param_{callee_name_simple}_{line}_{param_index} *)
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
            ~f:(fun _ -> mk_callv_pvar callee_methname) in
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
              begin match search_target_tuples_by_vardef_ap ((Var.of_pvar pvar), []) methname (fst apair) with
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
                    let newset = S.add mrt_updated astate_set_rmvd in
                    (newset, snd apair) end end
    | Lfield (Var var, fld, _) ->
        (* Find the base pvar astate. *)
        let (rhs_base_proc, rhs_base_vardef, rhs_base_locset, rhs_base_aliasset) as rhs_base_astate =
          search_target_tuple_by_id var methname (fst apair) in
        (* Find the base pvar + fld astate. Note: it may not exist at this point. *)
        (try 
           let rhs_vardef = put_fieldname fld rhs_base_vardef in
           let (rhs_proc, rhs_vardef, rhs_locset, rhs_aliasset) as rhs_astate =
             search_target_tuple_by_vardef_ap rhs_vardef methname (fst apair) in
           let rhs_astate_updated = (rhs_proc, rhs_vardef, rhs_locset, A.add (Var.of_id id, []) rhs_aliasset) in
           let newset = (fst apair) |> S.remove rhs_astate |> S.add rhs_astate_updated in
           (newset, snd apair)
         with SearchAstateByPVarFailed -> (* there does not exist a pvar + fld astate. We make a new one. *)
           let rhs_vardef = put_fieldname fld rhs_base_vardef in
           let new_tuple = (methname, rhs_vardef, rhs_base_locset, doubleton (Var.of_id id, []) rhs_vardef) in
           let newset = S.add new_tuple (fst apair) in
           (newset, snd apair))
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
