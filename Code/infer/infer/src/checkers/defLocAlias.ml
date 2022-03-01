(* open! IStd *)
open DefLocAliasDomain
open DefLocAliasSearches
open DefLocAliasPredicates
open DefLocAliasPP

(** Interprocedural Liveness Checker with alias relations and redefinitions in mind. *)

exception FindActualPvarFailed

exception InvalidExp

exception NotACallInstr of string

exception NoMatchingCallv of string

exception TooManyMatchingCallv of string

exception MatchFailed

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

  let ( >>| ) = List.( >>| )

  let ( >>= ) = List.( >>= )

  type instr = Sil.instr

  type analysis_data = P.t InterproceduralAnalysis.t

  let choose_larger_location (locset1 : LocationSet.t) (locset2 : LocationSet.t) =
    let elem1 = LocationSet.min_elt locset1 in
    let elem2 = LocationSet.min_elt locset2 in
    match Location.compare elem1 elem2 with
    | -1 ->
        locset1
    | 0 ->
        if LocationSet.subset locset1 locset2 then locset1 else locset2
    | 1 ->
        locset2
    | _ ->
        L.die InternalError "choose_larger_location failed, locset1: %a, locset2: %a" LocationSet.pp
          locset1 LocationSet.pp locset2


  (** Ref variable to number all callv special variables *)
  let callv_number = ref 0

  (** truncate the textual representation if necessary, to avoid weird formatting issues.. *)
  let truncate_procname (procname : Procname.t) : string =
    let target = Procname.get_method procname in
    let antipattern = Str.regexp "\\(.*_[0-9]+_[0-9]+\\)" in
    let _ = Str.string_match antipattern (Procname.get_method procname) 0 in
    let to_truncate = Str.matched_group 1 target in
    List.hd_exn @@ String.split ~on:'_' to_truncate


  (* Manglers ========================================= *)
  (* ================================================== *)

  (** specially mangled variable to mark an AP as passed to a callee *)
  let mk_callv_pvar procname linum =
    let antipattern = Str.regexp "\\(.*_[0-9]+_[0-9]+\\)" in
    let out =
      if Str.string_match antipattern (Procname.get_method procname) 0 then
        let truncated = truncate_procname procname in
        Pvar.mk
          (Mangled.from_string @@ F.asprintf "callv_%d_%d: %s" !callv_number linum truncated)
          procname
      else
        Pvar.mk
          ( Mangled.from_string
          @@ F.asprintf "callv_%d_%d: %a" !callv_number linum Procname.pp procname )
          procname
    in
    callv_number := !callv_number + 1 ;
    out


  let mk_callv procname linum = Var.of_pvar @@ mk_callv_pvar procname linum

  (** specially mangled variable to mark a value as returned from callee *)
  let mk_returnv (procname : Procname.t) (counters : int list) (linum : int) =
    let pp_int_list fmt intlist =
      F.fprintf fmt "[" ;
      List.iter ~f:(F.fprintf fmt "%d ") counters ;
      F.fprintf fmt "]"
    in
    let antipattern = Str.regexp "\\(.*_[0-9]+_[0-9]+\\)" in
    if Str.string_match antipattern (Procname.get_method procname) 0 then
      let truncated = truncate_procname procname in
      Var.of_pvar
      @@ Pvar.mk
           ( Mangled.from_string
           @@ F.asprintf "returnv_%a_%d: %s" pp_int_list counters linum truncated )
           procname
    else
      Var.of_pvar
      @@ Pvar.mk
           ( Mangled.from_string
           @@ F.asprintf "returnv_%a_%d: %a" pp_int_list counters linum Procname.pp procname )
           procname


  let mk_returnv_for_frontend_new (procname : Procname.t) ~(classname_str : string)
      (counters : int list) (linum : int) =
    let pp_int_list fmt intlist =
      F.fprintf fmt "[" ;
      List.iter ~f:(F.fprintf fmt "%d ") counters ;
      F.fprintf fmt "]"
    in
    Var.of_pvar
    @@ Pvar.mk
         ( Mangled.from_string
         @@ F.asprintf "returnv_%a_%d: __new_%s" pp_int_list counters linum classname_str )
         procname


  (** specially mangled variable to mark a value as a param of the callee *)
  let mk_param (procname : Procname.t) (linum : int) (param_index : int) =
    Var.of_pvar
    @@ Pvar.mk
         ( Mangled.from_string
         @@ F.asprintf "param_%s_%d_%d" (Procname.get_method procname) linum param_index )
         procname


  let mk_cast_of (ap : MyAccessPath.t) (procname : Procname.t) =
    let var, flds = ap in
    let cast_var =
      Var.of_pvar @@ Pvar.mk (Mangled.from_string @@ F.asprintf "%a_cast" Var.pp var) procname
    in
    (cast_var, flds)


  let rec extract_nonthisvar_from_args methname (arg_ts : (Exp.t * Typ.t) list) (astate_set : S.t) :
      Exp.t list =
    match arg_ts with
    | [] ->
        []
    | ((Var var as v), _) :: t ->
        let aliasset = fourth_of @@ search_target_tuple_by_id var methname astate_set in
        if not (A.exists is_this_ap aliasset) then
          v :: extract_nonthisvar_from_args methname t astate_set
        else extract_nonthisvar_from_args methname t astate_set
    | (other, _) :: t ->
        other :: extract_nonthisvar_from_args methname t astate_set


  let leave_only_var_tuples (ziplist : (Var.t * Var.t) list) =
    let leave_logical (x, _) = is_logical_var x in
    let map_func (var1, var2) =
      match (var1, var2) with
      | Var.LogicalVar id, var ->
          (Var.of_id id, var)
      | _, _ ->
          L.die InternalError "leave_only_var_tuples/map_func failed, exp: %a, var: %a@." Var.pp
            var1 Var.pp var2
    in
    List.filter ~f:leave_logical ziplist |> List.map ~f:map_func


  let get_formal_args analyze_dependency (callee_methname : Procname.t) : Var.t list =
    match analyze_dependency callee_methname with
    | Some (procdesc, _) ->
        Procdesc.get_formals procdesc >>| convert_from_mangled callee_methname
    | None ->
        (* Oops, it's a native code outside our focus *) []


  let put_fieldname (fieldname : Fieldname.t) (aliastup : MyAccessPath.t) =
    let var, lst = aliastup in
    (var, lst @ [AccessPath.FieldAccess fieldname])


  let put_arrayaccess (aliastup : A.elt) =
    let var, lst = aliastup in
    (var, lst @ [AccessPath.ArrayAccess (Typ.void_star, [])])


  let exp_as_var (exp : Exp.t) : Ident.t =
    match exp with Var id -> id | _ -> raise @@ Invalid_argument (Exp.to_string exp)


  let has_unowned_var (operands : Exp.t list) (pvar_ap : MyAccessPath.t) (astate_set : S.t) =
    List.exists
      ~f:(fun exp -> exp_is_var exp && (not @@ is_mine (exp_as_var exp) pvar_ap astate_set))
      operands


  let rec exec_store (exp1 : Exp.t) (exp2 : Exp.t) (methname : Procname.t) (apair : P.t)
      (node_loc : Location.t) : P.t =
    match (exp1, exp2) with
    (* ============ LHS is Lvar ============ *)
    | Lvar pv, Var id -> (
      match Var.is_return (Var.of_pvar pv) with
      | true ->
          (* A variable is being returned *)
          let target_tuples = weak_search_target_tuples_by_id id (fst apair) in
          let processed =
            List.fold
              ~f:(fun acc (_, _, _, aliasset) ->
                try
                  (* 가장 최근의 pvar를 찾아서 alias set에 return을 집어넣어 준다. *)
                  let pvar_var, _ = A.find_first is_program_var_ap aliasset in
                  let most_recent_loc =
                    H.get_most_recent_loc (methname, (pvar_var, [])) (snd apair)
                  in
                  let candStates = search_target_tuples_by_vardef pvar_var methname acc in
                  let ((proc, var, loc, aliasset') as candState) =
                    search_astate_by_loc most_recent_loc candStates
                  in
                  let astate_rmvd = S.remove candState acc in
                  let logicalvar = Var.of_id id in
                  let returnvar = Var.of_pvar pv in
                  let newtuple =
                    (proc, var, loc, A.union aliasset' (doubleton (logicalvar, []) (returnvar, [])))
                  in
                  S.add newtuple astate_rmvd
                with _ ->
                  (* the pvar_var is not redefined in the procedure. *)
                  let ((proc, var, loc, aliasset') as candState) =
                    search_target_tuple_by_id id methname acc
                  in
                  let astate_rmvd = S.remove candState acc in
                  let logicalvar = Var.of_id id in
                  let returnvar = Var.of_pvar pv in
                  let newtuple =
                    (proc, var, loc, A.union aliasset' (doubleton (logicalvar, []) (returnvar, [])))
                  in
                  S.add newtuple astate_rmvd )
              target_tuples ~init:(fst apair)
          in
          (processed, snd apair)
      | false ->
          (* An ordinary variable assignment. *)
          let ((rhs_proc, rhs_vardef, rhs_loc, rhs_aliasset) as rhs_pvar_tuple) =
            try weak_search_target_tuple_by_id id (fst apair) with _ -> bottuple
          in
          let pvar_var = Var.of_pvar pv in
          let loc = LocationSet.singleton node_loc in
          let rhs_pvar_tuple_updated =
            (rhs_proc, rhs_vardef, rhs_loc, A.add (pvar_var, []) rhs_aliasset)
          in
          if
            (* handling difficult loops: there already exists a tuple made in the previous fixpoint iteration, but a same vardef also exists in the different line! *)
            S.exists (* there already exists a tuple made in the previous fixpoint iteration *)
              (fun astate ->
                MyAccessPath.equal (second_of astate) (pvar_var, [])
                && LocationSet.mem node_loc (third_of astate) )
              (fst apair)
            && S.exists (* but a same vardef also exists in the different line *)
                 (fun astate ->
                   MyAccessPath.equal (second_of astate) (pvar_var, [])
                   && (not @@ LocationSet.mem node_loc (third_of astate)) )
                 (fst apair)
          then
            let ((lhs_proc, lhs_vardef, lhs_loc, lhs_aliasset) as lhs_tuple) =
              search_target_tuples_by_vardef_ap (pvar_var, []) methname (fst apair)
              |> find_most_linenumber
            in
            let lhs_tuple_updated = (lhs_proc, lhs_vardef, lhs_loc, lhs_aliasset) in
            let newset =
              fst apair |> S.remove lhs_tuple |> S.remove rhs_pvar_tuple |> S.add lhs_tuple_updated
            in
            (newset, snd apair)
          else
            let newtuple =
              if is_placeholder_vardef_ap (second_of rhs_pvar_tuple) then
                (methname, (pvar_var, []), loc, A.add (Var.of_pvar pv, []) rhs_aliasset)
              else (methname, (pvar_var, []), loc, A.singleton (Var.of_pvar pv, []))
            in
            let astate_set_rmvd = S.remove rhs_pvar_tuple (fst apair) in
            let newmap = H.add_to_history (methname, (pvar_var, [])) loc (snd apair) in
            if is_placeholder_vardef_ap (second_of rhs_pvar_tuple) then
              let newset = S.add newtuple astate_set_rmvd in
              (newset, newmap)
            else
              let newset = astate_set_rmvd |> S.add newtuple |> S.add rhs_pvar_tuple_updated in
              (newset, newmap) )
    | Lvar pv, Const _ ->
        if Var.is_return (Var.of_pvar pv) then apair
        else
          let pvar_var = Var.of_pvar pv in
          let loc = LocationSet.singleton node_loc in
          let aliasset_new = A.singleton (pvar_var, []) in
          let newtuple = (methname, (pvar_var, []), loc, aliasset_new) in
          let newmap = H.add_to_history (methname, (pvar_var, [])) loc (snd apair) in
          let newset = S.add newtuple (fst apair) in
          (newset, newmap)
    | Lvar pvar, Exn _ when Var.is_return (Var.of_pvar pvar) ->
        apair
    | Lvar pv, BinOp (_, exp1, exp2) ->
        let all_atomic_operands =
          List.stable_dedup @@ collect_atomic_exps exp1 @ collect_atomic_exps exp2
        in
        let pvar_ap = (Var.of_pvar pv, []) in
        if has_unowned_var all_atomic_operands pvar_ap (fst apair) then
          (* Make a new tuple and update all most recent astates of the unowned vars *)
          (* 1. making a new tuple. *)
          let loc = LocationSet.singleton node_loc in
          let aliasset_new = A.singleton pvar_ap in
          let newtuple = (methname, pvar_ap, loc, aliasset_new) in
          (* 2. updating all most recent astates. *)
          let all_unowned_vars_updated =
            List.fold
              ~f:(fun acc exp ->
                if exp_is_var exp then
                  let ident = exp_as_var exp in
                  let ((proc, vardef, locset, aliasset) as target_tuple) =
                    search_target_tuple_by_id ident methname acc
                  in
                  let target_tuple_updated =
                    (proc, vardef, locset, A.add (Var.of_pvar pv, []) aliasset)
                  in
                  acc |> S.remove target_tuple |> S.add target_tuple_updated
                else if exp_is_const exp then acc
                else raise InvalidExp )
              all_atomic_operands ~init:(fst apair)
          in
          let newset = S.add newtuple all_unowned_vars_updated in
          let newmap = H.add_to_history (methname, pvar_ap) loc (snd apair) in
          (newset, newmap)
        else
          (* Make a new tuple and end *)
          let loc = LocationSet.singleton node_loc in
          let aliasset_new = A.singleton pvar_ap in
          let newtuple = (methname, pvar_ap, loc, aliasset_new) in
          let newmap = H.add_to_history (methname, pvar_ap) loc (snd apair) in
          let newset = S.add newtuple (fst apair) in
          (newset, newmap)
    (* ============ LHS is Lfield ============ *)
    | Lfield (Var lhs_id, fld, _), Var rhs_id -> (
      (* finding the pvar tuple (lhs) getting stored *)
      try
        (* normal cases where x = new(); then x.f = ... . *)
        let loc = LocationSet.singleton node_loc in
        let ((lhs_proc, lhs_var, lhs_loc, lhs_aliasset) as lhs_tuple) =
          search_target_tuple_by_id lhs_id methname (fst apair)
        in
        (* update the lhs vartuple. *)
        let lhs_var_updated = put_fieldname fld lhs_var in
        let new_lhs_aliasset = A.singleton lhs_var_updated in
        let new_tuple = (lhs_proc, lhs_var_updated, lhs_loc, new_lhs_aliasset) in
        (* find the rhs vartuple and update it. *)
        let ((rhs_proc, rhs_var, rhs_loc, rhs_aliasset) as rhs_tuple) =
          search_target_tuple_by_id rhs_id methname (fst apair)
        in
        let rhs_tuple_updated = (rhs_proc, rhs_var, rhs_loc, A.add lhs_var_updated rhs_aliasset) in
        (* update the historymap. *)
        let newset =
          fst apair |> S.remove rhs_tuple |> S.add rhs_tuple_updated |> S.add new_tuple
        in
        let newmap = H.add_to_history (methname, lhs_var_updated) loc (snd apair) in
        (newset, newmap)
      with _ ->
        (* abnormal cases where n$2 = new() and n$2 is not owned by any pvars *)
        (* create a new ph tuple! *)
        let ph = placeholder_vardef methname in
        let loc = LocationSet.singleton Location.dummy in
        let aliasset =
          doubleton (Var.of_id lhs_id, [AccessPath.FieldAccess fld]) (Var.of_id rhs_id, [])
        in
        let newset = S.add (methname, (ph, []), loc, aliasset) (fst apair) in
        (newset, snd apair) )
    | Lfield (Var id, fld, _), Const _ ->
        let ((proc, var, _, aliasset) as targetState) =
          search_target_tuple_by_id id methname (fst apair)
        in
        let ap_containing_pvar : A.elt = find_pvar_ap_in aliasset in
        let ap_containing_pvar_updated = put_fieldname fld ap_containing_pvar in
        let aliasset_rmvd = A.remove ap_containing_pvar aliasset in
        let new_aliasset = A.add ap_containing_pvar_updated aliasset_rmvd in
        let loc = LocationSet.singleton node_loc in
        let newtuple = (proc, ap_containing_pvar_updated, loc, new_aliasset) in
        let astate_set_rmvd = S.remove targetState (fst apair) in
        let newmap = H.add_to_history (methname, ap_containing_pvar_updated) loc (snd apair) in
        if is_placeholder_vardef_ap var then
          let newset = S.add newtuple astate_set_rmvd in
          (newset, newmap)
        else
          let newset = S.add newtuple (fst apair) in
          (newset, newmap)
    | Lfield (Var id, fld, _), BinOp (_, exp2_1, exp2_2) ->
        let lhs_pvar_ap =
          search_target_tuple_by_id id methname (fst apair) |> second_of |> put_fieldname fld
        in
        let loc = LocationSet.singleton node_loc in
        let all_atomic_operands =
          List.stable_dedup @@ collect_atomic_exps exp1 @ collect_atomic_exps exp2
        in
        if has_unowned_var all_atomic_operands lhs_pvar_ap (fst apair) then
          let all_unowned_vars_updated =
            List.fold
              ~f:(fun acc exp ->
                if exp_is_var exp then
                  let ((rhs_proc, rhs_vardef, rhs_locset, rhs_aliasset) as rhs_tuple) =
                    search_target_tuple_by_id (exp_as_var exp) methname acc
                  in
                  let rhs_tuple_updated =
                    (rhs_proc, rhs_vardef, rhs_locset, A.add lhs_pvar_ap rhs_aliasset)
                  in
                  acc |> S.remove rhs_tuple |> S.add rhs_tuple_updated
                else acc )
              all_atomic_operands ~init:(fst apair)
          in
          let newtuple = (methname, lhs_pvar_ap, loc, A.singleton lhs_pvar_ap) in
          let newset = S.add newtuple all_unowned_vars_updated in
          let new_history = H.add_to_history (methname, lhs_pvar_ap) loc (snd apair) in
          (newset, new_history)
        else
          let newtuple = (methname, lhs_pvar_ap, loc, A.singleton lhs_pvar_ap) in
          let newmap = H.add_to_history (methname, lhs_pvar_ap) loc (snd apair) in
          let newset = S.add newtuple (fst apair) in
          (newset, newmap)
    | Lfield (Lvar lhs_pvar, fld, _), Var id ->
        let lhs_pvar_ap = (Var.of_pvar lhs_pvar, [AccessPath.FieldAccess fld]) in
        let loc = LocationSet.singleton node_loc in
        let rhs_pvar_tuple = search_target_tuple_by_id id methname (fst apair) in
        let newtuple =
          (methname, lhs_pvar_ap, loc, doubleton lhs_pvar_ap (second_of rhs_pvar_tuple))
        in
        let newmap = H.add_to_history (methname, lhs_pvar_ap) loc (snd apair) in
        let newset = S.add newtuple (fst apair) in
        (newset, newmap)
    | Lfield (Lvar lhs_pvar, fld, _), Lvar rhs_pvar ->
        let lhs_pvar_ap = (Var.of_pvar lhs_pvar, [AccessPath.FieldAccess fld]) in
        let rhs_pvar_ap = (Var.of_pvar rhs_pvar, []) in
        let loc = LocationSet.singleton node_loc in
        let newtuple = (methname, lhs_pvar_ap, loc, doubleton lhs_pvar_ap rhs_pvar_ap) in
        let newmap = H.add_to_history (methname, lhs_pvar_ap) loc (snd apair) in
        let newset = S.add newtuple (fst apair) in
        (newset, newmap)
    | Lfield (Lvar lhs_pvar, lhs_fld, _), Lfield (Lvar rhs_pvar, rhs_fld, _) ->
        let lhs_pvar_ap = (Var.of_pvar lhs_pvar, [AccessPath.FieldAccess lhs_fld]) in
        let rhs_pvar_ap = (Var.of_pvar rhs_pvar, [AccessPath.FieldAccess rhs_fld]) in
        let loc = LocationSet.singleton node_loc in
        let newtuple = (methname, lhs_pvar_ap, loc, doubleton lhs_pvar_ap rhs_pvar_ap) in
        let newmap = H.add_to_history (methname, lhs_pvar_ap) loc (snd apair) in
        let newset = S.add newtuple (fst apair) in
        (newset, newmap)
    (* ============ LHS is Lindex ============ *)
    | Lindex (Var lhs_id, _), Const _ -> (
        (* covers both cases where offset is either const or id *)
        let ((lhs_proc, lhs_var, lhs_loc, lhs_aliasset) as lhs_tuple) =
          search_target_tuple_by_id lhs_id methname (fst apair)
        in
        let loc = LocationSet.singleton node_loc in
        match is_irvar_ap lhs_var with
        | true ->
            apair
        | false ->
            let lhs_var_updated = put_arrayaccess lhs_var in
            let newtuple =
              ( lhs_proc
              , lhs_var_updated
              , loc
              , lhs_aliasset |> A.remove lhs_var |> A.add lhs_var_updated )
            in
            let newmap = H.add_to_history (methname, lhs_var_updated) loc (snd apair) in
            let newset = fst apair |> S.remove lhs_tuple |> S.add newtuple in
            (newset, newmap) )
    | Lindex (Var lhs_id, _), Var rhs_id -> (
        let loc = LocationSet.singleton node_loc in
        let ((lhs_proc, lhs_var, lhs_loc, lhs_aliasset) as lhs_tuple) =
          search_target_tuple_by_id lhs_id methname (fst apair)
        in
        match is_irvar_ap lhs_var with
        | true ->
            let ((rhs_proc, rhs_vardef, rhs_loc, rhs_aliasset) as rhs_tuple) =
              search_target_tuple_by_id rhs_id methname (fst apair)
            in
            let new_rhs_tuple =
              ( rhs_proc
              , rhs_vardef
              , rhs_loc
              , rhs_aliasset |> A.remove (put_arrayaccess lhs_var) |> A.add lhs_var )
            in
            let newset = fst apair |> S.remove rhs_tuple |> S.add new_rhs_tuple in
            (newset, snd apair)
        | false ->
            (* update the lhs vartuple. *)
            let lhs_var_updated = put_arrayaccess lhs_var in
            let new_lhs_aliasset = A.singleton lhs_var_updated in
            let new_tuple = (lhs_proc, lhs_var_updated, lhs_loc, new_lhs_aliasset) in
            (* find the rhs vartuple and update it. *)
            let ((rhs_proc, rhs_var, rhs_loc, rhs_aliasset) as rhs_tuple) =
              search_target_tuple_by_id rhs_id methname (fst apair)
            in
            let rhs_tuple_updated =
              (rhs_proc, rhs_var, rhs_loc, A.add lhs_var_updated rhs_aliasset)
            in
            (* update the historymap. *)
            let new_history = H.add_to_history (methname, lhs_var_updated) loc (snd apair) in
            let newset =
              fst apair |> S.remove rhs_tuple |> S.add rhs_tuple_updated |> S.add new_tuple
            in
            (newset, new_history) )
    | Lindex (Var id, _), BinOp (_, exp2_1, exp2_2) ->
        let lhs_pvar_ap =
          search_target_tuple_by_id id methname (fst apair) |> second_of |> put_arrayaccess
        in
        let loc = LocationSet.singleton node_loc in
        let all_atomic_operands =
          List.stable_dedup @@ collect_atomic_exps exp1 @ collect_atomic_exps exp2
        in
        if has_unowned_var all_atomic_operands lhs_pvar_ap (fst apair) then
          let all_unowned_vars_updated =
            List.fold
              ~f:(fun acc exp ->
                if exp_is_var exp then
                  let ((rhs_proc, rhs_vardef, rhs_locset, rhs_aliasset) as rhs_tuple) =
                    search_target_tuple_by_id (exp_as_var exp) methname acc
                  in
                  let rhs_tuple_updated =
                    (rhs_proc, rhs_vardef, rhs_locset, A.add lhs_pvar_ap rhs_aliasset)
                  in
                  acc |> S.remove rhs_tuple |> S.add rhs_tuple_updated
                else acc )
              all_atomic_operands ~init:(fst apair)
          in
          let newtuple = (methname, lhs_pvar_ap, loc, A.singleton lhs_pvar_ap) in
          let newset = S.add newtuple all_unowned_vars_updated in
          let newmap = H.add_to_history (methname, lhs_pvar_ap) loc (snd apair) in
          (newset, newmap)
        else
          let newtuple = (methname, lhs_pvar_ap, loc, A.singleton lhs_pvar_ap) in
          let newmap = H.add_to_history (methname, lhs_pvar_ap) loc (snd apair) in
          let newset = S.add newtuple (fst apair) in
          (newset, newmap)
    (* ============ Misc ============ *)
    | lhs, Cast (_, exp) ->
        (* we ignore the cast *)
        exec_store lhs exp methname apair node_loc
    | _, _ ->
        L.progress "Unsupported Store instruction %a := %a at %a@." Exp.pp exp1 Exp.pp exp2
          Procname.pp methname ;
        apair


  (** exp를 받아서 logical var로 변환한다. *)
  let convert_exp_to_logical (exp : Exp.t) =
    match exp with Var id -> id | _ -> Ident.create_none ()


  let find_actual_pvar_for_inter_id (id : Ident.t) (current_methname : Procname.t) (astate_set : S.t)
      =
    let statetups_alias_with_id = search_target_tuples_by_id id current_methname astate_set in
    (* try find_most_linenumber statetups_alias_with_id with _ -> raise FindActualPvarFailed *)
    List.hd_exn statetups_alias_with_id


  let exec_user_init_call (ret_id : Ident.t) (callee_methname : Procname.t)
      (arg_ts : (Exp.t * Typ.t) list) analyze_dependency (apair : P.t) (methname : Procname.t)
      (node_loc : Location.t) =
    (* There is at least one argument which is a non-thisvar variable *)
    let formals = get_formal_args analyze_dependency callee_methname in
    let actuals_logical_id =
      match is_inner_class_init callee_methname with
      | true -> (
        try
          arg_ts >>| (fst >> convert_exp_to_logical)
          |> List.filter ~f:(not << Ident.is_none)
          |> List.tl_exn |> List.tl_exn
        with _ -> [] )
      | false -> (
        try
          arg_ts >>| (fst >> convert_exp_to_logical)
          |> List.filter ~f:(not << Ident.is_none)
          |> List.tl_exn
        with _ -> [] )
    in
    let actual_interid_param_triples =
      let collected_triples =
        List.rev
        @@ List.foldi
             ~f:(fun index acc inter_id ->
               try
                 let actual_pvar_ap =
                   find_actual_pvar_for_inter_id inter_id methname (fst apair) |> second_of
                 in
                 let corresponding_formal = List.nth_exn formals index in
                 (actual_pvar_ap, inter_id, corresponding_formal) :: acc
               with FindActualPvarFailed | Invalid_argument _ -> acc )
             actuals_logical_id ~init:[]
      in
      match is_inner_class_init callee_methname with
      | true ->
          (* truncate as much as we can *)
          if List.is_empty collected_triples then collected_triples
          else if Int.( = ) (List.length collected_triples) 1 then collected_triples |> List.tl_exn
          else collected_triples |> List.tl_exn |> List.tl_exn
      | false ->
          if List.is_empty collected_triples then collected_triples
          else collected_triples |> List.tl_exn
    in
    (* 1. mangle callvs *)
    let callvs =
      List.init
        ~f:(fun _ -> (mk_callv callee_methname node_loc.line, []))
        (List.length actual_interid_param_triples)
    in
    (* 2. add callvs to the actual astates *)
    let astate_set_callv_added =
      List.foldi
        ~f:(fun index acc (actual, inter_id, formal) ->
          let actual_vardef_astates = search_target_tuples_by_vardef_ap actual methname acc in
          let ((proc, vardef, locset, aliasset) as most_recent_vardef_astate) =
            find_most_linenumber actual_vardef_astates
          in
          let acc_rmvd = S.remove most_recent_vardef_astate acc in
          let corresponding_callv = List.nth_exn callvs index in
          let actual_vardef_astate_updated =
            (proc, vardef, locset, aliasset |> A.add (formal, []) |> A.add corresponding_callv)
          in
          S.add actual_vardef_astate_updated acc_rmvd )
        actual_interid_param_triples ~init:(fst apair)
    in
    (* 4. create a returnv and add it to a newly made ph tuple *)
    let callv_counters = callvs >>| extract_counter_from_callv in
    let returnv = mk_returnv callee_methname callv_counters node_loc.line in
    let ph_tuple =
      ( methname
      , (placeholder_vardef methname, [])
      , LocationSet.singleton Location.dummy
      , doubleton (Var.of_id ret_id, []) (returnv, []) )
    in
    (* 5. add the ph tuple to the above astate_set *)
    let newset = S.add ph_tuple astate_set_callv_added in
    (newset, snd apair)


  let exec_lib_init_call (ret_id : Ident.t) (callee_methname : Procname.t)
      (arg_ts : (Exp.t * Typ.t) list) (apair : P.t) (methname : Procname.t) (node_loc : Location.t)
      =
    let linum = node_loc.line in
    let init_params =
      List.init ~f:(fun _ -> mk_param callee_methname linum (-1)) (List.length arg_ts)
    in
    let actuals_logical_id =
      arg_ts >>| (fst >> convert_exp_to_logical) |> List.filter ~f:(not << Ident.is_none)
    in
    let actual_interid_param_triples =
      List.tl_exn @@ List.rev
      @@ List.foldi
           ~f:(fun index acc inter_id ->
             try
               let actual_pvar_ap =
                 find_actual_pvar_for_inter_id inter_id methname (fst apair) |> second_of
               in
               let corresponding_formal = List.nth_exn init_params index in
               (actual_pvar_ap, inter_id, corresponding_formal) :: acc
             with FindActualPvarFailed -> acc )
           actuals_logical_id ~init:[]
    in
    (* 1. mangle callvs *)
    let callvs =
      List.init
        ~f:(fun _ -> (mk_callv callee_methname node_loc.line, []))
        (List.length actual_interid_param_triples)
    in
    (* 2. add callvs to the actual astates *)
    let astate_set_callv_added =
      List.foldi
        ~f:(fun index acc (actual, inter_id, formal) ->
          let actual_vardef_astates = search_target_tuples_by_vardef_ap actual methname acc in
          let ((proc, vardef, locset, aliasset) as most_recent_vardef_astate) =
            find_most_linenumber actual_vardef_astates
          in
          let acc_rmvd = S.remove most_recent_vardef_astate acc in
          let corresponding_callv = List.nth_exn callvs index in
          let actual_vardef_astate_updated =
            (proc, vardef, locset, aliasset |> A.add (formal, []) |> A.add corresponding_callv)
          in
          S.add actual_vardef_astate_updated acc_rmvd )
        actual_interid_param_triples ~init:(fst apair)
    in
    (* 4. create a returnv and add it to a newly made ph tuple *)
    let callv_counters = callvs >>| extract_counter_from_callv in
    let returnv = mk_returnv callee_methname callv_counters node_loc.line in
    let ph_tuple =
      ( methname
      , (placeholder_vardef methname, [])
      , LocationSet.singleton Location.dummy
      , doubleton (Var.of_id ret_id, []) (returnv, []) )
    in
    (* 5. add the ph tuple to the above astate_set *)
    let newset = S.add ph_tuple astate_set_callv_added in
    (newset, snd apair)


  let batch_alias_assoc (astate_set : S.t) (logicals : Ident.t list) (pvars : Pvar.t list) : S.t =
    let logicals_and_pvars =
      List.zip_exn logicals pvars
      |> List.filter ~f:(fun (logical, pvar) -> not @@ Ident.is_none logical)
      |> List.map ~f:(fun (logical, pvar) -> (Var.of_id logical, Var.of_pvar pvar))
    in
    let id_and_astates =
      List.filter ~f:(not << Ident.is_none) logicals
      >>| fun id -> (id, weak_search_target_tuple_by_id id astate_set)
    in
    let astate_tuples_to_remove = S.of_list (id_and_astates >>| snd) in
    let astate_set_rmvd = S.diff astate_set astate_tuples_to_remove in
    let update_astate (id, astate) =
      let pvar = List.Assoc.find_exn logicals_and_pvars (Var.of_id id) ~equal:Var.equal in
      let proc, vardef, loc, aliasset = astate in
      let aliasset' = A.add (pvar, []) aliasset in
      (proc, vardef, loc, aliasset')
    in
    let astate_set_updated = S.of_list (id_and_astates >>| update_astate) in
    S.union astate_set_rmvd astate_set_updated


  (** Handles calls to library APIs, whose Procdesc.t is empty *)
  let exec_lib_call (ret_id : Ident.t) (callee_methname : Procname.t)
      (arg_ts : (Exp.t * Typ.t) list) ((astate_set, histmap) : P.t) (caller_methname : Procname.t)
      (node_loc : Location.t) : P.t =
    match is_cast callee_methname with
    | true ->
        let actuals_logical_id =
          List.hd_exn
            (arg_ts >>| (fst >> convert_exp_to_logical) |> List.filter ~f:(not << Ident.is_none))
        in
        let ((actual_proc, actual_vardef, actual_loc, actual_aliasset) as actual_astate) =
          weak_search_target_tuple_by_id actuals_logical_id astate_set
        in
        let callv = mk_callv callee_methname node_loc.line in
        let callv_ap = (callv, []) in
        let param_ap = (mk_param callee_methname node_loc.line 0, []) in
        let callv_counter = extract_counter_from_callv callv_ap in
        let returnv = mk_returnv callee_methname [callv_counter] node_loc.line in
        let returnv_ap = (returnv, []) in
        let actual_astate_updated =
          ( actual_proc
          , actual_vardef
          , actual_loc
          , actual_aliasset |> A.add callv_ap |> A.add param_ap )
        in
        let cast_vardef = mk_cast_of actual_vardef caller_methname in
        let new_tuple =
          ( caller_methname
          , cast_vardef
          , LocationSet.singleton node_loc
          , A.add (Var.of_id ret_id, []) (doubleton returnv_ap cast_vardef) )
        in
        let newmap =
          H.add_to_history (caller_methname, cast_vardef) (LocationSet.singleton node_loc) histmap
        in
        let newset =
          astate_set |> S.remove actual_astate |> S.add actual_astate_updated |> S.add new_tuple
        in
        (newset, newmap)
    | false ->
        let callee_name_simple = Procname.get_method callee_methname in
        let param_indices = List.init (List.length arg_ts) ~f:Int.to_string in
        let mangles : Mangled.t list =
          param_indices
          >>| fun param_index ->
          if is_new callee_methname then
            let __new_classname = extract_classname_from_sizeof_exp @@ List.hd_exn arg_ts in
            Mangled.from_string
            @@ F.asprintf "param_%s_%s_%d_%s" callee_name_simple __new_classname node_loc.line
                 param_index
          else
            Mangled.from_string
            @@ F.asprintf "param_%s_%d_%s" callee_name_simple node_loc.line param_index
        in
        let mangled_params : Pvar.t list =
          List.map ~f:(fun mangle -> Pvar.mk mangle callee_methname) mangles
        in
        (* Associate mangled parameters and their resp. actual arguments as aliases. *)
        let actuals_logical = arg_ts >>| (fst >> convert_exp_to_logical) in
        let callvs =
          List.init (List.length actuals_logical) ~f:(fun _ ->
              mk_callv_pvar callee_methname node_loc.line )
        in
        let astate_set' =
          batch_alias_assoc astate_set actuals_logical mangled_params
          |> fun astate_set -> batch_alias_assoc astate_set actuals_logical callvs
        in
        (* We need to create a new astate (ph tuple) here *)
        let callv_counters =
          callvs >>| (fun callv -> (Var.of_pvar callv, [])) >>| extract_counter_from_callv
        in
        let returnv =
          if is_new callee_methname then
            let __new_classname = extract_classname_from_sizeof_exp @@ List.hd_exn arg_ts in
            mk_returnv_for_frontend_new callee_methname callv_counters node_loc.line
              ~classname_str:__new_classname
          else mk_returnv callee_methname callv_counters node_loc.line
        in
        let newtuple =
          ( caller_methname
          , (placeholder_vardef caller_methname, [])
          , LocationSet.singleton Location.dummy
          , doubleton (Var.of_id ret_id, []) (returnv, []) )
        in
        (S.add newtuple astate_set', histmap)


  let exec_call (ret_id : Ident.t) (callee_methname : Procname.t) (arg_ts : (Exp.t * Typ.t) list)
      analyze_dependency (apair : P.t) (methname : Procname.t) (node_loc : Location.t) : P.t =
    L.d_printfln "It's a UDF call@." ;
    let formals = get_formal_args analyze_dependency callee_methname in
    L.d_printfln "arg_ts: %a@." pp_explist (arg_ts >>| fst) ;
    let actuals_logical_id =
      arg_ts >>| (fst >> convert_exp_to_logical) |> List.filter ~f:(not << Ident.is_none)
    in
    L.d_printfln "actuals_logial_id: %a@." pp_idlist actuals_logical_id ;
    let actual_interid_param_triples =
      List.foldi
        ~f:(fun index acc inter_id ->
          try
            let actual_pvar_ap =
              find_actual_pvar_for_inter_id inter_id methname (fst apair) |> second_of
            in
            let corresponding_formal =
              if List.is_empty formals then mk_param callee_methname node_loc.line index
              else List.nth_exn formals index
            in
            (actual_pvar_ap, inter_id, corresponding_formal) :: acc
          with FindActualPvarFailed -> acc )
        actuals_logical_id ~init:[]
    in
    L.d_printfln "actual_interid_param_triples, formals: %a@." pp_varlist
      (actual_interid_param_triples >>| fun (_, _, a) -> a) ;
    (* 1. mangle callvs *)
    let callvs =
      List.init
        ~f:(fun _ -> (mk_callv callee_methname node_loc.line, []))
        (List.length actual_interid_param_triples)
    in
    (* 2. add callvs to the actual astates *)
    let astate_set_callv_added =
      List.foldi
        ~f:(fun index acc (actual, inter_id, formal) ->
          let actual_vardef_astates = search_target_tuples_by_vardef_ap actual methname acc in
          let ((proc, vardef, locset, aliasset) as most_recent_vardef_astate) =
            find_most_linenumber actual_vardef_astates
          in
          let acc_rmvd = S.remove most_recent_vardef_astate acc in
          let corresponding_callv = List.nth_exn callvs index in
          let actual_vardef_astate_updated =
            (proc, vardef, locset, aliasset |> A.add (formal, []) |> A.add corresponding_callv)
          in
          S.add actual_vardef_astate_updated acc_rmvd )
        actual_interid_param_triples ~init:(fst apair)
    in
    (* 4. create a returnv and add it to a newly made ph tuple *)
    let callv_counters = callvs >>| extract_counter_from_callv in
    let returnv = mk_returnv callee_methname callv_counters node_loc.line in
    let ph_tuple =
      match analyze_dependency callee_methname with
      | Some (_, callee_summary) ->
          let callee_ret_tuples = find_tuples_with_ret (fst callee_summary) in
          let carriedover_aps =
            List.fold
              ~f:(fun acc astate ->
                let callee_vardef, _ = second_of astate in
                if Var.is_return callee_vardef then A.add (Var.of_id ret_id, []) acc
                  (* 'return' itself should not be considered a pvar that is carrried over *)
                else A.union acc @@ doubleton (callee_vardef, []) (Var.of_id ret_id, []) )
              callee_ret_tuples ~init:A.empty
          in
          ( methname
          , (placeholder_vardef methname, [])
          , LocationSet.singleton Location.dummy
          , carriedover_aps |> A.add (Var.of_id ret_id, []) |> A.add (returnv, []) )
      | None ->
          ( methname
          , (placeholder_vardef methname, [])
          , LocationSet.singleton Location.dummy
          , doubleton (Var.of_id ret_id, []) (returnv, []) )
    in
    (* 5. add the ph tuple to the above astate_set *)
    let newset = S.add ph_tuple astate_set_callv_added in
    (newset, snd apair)


  (** Procname.Java.t를 포장한 Procname.t에서 해당 Procname.Java.t를 추출한다. *)
  let extract_java_procname (methname : Procname.t) : Procname.Java.t =
    match methname with
    | Java procname ->
        procname
    | _ ->
        L.die InternalError
          "extract_java_procname failed, methname: %a (maybe you ran this analysis on a non-Java \
           project?)@."
          Procname.pp methname


  let exec_load (id : Ident.t) (exp : Exp.t) (apair : P.t) (methname : Procname.t)
      (node_loc : Location.t) : P.t =
    let java_procname = extract_java_procname methname in
    match exp with
    | Lvar pvar -> (
      match is_formal pvar methname && (not @@ Var.is_this (Var.of_pvar pvar)) with
      | true when Procname.Java.is_autogen_method java_procname ->
          (* 그냥 ph 튜플 하나 만들고 말자 *)
          let ph = (placeholder_vardef methname, []) in
          let aliasset = doubleton (Var.of_id id, []) (Var.of_pvar pvar, []) in
          let newtuple = (methname, ph, LocationSet.singleton node_loc, aliasset) in
          let newset = S.add newtuple (fst apair) in
          (newset, snd apair)
      | true ->
          let targetTuples =
            search_target_tuples_by_vardef (Var.of_pvar pvar) methname (fst apair)
          in
          let ((proc, var, loc, aliasset) as targetTuple) = find_most_linenumber targetTuples in
          let newtuple = (proc, var, loc, A.add (Var.of_id id, []) aliasset) in
          let newstate = newtuple in
          let astate_rmvd = S.remove targetTuple (fst apair) in
          let newset = S.add newstate astate_rmvd in
          (newset, snd apair)
      | false -> (
        match search_target_tuples_by_vardef_ap (Var.of_pvar pvar, []) methname (fst apair) with
        | [] ->
            (* 한 번도 def된 적 없음 *)
            let double = doubleton (Var.of_id id, []) (Var.of_pvar pvar, []) in
            let ph = placeholder_vardef methname in
            let newtuple = (methname, (ph, []), LocationSet.singleton node_loc, double) in
            let newstate = newtuple in
            let newset = S.add newstate (fst apair) in
            (newset, snd apair)
        | h :: _ as tuples ->
            (* 이전에 def된 적 있음 *)
            let vardef_tup = second_of h in
            let most_recent_locset = H.get_most_recent_loc (methname, vardef_tup) (snd apair) in
            let ((proc, vardef, loc, aliasset) as most_recent_tuple) =
              try search_tuple_by_loc most_recent_locset tuples
              with _ ->
                (* to handle very weird corner cases
                   where Infer is analyzing a SKIP_FUNCTION *)
                search_tuple_by_loc most_recent_locset (S.elements (fst apair))
            in
            let astate_set_rmvd = S.remove most_recent_tuple (fst apair) in
            let mrt_updated = (proc, vardef, loc, A.add (Var.of_id id, []) aliasset) in
            let newset = S.add mrt_updated astate_set_rmvd in
            (newset, snd apair) ) )
    | Lfield (Var var, fld, _) -> (
        (* Find the base pvar astate. *)
        let ((rhs_base_proc, rhs_base_vardef, rhs_base_locset, rhs_base_aliasset) as rhs_base_astate)
            =
          search_target_tuple_by_id var methname (fst apair)
        in
        (* Find the base pvar + fld astate. Note: it may not exist at this point. *)
        try
          let rhs_vardef = put_fieldname fld rhs_base_vardef in
          let ((rhs_proc, rhs_vardef, rhs_locset, rhs_aliasset) as rhs_astate) =
            search_target_tuple_by_vardef_ap rhs_vardef methname (fst apair)
          in
          let rhs_astate_updated =
            (rhs_proc, rhs_vardef, rhs_locset, A.add (Var.of_id id, []) rhs_aliasset)
          in
          let newset = fst apair |> S.remove rhs_astate |> S.add rhs_astate_updated in
          (newset, snd apair)
        with SearchAstateByVardefFailed _ ->
          (* there does not exist a pvar + fld astate. We make a new one. *)
          let rhs_vardef = put_fieldname fld rhs_base_vardef in
          let new_tuple =
            (methname, rhs_vardef, rhs_base_locset, doubleton (Var.of_id id, []) rhs_vardef)
          in
          let newset = S.add new_tuple (fst apair) in
          (newset, snd apair) )
    | Lfield (Lvar pvar, fld, _) when Pvar.is_global pvar -> (
        let access_path : A.elt = (Var.of_pvar pvar, [FieldAccess fld]) in
        (* 이전에 정의된 적이 있는가 없는가로 경우 나눠야 함 (formal엔 못 옴) *)
        match search_target_tuples_by_vardef_ap access_path methname (fst apair) with
        | [] ->
            let ph = placeholder_vardef methname in
            let double = doubleton access_path (Var.of_id id, []) in
            let newtuple = (methname, (ph, []), LocationSet.singleton Location.dummy, double) in
            let newset = S.add newtuple (fst apair) in
            (newset, snd apair)
        | h :: _ as tuples ->
            let var, fldlst = second_of h in
            let most_recent_loc = H.get_most_recent_loc (methname, (var, fldlst)) (snd apair) in
            let ((proc, vardef, loc, aliasset) as most_recent_tuple) =
              search_astate_by_loc most_recent_loc tuples
            in
            let astate_set_rmvd = S.remove most_recent_tuple (fst apair) in
            let mra_updated = (proc, vardef, loc, A.add (Var.of_id id, []) aliasset) in
            let double = doubleton (Var.of_id id, []) (Var.of_pvar pvar, fldlst) in
            let ph = placeholder_vardef methname in
            let newstate = (methname, (ph, []), LocationSet.singleton Location.dummy, double) in
            let newset = S.add mra_updated astate_set_rmvd |> S.add newstate in
            (newset, snd apair) )
    | Lindex (Var var, _) -> (
        (* Var[const or Var] *)
        let access_path : A.elt = (Var.of_id var, [ArrayAccess (Typ.void_star, [])]) in
        (* 이전에 정의된 적이 있는가 없는가로 경우 나눠야 함 (formal엔 못 옴) *)
        match search_target_tuples_by_vardef_ap access_path methname (fst apair) with
        | [] ->
            let ph = placeholder_vardef methname in
            let double = doubleton access_path (Var.of_id id, []) in
            let newtuple = (methname, (ph, []), LocationSet.singleton Location.dummy, double) in
            let newset = S.add newtuple (fst apair) in
            (newset, snd apair)
        | _ ->
            L.die InternalError "exec_load failed, id: %a, exp: %a, astate_set: %a, methname: %a"
              Ident.pp id Exp.pp exp S.pp (fst apair) Procname.pp methname )
    | Var _ ->
        (* 아직은 버리는 케이스만 있으니 e.g. _=*n$9 *)
        apair
    | _ ->
        L.progress "Unsupported Load Instruction %a := %a at %a@." Ident.pp id Exp.pp exp
          Procname.pp methname ;
        apair


  (** register tuples for formal arguments before a procedure starts. *)
  let register_formals (apair : P.t) cfg_node methname : P.t =
    let node = CFG.Node.underlying_node cfg_node in
    match Procdesc.Node.get_kind node with
    | Start_node ->
        let formals = get_my_formal_args methname in
        let formal_aps = List.map ~f:(fun var -> (var, [])) formals in
        let proc = Procdesc.Node.get_proc_name node in
        let loc = LocationSet.singleton @@ Procdesc.Node.get_loc node in
        let bake_newstate (var_ap : MyAccessPath.t) = (proc, var_ap, loc, A.singleton var_ap) in
        let tuplelist = List.map ~f:bake_newstate formal_aps in
        let tupleset = S.of_list tuplelist in
        let formal_aps_with_methname = List.map ~f:(fun tup -> (methname, tup)) formal_aps in
        let newmap = H.batch_add_to_history formal_aps_with_methname loc (snd apair) in
        let newset = S.union (fst apair) tupleset in
        (newset, newmap)
    | _ ->
        apair


  let collect_call_instrs (pdesc : Procdesc.t) : Sil.instr list =
    let nodes = Procdesc.get_nodes pdesc in
    List.map ~f:Procdesc.Node.get_instrs nodes
    |> List.map ~f:Instrs.get_underlying_not_reversed
    |> List.map ~f:Array.to_list |> List.concat |> List.filter ~f:is_call


  let exec_instr (prev' : P.t)
      {InterproceduralAnalysis.proc_desc; InterproceduralAnalysis.analyze_dependency}
      (node : CFG.Node.t) (instr : Sil.instr) : P.t =
    let methname = node |> CFG.Node.underlying_node |> Procdesc.Node.get_proc_name in
    let node_loc = CFG.Node.loc node in
    let prev = register_formals prev' node methname in
    match instr with
    | Load {id; e= exp} ->
        exec_load id exp prev methname node_loc
    | Store {e1= exp1; e2= exp2} ->
        exec_store exp1 exp2 methname prev node_loc
    | Prune _ ->
        prev
    | Call ((ret_id, _), e_fun, arg_ts, _, _) -> (
      match e_fun with
      | Const (Cfun callee_methname) -> (
        match is_initializer callee_methname with
        | true ->
            if Option.is_some @@ Procdesc.load callee_methname then
              exec_user_init_call ret_id callee_methname arg_ts analyze_dependency prev methname
                node_loc
            else exec_lib_init_call ret_id callee_methname arg_ts prev methname node_loc
        | false ->
            if Option.is_some @@ Procdesc.load callee_methname then
              exec_call ret_id callee_methname arg_ts analyze_dependency prev methname node_loc
            else exec_lib_call ret_id callee_methname arg_ts prev methname node_loc )
      | _ ->
          L.die InternalError "exec_call failed, ret_id: %a, e_fun: %a astate_set: %a, methname: %a"
            Ident.pp ret_id Exp.pp e_fun S.pp (fst prev) Procname.pp methname )
    | Metadata _ ->
        prev


  let pp_session_name node fmt = F.fprintf fmt "def/loc/alias %a" CFG.Node.pp_id (CFG.Node.id node)
end

module CFG = ProcCfg.OneInstrPerNode (ProcCfg.Normal)
module Analyzer = AbstractInterpreter.MakeRPO (TransferFunctions (CFG))

(** Postcondition computing function *)
let checker ({InterproceduralAnalysis.proc_desc} as analysis_data) =
  Analyzer.compute_post analysis_data ~initial:DefLocAliasDomain.initial proc_desc
