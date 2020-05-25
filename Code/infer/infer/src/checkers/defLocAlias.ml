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

module S = DefLocAliasDomain.AbstractState
module A = DefLocAliasDomain.SetofAliases

module Payload = SummaryPayload.Make (struct
    type t = DefLocAliasDomain.t
    let field = Payloads.Fields.def_loc_alias
  end)


module TransferFunctions = struct
  module CFG = ProcCfg.OneInstrPerNode (ProcCfg.Exceptional)
  module Domain = S
  type extras = ProcData.no_extras
  type instr = Sil.instr

  (** Pair of Procname.t and MyAccessPath.t *)
  module ProcAccess = struct
    type t = Procname.t * MyAccessPath.t [@@deriving compare]
    let pp fmt (proc, ap) = F.fprintf fmt "(%a, %a)" Procname.pp proc MyAccessPath.pp ap
  end

  module HistoryMap = PrettyPrintable.MakePPMap (ProcAccess)

  let history = ref HistoryMap.empty


  let add_to_history (key:Procname.t * MyAccessPath.t) (value:Location.t) = history := HistoryMap.add key value !history


  let batch_add_to_history (keys:(Procname.t * MyAccessPath.t) list) (loc:Location.t) = List.iter ~f:(fun h -> add_to_history h loc) keys


  let get_most_recent_loc (key:Procname.t * MyAccessPath.t) = HistoryMap.find key !history


  (** specially mangled variable to mark a value as returned from callee *)
  let mk_returnv procname = Pvar.mk (Mangled.from_string "returnv") procname |> Var.of_pvar


  let rec extract_nonthisvar_from_args methname (arg_ts:(Exp.t*Typ.t) list) (astate:S.t) : Exp.t list =
    match arg_ts with
    | [] -> []
    | (Var var as v, _)::t ->
        let (_, _, _, aliasset) = search_target_tuple_by_id var methname astate in
        if not (A.exists is_this_ap aliasset)
        then v::extract_nonthisvar_from_args methname t astate
        else extract_nonthisvar_from_args methname t astate
    | (other, _)::t -> other::extract_nonthisvar_from_args methname t astate


  let leave_only_var_tuples (ziplist:(Exp.t*Var.t) list) =
    let leave_logical = fun (x,_) -> is_logical_var_expr x in
    let map_func = function (Exp.Var id, var) -> (Var.of_id id, var) | (_, _) -> L.die InternalError "Exp not a Var" in
    List.filter ~f:leave_logical ziplist |> List.map ~f:map_func


(** id를 토대로 가장 최근의 non-ph 튜플을 찾아내고, 없으면 raise *)
let search_recent_vardef (methname:Procname.t) (pvar:Var.t) (astate:S.t) =
  let elements = S.elements astate in
  let rec search_recent_vardef_inner methname id tuplelist =
    match tuplelist with
    | [] -> L.die InternalError "searching most recent vardef failed"
    | (proc, (var, _),  loc, aliasset) as targetTuple::t ->
        (* L.progress "methname: %a, searching: %a, loc: %a, proc: %a\n" Procname.pp methname Var.pp var Location.pp loc Procname.pp proc; *)
        let proc_cond = Procname.equal proc methname in
        let id_cond = A.mem (id, []) aliasset in
        let var_cond = not @@ Var.equal var (placeholder_vardef proc) in
        if var_cond then 
        (let most_recent_loc = get_most_recent_loc (methname, (var, [])) in
        let loc_cond = Location.equal most_recent_loc loc in
        if proc_cond && id_cond && loc_cond then
        targetTuple else search_recent_vardef_inner methname id t)
        else search_recent_vardef_inner methname id t in
  search_recent_vardef_inner methname pvar elements


  (** given a doubleton set of lv and pv, extract the pv. *)
  let rec extract_another_pvar (id:Ident.t) (varsetlist:A.t list) : Var.t =
    match varsetlist with
    | [] -> L.die InternalError "extract_another_pvar failed"
    | set::t ->
        if Int.equal (A.cardinal set) 2 && A.mem (Var.of_id id, []) set
        then
          begin match set |> A.remove (Var.of_id id, []) |> A.elements with
            | [(x, _)] -> x
            | _ -> L.die InternalError "extract_another_pvar failed" end
        else extract_another_pvar id t


(** Takes an actual(logical)-formal binding list and adds the formals to the respective pvar tuples of the actual arguments *)
  let rec add_bindings_to_alias_of_tuples (methname:Procname.t) bindinglist (actualtuples:S.elt list) =
    match bindinglist with
    | [] -> []
    | (actualvar, formalvar)::tl ->
        begin match actualvar with
        | Var.LogicalVar vl ->
            (* L.progress "Processing (%a, %a)\n" Var.pp actualvar Var.pp formalvar; *)
            (* L.progress "methname: %a, id: %a\n" Procname.pp methname Ident.pp vl; *)
            (* L.progress "Astate before death: @.%a@." S.pp (S.of_list actualtuples); *)
            let actual_pvar, _ = second_of @@ weak_search_target_tuple_by_id vl (S.of_list actualtuples) in
            (* possibly various definitions of the pvar in question. *)
            let candTuples = 
            (* L.progress "methname: %a, var: %a\n" Procname.pp methname Var.pp actual_pvar;  *)
            search_target_tuples_by_vardef actual_pvar methname (S.of_list actualtuples) in
            (* the most recent one among the definitions. *)
            let most_recent_loc = get_most_recent_loc (methname, (actual_pvar, [])) in
            let (proc,var,loc,aliasset') = search_tuple_by_loc most_recent_loc candTuples in
            let newTuple = (proc, var, loc, A.add (formalvar, []) aliasset') in
            newTuple::add_bindings_to_alias_of_tuples methname tl actualtuples
        | Var.ProgramVar _ -> L.die InternalError "add_bindings_to_alias_of_tuples failed"
        end


  let triple_equal = fun (proc1, var1, loc1) (proc2, var2, loc2) -> Procname.equal proc1 proc2 && Var.equal var1 var2 && Location.equal loc1 loc2


  (** astate로부터 (procname, vardef) 쌍을 중복 없이 만든다. *)
  let get_keys astate =
    let elements = S.elements astate in
    let rec enum_nodup (tuplelist:S.elt list) (current:(Procname.t*Var.t*Location.t) list) =
      match tuplelist with
      | [] -> current
      | (a,(b, _),c,_)::t ->
        if not (List.mem current (a,b,c) ~equal:triple_equal) && not (Var.equal b (placeholder_vardef a) || Var.is_this b)
          then enum_nodup t ((a,b,c)::current)
          else enum_nodup t current in
    enum_nodup elements []


  (** 실행이 끝난 astate에서 중복된 튜플들 (proc과 vardef가 같음)끼리 묶여 있는 list of list를 만든다. *)
  let group_by_duplicates (astate:S.t) : S.elt list list = 
    let keys = get_keys astate in
    let rec get_tuple_by_key tuplelist key =
      match tuplelist with
      | [] -> []
      | (proc,(name, _), loc,_) as targetTuple::t ->
          if triple_equal key (proc, name, loc)
          then ((*L.progress "generating key: %a, targetTuple: %a\n" Var.pp name QuadrupleWithPP.pp targetTuple;*) targetTuple::get_tuple_by_key t key) 
          else get_tuple_by_key t key in
    let get_tuples_by_keys tuplelist keys = List.map ~f:(get_tuple_by_key tuplelist) keys in
    let elements = S.elements astate in
    get_tuples_by_keys elements keys


  let duplicated_times (var:Var.t) (lst:S.elt list) =
    let rec duplicated_times_inner (var:Var.t) (current_line:int) (current_time:int) (lst:S.elt list) =
      match lst with
      | [] -> (*L.progress "dup time: %d\n" current_time;*) current_time
      | (_, (vardef, _), loc, _)::t ->
          if Var.equal var vardef
          then (if Int.equal loc.line current_line
                then duplicated_times_inner var current_line (current_time+1) t
                else duplicated_times_inner var current_line current_time t)
          else duplicated_times_inner var current_line current_time t in
    let first_loc : Location.t = third_of @@ List.nth_exn lst 0 in
    duplicated_times_inner var first_loc.line 0 lst

  
  (** group_by_duplicates가 만든 list of list를 받아서, duplicate된 변수 list를 반환하되, ph와 this는 무시한다. *)
  let rec collect_duplicates (listlist:S.elt list list) : S.elt list list =
    match listlist with
    | [] -> []
    | lst::t ->
        let sample_tuple = List.nth_exn lst 0 in
        (*L.progress "sample tuple: %a\n" QuadrupleWithPP.pp sample_tuple;*)
        let current_var, _ = second_of sample_tuple in
        if not @@ is_placeholder_vardef current_var && not @@ Var.is_this current_var
        then (if duplicated_times current_var lst >= 2
              then lst::collect_duplicates t
              else collect_duplicates t)
        else collect_duplicates t


  (** callee가 return c;꼴로 끝날 경우 새로 튜플을 만들고 alias set에 c를 추가 *)
  let variable_carryover astate callee_methname ret_id methname summ_read =
    let calleeTuples = find_tuple_with_ret summ_read callee_methname in
    (** 콜리 튜플 하나에 대해, 튜플 하나를 새로 만들어 alias set에 추가 *)
    let carryfunc tup =
      let ph = placeholder_vardef methname in
      let callee_vardef, _ = second_of tup in
      (* 여기서 returnv를 집어넣자 *)
      let aliasset = A.add (mk_returnv callee_methname, []) @@ doubleton (callee_vardef, []) (Var.of_id ret_id, []) in
      (methname, (ph, []),  Location.dummy, aliasset) in
    let carriedover = List.map calleeTuples ~f:carryfunc |> S.of_list in
    S.union astate carriedover


  (** 변수가 리턴된다면 그걸 alias set에 넣는다 (variable carryover) *)
  let apply_summary astate caller_summary callee_methname ret_id caller_methname : S.t =
    match Payload.read_full ~caller_summary:caller_summary ~callee_pname:callee_methname with
    | Some (_, summ) -> (*L.progress "Applying summary of %a\n" Procname.pp (Procdesc.get_proc_name pdesc);*)
        variable_carryover astate callee_methname ret_id caller_methname summ
    | None -> 
        (* Nothing to carry over! -> just make a ph tuple and end *)
        let ph = (placeholder_vardef caller_methname, []) in
        let loc = Location.dummy in
        let alias = A.singleton (Var.of_id ret_id, []) in
        let newtuple = (caller_methname, ph, loc, alias) in
        S.add newtuple astate


  let rec zip (l1:'a list) (l2:'b list) =
    match l1, l2 with
    | [], [] -> []
    | h1::t1, h2::t2 -> (h1, h2)::zip t1 t2
    | _, _ -> L.die InternalError "Zip error"


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


  let merge_ph_tuples (tup1:QuadrupleWithPP.t) (tup2:QuadrupleWithPP.t) (location:Location.t) : S.elt =
    let proc1, _, _, alias1 = tup1 in
    let proc2, _, _, alias2 = tup2 in
    let pvar_vardef = find_another_pvar_vardef alias2 in
    if not @@ Procname.equal proc1 proc2 then L.die InternalError "Merging two tuples from different procedures";
    let aliasset = A.add pvar_vardef @@ A.union alias1 alias2 in
    (proc1, pvar_vardef, location, aliasset)


  let exec_store (exp1:Exp.t) (exp2:Exp.t) (methname:Procname.t) (astate:S.t) (node:CFG.Node.t) : S.t =
    match exp1, exp2 with
    | Lvar pv, Var id ->
        begin match Var.is_return (Var.of_pvar pv) with
        | true -> (* A variable is being returned *)
            let (_, _, _, aliasset) as targetTuple =
              try weak_search_target_tuple_by_id id astate
              with _ ->
                  ((*L.progress "=== Search Failed (1): Astate before search_target_tuple at %a := %a === @.:%a@." Exp.pp exp1 Exp.pp exp2 S.pp astate ;*) bottuple) in
            begin try
            let pvar_var, _ = A.find_first is_program_var_ap aliasset in
            let most_recent_loc = get_most_recent_loc (methname, (pvar_var, [])) in
              let candTuples = search_target_tuples_by_vardef pvar_var methname astate in
              let (proc,var,loc,aliasset') as candTuple = search_tuple_by_loc most_recent_loc candTuples in
              let astate_rmvd = S.remove candTuple astate in
              let logicalvar = Var.of_id id in
              let programvar = Var.of_pvar pv in
              let newstate = (proc,var,loc,A.union aliasset' (doubleton (logicalvar, []) (programvar, []))) in
              S.add newstate astate_rmvd
            with _ -> (* the pvar_var is not redefined in the procedure. *)
              S.remove targetTuple astate end
        | false -> (* An ordinary variable assignment. *)
            let targetTuple =
              begin try weak_search_target_tuple_by_id id astate
              with _ -> ((*L.progress "id: %a" Ident.pp id ; L.progress "=== Search Failed (2): Astate before search_target_tuple at %a := %a === @.:%a@." Exp.pp exp1 Exp.pp exp2 S.pp astate ;*) bottuple) end in
            let aliasset = fourth_of targetTuple in
            let pvar_var = Var.of_pvar pv in
            let loc = CFG.Node.loc node in
            let aliasset_new = A.add (pvar_var, []) aliasset in
            let newstate = (methname, (pvar_var, []),  loc, aliasset_new) in
            let astate_rmvd = S.remove targetTuple astate in
            add_to_history (methname, (pvar_var, [])) loc;
            if is_placeholder_vardef_ap (second_of targetTuple)
            then S.add newstate astate_rmvd
            else S.add newstate astate
        end
    | Lvar pv, Const _ when (Var.is_return (Var.of_pvar pv)) -> astate
    | Lvar pv, Const _ ->
        let pvar_var = Var.of_pvar pv in
        let loc = CFG.Node.loc node in
        let aliasset_new = A.singleton (pvar_var, []) in
        let newstate = (methname, (pvar_var, []), loc, aliasset_new) in
        add_to_history (methname, (pvar_var, [])) loc; S.add newstate astate
    | Lvar pv, BinOp (_, Var id, Const _) | Lvar pv, BinOp (_, Const _, Var id) when is_mine id pv methname astate ->
        let (procname, (vardef, _),  _, aliasset) as targetTuple = search_target_tuple_by_id id methname astate in
        let pvar_var = Var.of_pvar pv in
        let loc = CFG.Node.loc node in
        let aliasset_new = A.add (pvar_var, []) aliasset in
          if not (is_placeholder_vardef vardef)
          then let newstate = (procname, (vardef, []), loc, aliasset_new) in
               add_to_history (methname, (pvar_var, [])) loc;
               S.add newstate astate
          else let newstate = (procname, (vardef, []), loc, aliasset_new) in
               let astate_rmvd = S.remove targetTuple astate in
               add_to_history (methname, (pvar_var, [])) loc;
               S.add newstate astate_rmvd
    | Lvar pv, BinOp (_, Var _, Const _) | Lvar pv, BinOp (_, Const _, Var _) -> (* This id does not belong to pvar. *)
        let pvar_var = Var.of_pvar pv in
        let loc = CFG.Node.loc node in
        let aliasset_new = A.singleton (pvar_var, []) in
        let newstate = (methname, (pvar_var, []), loc, aliasset_new) in
        add_to_history (methname, (pvar_var, [])) loc;
        L.progress "added pvar_var: %a\n" Var.pp pvar_var;
        (* L.progress "current map: %a\n" (HistoryMap.pp ~pp_value:Location.pp) !history; *)
        S.add newstate astate
    | Lvar pv, BinOp (_, Var id1, Var id2) when not (is_mine id1 pv methname astate && is_mine id2 pv methname astate) ->
        let targetTuple1 = search_target_tuple_by_id id1 methname astate in
        let targetTuple2 = search_target_tuple_by_id id2 methname astate in
        let astate_rmvd = astate |> S.remove targetTuple1 |> S.remove targetTuple2 in
        let pvar_var = Var.of_pvar pv in
        let loc = CFG.Node.loc node in
        let aliasset_new = A.singleton (pvar_var, []) in
        let newstate = (methname, (pvar_var, []), loc, aliasset_new) in
        add_to_history (methname, (pvar_var, [])) loc;
        (* L.progress "added pvar_var: %a\n" Var.pp pvar_var; *)
        (* L.progress "current map: %a\n" (HistoryMap.pp ~pp_value:Location.pp) !history; *)
        S.add newstate astate_rmvd
    | Lvar pv, BinOp (_, Const _, Const _) ->
        let pvar_var = Var.of_pvar pv in
        let loc = CFG.Node.loc node in
        let aliasset_new = A.singleton (pvar_var, []) in
        let newstate = (methname, (pvar_var, []), loc, aliasset_new) in
        add_to_history (methname, (pvar_var, [])) loc;
        (* L.progress "added pvar_var: %a\n" Var.pp pvar_var; *)
        S.add newstate astate
    | Lfield (Var id1, fld, _), Var id2 ->
        (* finding the pvar tuple getting stored *)
        let (proc1, var1, loc1, aliasset) as vartuple = search_target_tuple_by_id id1 methname astate in
        let pvar_tuple : A.elt = begin try
            find_another_pvar_vardef aliasset
          with _ -> (* oops, long access path *)
            let vartuple2 = search_target_tuple_by_id id2 methname astate in
            let aliasset = fourth_of vartuple2 in
            find_another_pvar_vardef aliasset end in
        let pvar_tuple_updated = put_fieldname fld pvar_tuple in
        let new_aliasset = A.add pvar_tuple_updated @@ A.remove pvar_tuple aliasset in
        let newtuple = (proc1, var1, loc1, new_aliasset) in
        (* L.d_printfln "newtuple: %a@." QuadrupleWithPP.pp newtuple; *)
        (* finding the var tuple holding the value being stored *)
        L.d_printfln "finding for: %a@." Ident.pp id2;
        let another_tuple = search_target_tuple_by_id id2 methname astate in
        (* L.d_printfln "another_tuple: %a@." QuadrupleWithPP.pp another_tuple; *)
        let loc = CFG.Node.loc node in
        let merged_tuple =
            merge_ph_tuples another_tuple newtuple loc
        in
        (* L.progress "merged: %a@." QuadrupleWithPP.pp merged_tuple; *)
        let astate_rmvd = S.remove another_tuple @@ S.remove vartuple astate in
        let old_location = third_of newtuple in
        add_to_history (methname, pvar_tuple_updated) loc;
        if Location.equal old_location Location.dummy
        then S.add merged_tuple astate_rmvd
        else S.add vartuple @@ S.add merged_tuple astate_rmvd 
    | Lindex (Var id, _), Const _ -> (* covers both cases where offset is either const or id *)
        let (proc, _, _, aliasset) as targetTuple = search_target_tuple_by_id id methname astate in
        let (var, aplist) as ap_containing_pvar = find_pvar_ap_in aliasset in
        let ap_containing_pvar_updated = (var, aplist@[AccessPath.ArrayAccess (Typ.void_star, [])]) in
        let aliasset_rmvd = A.remove ap_containing_pvar aliasset in
        let new_aliasset = A.add ap_containing_pvar_updated aliasset_rmvd in
        let loc = CFG.Node.loc node in
        let newtuple = (proc, ap_containing_pvar_updated, loc, new_aliasset) in
        let astate_rmvd = S.remove targetTuple astate in
        add_to_history (methname, ap_containing_pvar_updated) loc;
        S.add newtuple astate_rmvd
    | Lfield (Var id, fld, _), Const _ ->
        let (proc, var, _, aliasset) as targetTuple = search_target_tuple_by_id id methname astate in
        let ap_containing_pvar : A.elt = find_pvar_ap_in aliasset in
        let ap_containing_pvar_updated = put_fieldname fld ap_containing_pvar in
        let aliasset_rmvd = A.remove ap_containing_pvar aliasset in
        let new_aliasset = A.add ap_containing_pvar_updated aliasset_rmvd in
        let loc = CFG.Node.loc node in
        let newtuple = (proc, ap_containing_pvar_updated, loc, new_aliasset) in
        let astate_rmvd = S.remove targetTuple astate in
        add_to_history (methname, ap_containing_pvar_updated) loc;
        if is_placeholder_vardef_ap var
        then S.add newtuple astate_rmvd
        else S.add newtuple astate
    | Lindex (Var id1, _), Var id2 ->
        (* finding the pvar tuple getting stored *)
        let (proc1, var1, loc1, aliasset) as vartuple = search_target_tuple_by_id id1 methname astate in
        let pvar_tuple : A.elt = begin try
            find_another_pvar_vardef aliasset
          with _ -> (* oops, long access path *)
            let vartuple2 = search_target_tuple_by_id id2 methname astate in
            let aliasset = fourth_of vartuple2 in
            find_another_pvar_vardef aliasset end in
        let pvar_tuple_updated = put_arrayaccess pvar_tuple in
        let new_aliasset = A.add pvar_tuple_updated @@ A.remove pvar_tuple aliasset in
        let newtuple = (proc1, var1, loc1, new_aliasset) in
        (* L.d_printfln "newtuple: %a@." QuadrupleWithPP.pp newtuple; *)
        (* finding the var tuple holding the value being stored *)
        let another_tuple = search_target_tuple_by_id id2 methname astate in
        (* L.d_printfln "another_tuple: %a@." QuadrupleWithPP.pp another_tuple; *)
        let loc = CFG.Node.loc node in
        let merged_tuple =
            merge_ph_tuples another_tuple newtuple loc
        in
        (* L.progress "merged: %a@." QuadrupleWithPP.pp merged_tuple; *)
        let astate_rmvd = S.remove another_tuple @@ S.remove vartuple astate in
        let old_location = third_of newtuple in
        add_to_history (methname, pvar_tuple_updated) loc;
        if Location.equal old_location Location.dummy
        then S.add merged_tuple astate_rmvd
        else S.add vartuple @@ S.add merged_tuple astate_rmvd 
    | Lvar pvar, Exn _ when Var.is_return (Var.of_pvar pvar) -> 
        L.progress "Storing an Exception@."; astate
    | Lfield (Lvar pvar, fld, _), Const _ ->
        let pvar_ap = (Var.of_pvar pvar, [AccessPath.FieldAccess fld]) in
        let loc = CFG.Node.loc node in
        let aliasset_new = A.singleton pvar_ap in
        let newstate = (methname, pvar_ap, loc, aliasset_new) in
        add_to_history (methname, pvar_ap) loc;
        S.add newstate astate 
    | Lfield (Lvar pvar, fld, _), Var id ->
        let targetTuple =
          begin try weak_search_target_tuple_by_id id astate
          with _ -> bottuple end in
        let aliasset = fourth_of targetTuple in
        let pvar_var = Var.of_pvar pvar in
        let loc = CFG.Node.loc node in
        let new_pvar_ap = put_fieldname fld (pvar_var, []) in
        let aliasset_new = A.add new_pvar_ap aliasset in
        let newstate = (methname, new_pvar_ap, loc, aliasset_new) in
        let astate_rmvd = S.remove targetTuple astate in
        add_to_history (methname, new_pvar_ap) loc;
        S.add newstate astate_rmvd
    | _, _ ->
        L.progress "Unsupported Store instruction %a := %a@." Exp.pp exp1 Exp.pp exp2; astate


  let exec_call (ret_id:Ident.t) (e_fun:Exp.t) (arg_ts:(Exp.t*Typ.t) list) (caller_summary:Summary.t) (astate:S.t) (methname:Procname.t) =
    let callee_methname =
      match e_fun with
      | Const (Cfun fn) -> fn
      | _ -> L.die InternalError "failed to find callee's methname" in
    match input_is_void_type arg_ts astate with
    | true -> (* All Arguments are Just Constants: just apply the summary, make a new tuple and end *)
        let astate_summary_applied = apply_summary astate caller_summary callee_methname ret_id methname in
        let aliasset = A.add (mk_returnv callee_methname, []) @@ A.singleton (Var.of_id ret_id, []) in
        let newstate = (methname, (placeholder_vardef methname, []), Location.dummy, aliasset) in
        S.add newstate astate_summary_applied
    | false -> (* There is at least one argument which is a non-thisvar variable *)
        begin try
            let astate_summary_applied = apply_summary astate caller_summary callee_methname ret_id methname in
            let formals = get_formal_args caller_summary callee_methname |> List.filter ~f:(fun x -> not @@ Var.is_this x) in
            begin match formals with
              | [] -> (* Callee in Native Code! *)
                  L.d_printfln "maybe cast?";
                  astate_summary_applied
              | _ ->  (* Callee in User Code! *)
                  let actuals_logical = extract_nonthisvar_from_args methname arg_ts astate_summary_applied in
                  let actuallog_formal_binding = leave_only_var_tuples @@ zip actuals_logical formals in
                  (* pvar tuples transmitted as actual arguments *)
                  let actuals_pvar_tuples =
                    actuals_logical |> List.filter ~f:is_logical_var_expr |> List.map ~f:(function
                        | Exp.Var id ->
                            (* L.progress "id: %a, processing: %a@." Ident.pp id S.pp astate; *)
                            let pvar = search_target_tuples_by_id id methname astate |> List.map ~f:fourth_of |> extract_another_pvar id in (* 여기가 문제 *)
                            search_recent_vardef methname pvar astate
                        | _ -> L.die InternalError "actuals should be logical vars") in
                  let actualpvar_alias_added = add_bindings_to_alias_of_tuples methname actuallog_formal_binding actuals_pvar_tuples |> S.of_list in
                  let applied_state_rmvd = S.diff astate_summary_applied (S.of_list actuals_pvar_tuples) in
                  S.union applied_state_rmvd actualpvar_alias_added end
          with _ -> (* corner case: maybe one of actuals contains literal null *)
            astate end



  let exec_load (id:Ident.t) (exp:Exp.t) (astate:S.t) (methname:Procname.t) =
    match exp with
    | Lvar pvar ->
        begin match is_formal pvar methname && not @@ Var.is_this (Var.of_pvar pvar) with
          | true ->
              let targetTuples = search_target_tuples_by_vardef (Var.of_pvar pvar) methname astate in
              let (proc, var, loc, aliasset) as targetTuple = find_least_linenumber targetTuples in
              let newtuple = (proc, var, loc, A.add (Var.of_id id, []) aliasset) in
              let astate_rmvd = S.remove targetTuple astate in
              S.add newtuple astate_rmvd
          | false ->
              if Pvar.is_global pvar then L.progress "it's a global!@.";
              begin match search_target_tuples_by_vardef (Var.of_pvar pvar) methname astate with
                  | [] -> (* 한 번도 def된 적 없음 *)
                        let double = doubleton (Var.of_id id, []) (Var.of_pvar pvar, []) in
                        let ph = placeholder_vardef methname in
                        let newstate = (methname, (ph, []), Location.dummy, double) in
                        S.add newstate astate
                  | h::_ as tuples -> (* 이전에 def된 적 있음 *)
                        let var, _ = second_of h in
                        L.d_printfln "finding var:%a\n" Var.pp var;
                          let most_recent_loc = get_most_recent_loc (methname, (var, [])) in
                        L.d_printfln "methname: %a, most_recent_loc: %a@." Procname.pp methname Location.pp most_recent_loc;
                        (* L.progress "astate: %a@." S.pp astate; *)
                        let (proc, vardef, loc, aliasset) as most_recent_tuple = search_tuple_by_loc most_recent_loc tuples in
                        let astate_rmvd = S.remove most_recent_tuple astate in
                        let mrt_updated = (proc, vardef, loc, A.add (Var.of_id id, []) aliasset) in
                        let double = doubleton (Var.of_id id, []) (Var.of_pvar pvar, []) in
                        let ph = placeholder_vardef methname in
                        let newstate = (methname, (ph, []), Location.dummy, double) in
                        S.add mrt_updated astate_rmvd |> S.add newstate
              end
        end
    | Lfield (Var var, fld, _) -> 
        let access_path : A.elt = (Var.of_id var, [FieldAccess fld]) in
        (* 이전에 정의된 적이 있는가 없는가로 경우 나눠야 함 (formal엔 못 옴) *)
        begin match search_target_tuples_by_vardef_ap (access_path) methname astate with
          | [] ->
              let ph = placeholder_vardef methname in
              let double = doubleton access_path (Var.of_id id, []) in
              let newstate = (methname, (ph, []), Location.dummy, double) in
              S.add newstate astate
          | _ -> L.die InternalError "Not Implemented 1"
        end
    | Lfield (Lvar pvar, fld, _) when Pvar.is_global pvar ->
        let access_path : A.elt = (Var.of_pvar pvar, [FieldAccess fld]) in
        (* 이전에 정의된 적이 있는가 없는가로 경우 나눠야 함 (formal엔 못 옴) *)
        begin match search_target_tuples_by_vardef_ap (access_path) methname astate with
          | [] ->
              let ph = placeholder_vardef methname in
              let double = doubleton access_path (Var.of_id id, []) in
              let newstate = (methname, (ph, []), Location.dummy, double) in
              S.add newstate astate
          | h::_ as tuples ->
              let var, fldlst = second_of h in
              let most_recent_loc = get_most_recent_loc (methname, (var, fldlst)) in
              let (proc, vardef, loc, aliasset) as most_recent_tuple = search_tuple_by_loc most_recent_loc tuples in
              let astate_rmvd = S.remove most_recent_tuple astate in
              let mrt_updated = (proc, vardef, loc, A.add (Var.of_id id, []) aliasset) in
              let double = doubleton (Var.of_id id, []) (Var.of_pvar pvar, fldlst) in
              let ph = placeholder_vardef methname in
              let newstate = (methname, (ph, []), Location.dummy, double) in
              S.add mrt_updated astate_rmvd |> S.add newstate
          end
    | Lindex (Var var, _) -> (* Var[const or Var] *)
        let access_path : A.elt = (Var.of_id var, [ArrayAccess (Typ.void_star, [])]) in
        (* 이전에 정의된 적이 있는가 없는가로 경우 나눠야 함 (formal엔 못 옴) *)
        begin match search_target_tuples_by_vardef_ap (access_path) methname astate with
          | [] ->
              let ph = placeholder_vardef methname in
              let double = doubleton access_path (Var.of_id id, []) in
              let newstate = (methname, (ph, []), Location.dummy, double) in
              S.add newstate astate
          | _ -> L.die InternalError "Not Implemented 3"
        end
    | Var _ -> (* 아직은 버리는 케이스만 있으니 e.g. _=*n$9 *)
        astate
    | _ -> L.progress "Unsupported Load Instruction %a := %a@." Ident.pp id Exp.pp exp; astate


  (** register tuples for formal arguments before a procedure starts. *)
  let register_formals astate cfg_node methname =
    let node = CFG.Node.underlying_node cfg_node in
    match Procdesc.Node.get_kind node with
    | Start_node ->
        let formals = get_my_formal_args methname in
        let formal_aps = List.map ~f:(fun var -> (methname, (var, []))) formals in 
        let proc = Procdesc.Node.get_proc_name node in
        let targetloc = Procdesc.Node.get_loc node in
        (* 파라미터 라인넘버 보정 *)
        let loc = {Location.line=targetloc.line-1; Location.col=targetloc.col; Location.file=targetloc.file} in
        let bake_newtuple = fun (var:Var.t) -> (proc, (var, []), loc, A.singleton (var, [])) in
        let tuplelist = List.map ~f:bake_newtuple formals in
        let tupleset = S.of_list tuplelist in
        batch_add_to_history formal_aps loc ; S.union astate tupleset
    | _ -> astate


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
  let all_proc_and_astates_opt = List.map ~f:(fun (proc, summ) -> (proc, Payload.of_summary summ)) all_proc_and_summaries in
  let all_proc_and_astates = catMaybes_tuplist all_proc_and_astates_opt in
  List.iter ~f:(fun (proc, astate) -> Hashtbl.add hashtbl proc astate) all_proc_and_astates


let exec_metadata (md:Sil.instr_metadata) (astate:S.t) =
  match md with
  | ExitScope _ -> (* S.filter (fun tup ->
       * not @@ Var.is_this @@ second_of tup &&
       * not @@ is_placeholder_vardef @@ second_of tup) *) astate
  | _ -> astate


  let exec_instr : S.t -> extras ProcData.t -> CFG.Node.t -> Sil.instr -> S.t = fun prev' {summary} node instr ->
    (* L.progress "Executing instr: %a\n" (Sil.pp_instr ~print_types:true Pp.text) instr; *)
    let my_summary = summary in
    let methname = node |> CFG.Node.underlying_node |> Procdesc.Node.get_proc_name in
    let prev = register_formals prev' node methname in
    (* let prev = prev' in *)
      match instr with
      | Sil.Load {id=id; e=exp} ->
          exec_load id exp prev methname
      | Sil.Store {e1=exp1; e2=exp2} ->
          exec_store exp1 exp2 methname prev node
      | Sil.Prune _ -> prev
      | Sil.Call ((ret_id, _), e_fun, arg_ts, _, _) ->
          exec_call ret_id e_fun arg_ts my_summary prev methname
      | Sil.Metadata md -> exec_metadata md prev


  let leq ~lhs:_ ~rhs:_ = S.subset


  let join = S.union


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
