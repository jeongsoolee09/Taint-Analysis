open! IStd

(** Interproceural Liveness Checker. *)

exception UndefinedSemantics1
exception UndefinedSemantics2
exception IDontKnow
exception IDontKnow2
exception NoMatch
exception NoMatch1
exception NoMatch2
exception NoMatch3
exception NoMatch4
exception NoMatch5
exception CannotExtractPvar
exception NotSupported
exception NoMethname
exception VarDefNotPH 
exception UnexpectedArg
exception NotImplemented
exception LengthError1
exception LengthError2
exception NoSummary

module L = Logging
module F = Format
module Hashtbl = Caml.Hashtbl

module D = DefLocAliasDomain
module S = DefLocAliasDomain.AbstractState
module A = DefLocAliasDomain.SetofAliases

module Payload = SummaryPayload.Make (struct
    type t = D.t
    let field = Payloads.Fields.def_loc_alias
  end)

module TransferFunctions = struct
  module CFG = ProcCfg.OneInstrPerNode (ProcCfg.Exceptional)
  module Domain = S
  type extras = ProcData.no_extras
  type instr = Sil.instr


  let history = Hashtbl.create 777


  let add_to_history (key:Var.t) (value:Location.t)= Hashtbl.add history key value


  let get_most_recent_loc (key:Var.t) = Hashtbl.find history key


  let (>>) f g = fun x -> g (f x)


  let is_pvar_expr (exp:Exp.t) : bool =
    match exp with
    | Lvar _ -> true
    | _ -> false


  let is_logical_var_expr (exp:Exp.t) : bool =
    match exp with
    | Var _ -> true
    | _ -> false


  let is_constant_expr (exp:Exp.t) : bool =
    match exp with
    | Const _ -> true
    | _ -> false


  let extract_pvar (exp:Exp.t) : Pvar.t =
    match exp with
    | Lvar pv -> pv
    | _ -> raise CannotExtractPvar


  let placeholder_vardef (pid:Procname.t) : Var.t =
    let mangled = Mangled.from_string "ph" in
    let ph_vardef = Pvar.mk mangled pid in
    Var.of_pvar ph_vardef


  let is_logical_var (var:Var.t) : bool =
    match var with
    | LogicalVar _ -> true
    | ProgramVar _ -> false


  let is_program_var (var:Var.t) : bool =
    match var with
    | LogicalVar _ -> false
    | ProgramVar _ -> true


  let rec search_target_tuple_by_id_inner id (methname:Procname.t) elements = 
    match elements with
    | [] -> raise NoMatch
    | ((procname, _, _, aliasset) as target)::t ->
        if Procname.equal procname methname && A.mem id aliasset then target else search_target_tuple_by_id_inner id methname t


  let search_target_tuple_by_id (id:Ident.t) (methname:Procname.t) (tupleset:S.t)=
    let elements = S.elements tupleset in
    search_target_tuple_by_id_inner (Var.of_id id) methname elements


  let rec weak_search_target_tuple_by_id_inner id elements = 
    match elements with
    | [] -> raise NoMatch1
    | ((_, _, _, aliasset) as target)::t ->
        if A.mem id aliasset then target else weak_search_target_tuple_by_id_inner id t


  let weak_search_target_tuple_by_id (id:Ident.t) (tupleset:S.t)=
    let elements = S.elements tupleset in
    weak_search_target_tuple_by_id_inner (Var.of_id id) elements


  let rec search_target_tuples_by_id_inner id (methname:Procname.t) elements acc = 
    match elements with
    | [] -> acc
    | ((procname, _, _, aliasset) as target)::t ->
        if Procname.equal procname methname && A.mem id aliasset
        then search_target_tuples_by_id_inner id methname t (target::acc)
        else search_target_tuples_by_id_inner id methname t acc


  let search_target_tuples_by_id (id:Ident.t) (methname:Procname.t) (tupleset:S.t) =
    let elements = S.elements tupleset in
    let result = search_target_tuples_by_id_inner (Var.of_id id) methname elements [] in
    if Int.equal (List.length result) 0 then raise NoMatch2 else result 


  (* There is an alias set which contains both id and pvar <-> id belongs to pvar, because ids never get reused *)
  let is_mine id pvar methname astate =
    try
      let (_, _, _, aliasset) = search_target_tuple_by_id id methname astate in
      A.mem (Var.of_id id) aliasset && A.mem (Var.of_pvar pvar) aliasset
    with NoMatch3 ->
      false


  let rec search_target_tuples_by_pvar_inner pv (methname:Procname.t) elements acc = 
    match elements with
    | [] -> acc
    | ((procname, vardef, _, _) as target)::t ->
        if Procname.equal procname methname && Var.equal vardef pv
        then search_target_tuples_by_pvar_inner pv methname t (target::acc)
        else search_target_tuples_by_pvar_inner pv methname t acc


  let search_target_tuples_by_pvar (pv:Var.t) (methname:Procname.t) (tupleset:S.t) =
    let elements = S.elements tupleset in
    let result = search_target_tuples_by_pvar_inner pv methname elements [] in
    if Int.equal (List.length result) 0 then raise NoMatch4 else result 


  let rec search_tuple_by_loc (loc:Location.t) (tuplelist:S.elt list) =
    match tuplelist with
    | [] -> raise NoMatch5
    | ((_,_,l,_) as target)::t ->
        if Location.equal loc l
        then target
        else search_tuple_by_loc loc t


  let rec find_tuple_with_ret_inner (tuplelist:S.elt list) (methname:Procname.t) (acc:S.elt list) =
    match tuplelist with
    | [] -> acc
    | (procname, _, _, aliasset) as target :: t ->
        if Procname.equal procname methname && A.exists Var.is_return aliasset (* short-circuit! *)
        then find_tuple_with_ret_inner t methname (target::acc)
        else find_tuple_with_ret_inner t methname acc


  let find_tuple_with_ret (tupleset:S.t) (methname:Procname.t) =
    let elements = S.elements tupleset in
    find_tuple_with_ret_inner elements methname []


  let input_is_void_type (arg_ts:(Exp.t*Typ.t) list) (astate:S.t) : bool =
    match arg_ts with
    | [] -> false
    | (Var var, _)::[] ->
        let (_, vardef, _, _) = weak_search_target_tuple_by_id var astate in
          if Var.is_this vardef
          then true
          else false
    | (Var _, _)::_ -> false
    | (_, _)::_ -> raise UnexpectedArg (* shouldn't actual args be all pure logical vars? *)


  let rec extract_nonthisvar_from_args methname (arg_ts:(Exp.t*Typ.t) list) (astate:S.t) : Var.t list =
    match arg_ts with
    | [] -> []
    | (Var var, _)::t ->
        let (_, _, _, aliasset) = search_target_tuple_by_id var methname  astate in
        if not (A.exists Var.is_this aliasset)
        then Var.of_id var::extract_nonthisvar_from_args methname t astate
        else extract_nonthisvar_from_args methname t astate
    | (_, _)::_ -> raise UnexpectedArg (* shouldn't actual args be all pure logical vars? *)


(** Takes an actual(logical)-formal binding list and adds the formals to the respective pvar tuples of the actual arguments *)
  let rec add_bindings_to_alias_of_tuples (methname:Procname.t) bindinglist (actualtuples:S.elt list) =
    match bindinglist with
      | [] -> []
      | (actualvar, formalvar)::tl ->
          begin match actualvar with
            | Var.LogicalVar vl ->
                let (proc, var, loc, alias) = weak_search_target_tuple_by_id vl (S.of_list actualtuples) in
                let newTuple = (proc, var, loc, A.add formalvar alias) in
                newTuple::add_bindings_to_alias_of_tuples methname tl actualtuples
            | Var.ProgramVar _ -> raise UndefinedSemantics1
            end


  let rec add_var_to_aliasset (tuplelist:S.elt list) (vars:Var.t list) : S.elt list =
    match tuplelist, vars with
    | [], [] -> []
    | (proc,vardef,loc,aliasset)::t1, var::t2 ->
        (proc,vardef,loc,A.add var aliasset)::add_var_to_aliasset t1 t2
    | _, _ -> raise LengthError1


  let get_summary_for (procname:Procname.t) =
    match Summary.OnDisk.get procname with
    | Some summary -> summary
    | None -> raise IDontKnow2


  let apply_summary astate caller_summary callee_methname node ret_id =
    match Payload.read ~caller_summary:caller_summary ~callee_pname:callee_methname with
    | Some summ ->
    (*     let callee_summary = get_summary_for callee_methname in
      * L.progress "callee summary: %a" Summary.pp_text callee_summary; *)
        let targetTuples = find_tuple_with_ret summ callee_methname in
        begin match List.length targetTuples with
        | 0 -> (* the variable being returned has not been redefined in callee, create a new def *)
            let methname = node |> CFG.Node.underlying_node |> Procdesc.Node.get_proc_name in
            let ph = placeholder_vardef methname in
            let logicalvar = Var.of_id ret_id in
            let newstate = (methname, ph, Location.dummy, A.singleton logicalvar) in
            S.add newstate astate
        | _ -> (* the variable being returned has been redefined in callee, carry that def over *)
            let update_summ_tuples = fun (procname,vardef,location,aliasset) -> (procname,vardef,location,A.add (Var.of_id ret_id) (A.filter is_logical_var aliasset)) in
            let targetTuples_set = (List.map ~f:update_summ_tuples targetTuples) |> S.of_list in
            S.union astate targetTuples_set end
    | None -> astate


  let rec zip (l1:'a list) (l2: 'b list) =
    match l1, l2 with
    | [], [] -> []
    | h1::t1, h2::t2 -> (h1, h2)::zip t1 t2
    | _, _ -> raise LengthError2


  let convert_from_mangled : Procname.t -> (Mangled.t*Typ.t) -> Var.t = fun methname (m,_) -> Pvar.mk m methname |> Var.of_pvar


  let extract_ident (v:Var.t) =
    match v with
    | Var.LogicalVar id -> id
    | Var.ProgramVar _ -> raise UnexpectedArg


  let get_formal_args (caller_procname:Procname.t) (caller_summary:Summary.t) (callee_pname:Procname.t) : Var.t list =
    L.progress "%a 's callee: %a\n" Procname.pp caller_procname Procname.pp callee_pname ;
      match Payload.read_full ~caller_summary:caller_summary ~callee_pname:callee_pname with
      | Some (procdesc, _) -> Procdesc.get_formals procdesc |> List.map ~f:(convert_from_mangled caller_procname)
      | None -> (* Oops, it's a native code outside our focus *) []


  let exec_store (exp1:Exp.t) (exp2:Exp.t) (methname:Procname.t) (astate:S.t) (node:CFG.Node.t) : S.t =
    match exp1, exp2 with
    | Lvar pv, Var id ->
        begin match Var.is_return (Var.of_pvar pv) with
        | true -> (* A variable is being returned *)
            let (_, _, _, aliasset) as targetTuple =
              try weak_search_target_tuple_by_id id astate
              with _ ->
                  (L.progress "==== Search Failed (1): Astate before search_target_tuple at %a := %a ==== @.:%a@." Exp.pp exp1 Exp.pp exp2 S.pp astate ; D.bottuple) in
            let pvar_var = A.find_first is_program_var aliasset in
            let most_recent_loc = get_most_recent_loc pvar_var in
            begin try
              let candTuples = search_target_tuples_by_pvar pvar_var methname astate in
              let (proc,var,loc,aliasset') as candTuple = search_tuple_by_loc most_recent_loc candTuples in
              let astate_rmvd = S.remove candTuple astate in
              let logicalvar = Var.of_id id in
              let programvar = Var.of_pvar pv in
              let newstate = (proc,var,loc,A.union aliasset' (A.singleton logicalvar |> A.add programvar)) in
              S.add newstate astate_rmvd
            with _ -> (* search_target_tuples_by_pvar failed: the pvar_var is not redefined in the procedure. *)
                S.remove targetTuple astate end
        | false -> (* An ordinary variable assignment. *)
            let (methname_old, vardef, _, aliasset) as targetTuple =
              try weak_search_target_tuple_by_id id astate
              with _ -> (L.progress "id: %a" Ident.pp id ; L.progress "==== Search Failed (3): Astate before search_target_tuple at %a := %a ==== @.:%a@." Exp.pp exp1 Exp.pp exp2 S.pp astate ; D.bottuple) in
            let pvar_var = Var.of_pvar pv in
            let loc = CFG.Node.loc node in
            let aliasset_new = A.add pvar_var aliasset in
            let newstate =
              if Var.equal vardef (placeholder_vardef methname)
                  (* Simple Variable Assignment. *)
                then (methname, pvar_var, loc, aliasset_new)
                  (* Previous Variable Definition Carryover. *)
                else (methname_old, vardef, loc, aliasset_new) in
            let astate_rmvd = S.remove targetTuple astate in
            add_to_history pvar_var loc;
            S.add newstate astate_rmvd
        end
    | Lvar pv, Const _ when (Var.is_return (Var.of_pvar pv)) -> astate
    | Lvar pv, Const _ ->
        let pvar_var = Var.of_pvar pv in
        let loc = CFG.Node.loc node in
        let aliasset_new = A.singleton pvar_var in
        let newstate = (methname, pvar_var, loc, aliasset_new) in
        add_to_history pvar_var loc; S.add newstate astate
    | Lvar pv, BinOp (_, Var id, Const _) | Lvar pv, BinOp (_, Const _, Var id) when is_mine id pv methname astate ->
        let (procname, vardef, _, aliasset) as targetTuple = search_target_tuple_by_id id methname astate in
        let pvar_var = Var.of_pvar pv in
        let loc = CFG.Node.loc node in
        let aliasset_new = A.add pvar_var aliasset in
        let newstate = 
          (* sanity check: check if the vardef is ph *)
          if not (Var.equal vardef (placeholder_vardef methname))
          then (procname, pvar_var, loc, aliasset_new)
          else (procname, vardef, loc, aliasset_new) in
        let astate_rmvd = S.remove targetTuple astate in
        add_to_history pvar_var loc;
        S.add newstate astate_rmvd
    | Lvar pv, BinOp (_, Var _, Const _) | Lvar pv, BinOp (_, Const _, Var _) -> (* This id does not belong to pvar. *)
        let pvar_var = Var.of_pvar pv in
        let loc = CFG.Node.loc node in
        let aliasset_new = A.singleton pvar_var in
        let newstate = (methname, pvar_var, loc, aliasset_new) in
        add_to_history pvar_var loc; S.add newstate astate 
    | Lvar pv, BinOp (_, Var id1, Var id2) when not (is_mine id1 pv methname astate && is_mine id2 pv methname astate) ->
        let targetTuple1 = search_target_tuple_by_id id1 methname astate in
        let targetTuple2 = search_target_tuple_by_id id2 methname astate in
        let astate_rmvd = astate |> S.remove targetTuple1 |> S.remove targetTuple2 in
        let pvar_var = Var.of_pvar pv in
        let loc = CFG.Node.loc node in
        let aliasset_new = A.singleton pvar_var in
        let newstate = (methname, pvar_var, loc, aliasset_new) in
        add_to_history pvar_var loc;
        S.add newstate astate_rmvd
    | Lvar pv, BinOp (_, Const _, Const _) ->
        let pvar_var = Var.of_pvar pv in
        let loc = CFG.Node.loc node in
        let aliasset_new = A.singleton pvar_var in
        let newstate = (methname, pvar_var, loc, aliasset_new) in
        add_to_history pvar_var loc;
        S.add newstate astate
    | _, _ -> raise NotSupported


  let exec_call (ret_id:Ident.t) (e_fun:Exp.t) (arg_ts:(Exp.t*Typ.t) list) (caller_summary:Summary.t) (node:CFG.Node.t) (astate:S.t) (methname:Procname.t) =
    (* let _ = List.map ~f:(fun ((e,_):Exp.t*Typ.t) -> L.progress "parameters of %a: (%a, sometype)\n" Exp.pp e_fun Exp.pp e) arg_ts in *)
    (* let _ = L.progress "caller summary: %a\n" Summary.pp_text caller_summary in *)
    let callee_methname =
      match e_fun with
      | Const (Cfun fn) -> fn
      | _ -> raise NoMethname in
    match input_is_void_type arg_ts astate with
    | true -> (* All Arguments are Just Constants: just apply the summary and end *)
        apply_summary astate caller_summary callee_methname node ret_id
    | false -> (* There is at least one argument which is a non-thisvar variable *)
        (* 외과수술 집도할 곳 *)
        let astate_summary_applied =
              apply_summary astate caller_summary callee_methname node ret_id
        in
        let actuals_logical = extract_nonthisvar_from_args methname arg_ts astate_summary_applied in
        let formals = get_formal_args methname caller_summary callee_methname |> List.filter ~f:(fun x -> Var.is_this x |> not) in
        (* let _ = List.map ~f:(L.progress "actual: %a\n" Var.pp) actuals_logical in
         * let _ = List.map ~f:(L.progress "formal: (%a, sometype)\n" Var.pp) formals in *)
        let actuallog_formal_binding = zip actuals_logical formals in
        let actuals_pvar_tuples = List.map ~f:(function
            | Var.LogicalVar id -> search_target_tuple_by_id id methname astate 
            | Var.ProgramVar _ -> raise UndefinedSemantics2) actuals_logical in
        let actualpvar_alias_added = try add_bindings_to_alias_of_tuples methname actuallog_formal_binding actuals_pvar_tuples |> S.of_list with _ -> raise IDontKnow in
        let applied_state_rmvd = S.diff astate_summary_applied actualpvar_alias_added in
        S.union applied_state_rmvd actualpvar_alias_added


  let exec_instr : S.t -> extras ProcData.t -> CFG.Node.t -> Sil.instr -> S.t = fun prev {summary} node instr ->
    let my_summary = summary in
    match instr with
    | Sil.Load {id=id; e=exp} when is_pvar_expr exp ->
          let pvar = extract_pvar exp in
          let double = D.doubleton (Var.of_id id) (Var.of_pvar pvar) in
          let methname = node |> CFG.Node.underlying_node |> Procdesc.Node.get_proc_name in
          let ph = placeholder_vardef methname in
          let newstate = (methname, ph, Location.dummy, double) in
          S.add newstate prev
    | Sil.Load _ -> prev (* Complex things are not supported at this point *)
    | Sil.Store {e1=exp1; e2=exp2} ->
        let methname = node |> CFG.Node.underlying_node |> Procdesc.Node.get_proc_name in
        exec_store exp1 exp2 methname prev node
    | Sil.Prune _ -> prev
    | Sil.Call ((ret_id, _), e_fun, arg_ts, _, _) ->
        let methname = node |> CFG.Node.underlying_node |> Procdesc.Node.get_proc_name in
        exec_call ret_id e_fun arg_ts my_summary node prev methname
    | Sil.Metadata _ -> prev


  let leq ~lhs:_ ~rhs:_ = S.subset


  let join = S.union


  let widen ~prev:prev ~next:next ~num_iters:_ = join prev next


  let pp_session_name node fmt = Format.fprintf fmt "def/loc/alias %a" CFG.Node.pp_id (CFG.Node.id node)

end




module Analyzer = AbstractInterpreter.MakeRPO (TransferFunctions)

let checker {Callbacks.summary=summary; exe_env} : Summary.t =
  let proc_name = Summary.get_proc_name summary in
  let tenv = Exe_env.get_tenv exe_env proc_name in
  match Analyzer.compute_post (ProcData.make_default summary tenv) ~initial:DefLocAliasDomain.initial with
  | Some post ->
      Payload.update_summary post summary
  | None -> raise IDontKnow
