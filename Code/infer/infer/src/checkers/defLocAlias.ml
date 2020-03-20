open! IStd

(** Interproceural Liveness Checker. *)

exception UndefinedSemantics
exception IDontKnow
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

  let history = Hashtbl.create 123456

  let add_to_history (key:Var.t) (value:Location.t)= Hashtbl.add history key value

  let get_most_recent_loc (value:Var.t) = Hashtbl.find history value

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

  let most_recent_tuple (pv:Var.t) = Hashtbl.find history pv

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
            with _ -> (* search_target_tuples_by_pvar failed: the pvar_var is not redefined in the procedure *)
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
            add_to_history pvar_var loc; S.add newstate astate_rmvd 
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
        (* sanity check: check if the vardef is ph *)
        let pvar_var = Var.of_pvar pv in
        let loc = CFG.Node.loc node in
        let aliasset_new = A.add pvar_var aliasset in
        let newstate = 
          if not (Var.equal vardef (placeholder_vardef methname))
          then (procname, pvar_var, loc, aliasset_new)
          else (procname, vardef, loc, aliasset_new) in
        let astate_rmvd = S.remove targetTuple astate in
        add_to_history pvar_var loc; S.add newstate astate_rmvd
    | Lvar pv, BinOp (_, Var _, Const _) | Lvar pv, BinOp (_, Const _, Var _) -> (* This id does not belong to pvar *)
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
        add_to_history pvar_var loc; S.add newstate astate_rmvd
    | Lvar pv, BinOp (_, Const _, Const _) ->
        let pvar_var = Var.of_pvar pv in
        let loc = CFG.Node.loc node in
        let aliasset_new = A.singleton pvar_var in
        let newstate = (methname, pvar_var, loc, aliasset_new) in
        add_to_history pvar_var loc; S.add newstate astate
    | _, _ -> raise NotSupported


  let exec_call (ret_id:Ident.t) (e_fun:Exp.t) (arg_ts:(Exp.t*Typ.t) list) (summary:Summary.t) (node:CFG.Node.t) (prev:S.t) =
    let _ = List.map ~f:(fun ((e,_):Exp.t*Typ.t) -> L.progress "parameters of %a: (%a, sometype)\n" Exp.pp e_fun Exp.pp e) arg_ts in
    let callee_methname =
      match e_fun with
      | Const (Cfun fn) -> fn
      | _ -> raise NoMethname in
    match Payload.read ~caller_summary:summary ~callee_pname:callee_methname with
    | Some summ -> 
        let targetTuples = find_tuple_with_ret summ callee_methname in
        begin match List.length targetTuples with
        | 0 -> (* the variable being returned has not been redefined in callee, create a new def *)
            let methname = node |> CFG.Node.underlying_node |> Procdesc.Node.get_proc_name in
            let ph = placeholder_vardef (methname) in
            let logicalvar = Var.of_id ret_id in
            let newstate = (methname, ph, Location.dummy, A.singleton logicalvar) in
            S.add newstate prev
        | _ -> (* the variable being returned has been redefined in callee, carry that def over *)
            let update_summ_tuples = fun (procname,vardef,location,aliasset) -> (procname,vardef,location,A.add (Var.of_id ret_id) (A.filter is_logical_var aliasset)) in
            let targetTuples_set = (List.map ~f:update_summ_tuples targetTuples) |> S.of_list in
            S.union prev targetTuples_set end
    | None -> prev


  let exec_instr : S.t -> extras ProcData.t -> CFG.Node.t -> Sil.instr -> S.t = fun prev {summary} node instr ->
    match instr with
    | Sil.Load {id=id; e=exp} when is_pvar_expr exp ->
          let pvar = extract_pvar exp in
          let double = D.doubleton (Var.of_id id) (Var.of_pvar pvar) in
          let methname = node |> CFG.Node.underlying_node |> Procdesc.Node.get_proc_name in
          let ph = placeholder_vardef methname in
          let newstate = (methname, ph, Location.dummy, double) in
          S.add newstate prev
    | Sil.Load _ -> (* Complex things are not supported at this point *) prev 
    | Sil.Store {e1=exp1; e2=exp2} ->
        let methname = node |> CFG.Node.underlying_node |> Procdesc.Node.get_proc_name in
        exec_store exp1 exp2 methname prev node
    | Sil.Prune _ -> prev
    | Sil.Call ((ret_id, _), e_fun, arg_ts, _, _) -> exec_call ret_id e_fun arg_ts summary node prev
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
