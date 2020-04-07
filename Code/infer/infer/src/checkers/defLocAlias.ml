open! IStd

(** Interprocedural Liveness Checker with alias relations in mind. *)

exception UndefinedSemantics1
exception UndefinedSemantics2
exception UndefinedSemantics3
exception UndefinedSemantics4
exception UndefinedSemantics5
exception IDontKnow
exception NoMatch
exception NoMatch1
exception NoMatch2
exception NoMatch3
exception NoMatch4
exception NoMatch5
exception NoSummary
exception NotSupported
exception NoMethname
exception UnexpectedArg1
exception UnexpectedArg2
exception UnexpectedArg3
exception NotImplemented
exception LengthError1
exception LengthError2

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

  let ( >> ) f g = fun x -> g (f x)

  let history = Hashtbl.create 777


  let add_to_history (key:Var.t) (value:Location.t)= Hashtbl.add history key value


  let get_most_recent_loc (key:Var.t) = Hashtbl.find history key


  let first_of (a,_,_,_) = a

  let second_of (_,b,_,_) = b

  let third_of (_,_,c,_) = c

  let fourth_of (_,_,_,d) = d


  let is_pvar_expr (exp:Exp.t) : bool =
    match exp with
    | Lvar _ -> true
    | _ -> false


  let is_logical_var_expr (exp:Exp.t) : bool =
    match exp with
    | Var _ -> true
    | _ -> false


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


  let rec search_target_tuple_by_pvar_inner pvar (methname:Procname.t) elements = 
    match elements with
    | [] -> raise NoMatch
    | ((procname, _, _, aliasset) as target)::t ->
        if Procname.equal procname methname && A.mem pvar aliasset then target else search_target_tuple_by_pvar_inner pvar methname t


  let search_target_tuple_by_pvar (pvar:Var.t) (methname:Procname.t) (tupleset:S.t) =
    let elements = S.elements tupleset in
    search_target_tuple_by_pvar_inner pvar methname elements


  (* 위 함수의 리스트 버전 *)
  let rec search_target_tuples_by_pvar_inner pvar (methname:Procname.t) elements = 
    match elements with
    | [] -> []
    | ((procname, _, _, aliasset) as target)::t ->
        if Procname.equal procname methname && A.mem pvar aliasset
        then target::search_target_tuples_by_pvar_inner pvar methname t
        else search_target_tuples_by_pvar_inner pvar methname t


  let search_target_tuples_by_pvar (pvar:Var.t) (methname:Procname.t) (tupleset:S.t) =
    let elements = S.elements tupleset in
    search_target_tuples_by_pvar_inner pvar methname elements


  let rec search_target_tuple_by_id_inner id (methname:Procname.t) elements = 
    match elements with
    | [] -> raise NoMatch
    | ((procname, _, _, aliasset) as target)::t ->
        if Procname.equal procname methname && A.mem id aliasset then target else search_target_tuple_by_id_inner id methname t


  let search_target_tuple_by_id (id:Ident.t) (methname:Procname.t) (tupleset:S.t) =
    let elements = S.elements tupleset in
    search_target_tuple_by_id_inner (Var.of_id id) methname elements


  let rec weak_search_target_tuple_by_id_inner (id:Var.t) (elements:S.elt list) = 
    match elements with
    | [] -> raise NoMatch1
    | ((_, _, _, aliasset) as target)::t ->
        if A.mem id aliasset then target else weak_search_target_tuple_by_id_inner id t


  let weak_search_target_tuple_by_id (id:Ident.t) (tupleset:S.t) =
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
    search_target_tuples_by_id_inner (Var.of_id id) methname elements []


  (* There is an alias set which contains both id and pvar <-> id belongs to pvar, because ids never get reused *)
  let is_mine id pvar methname astate =
    try
      let (_, _, _, aliasset) = search_target_tuple_by_id id methname astate in
      A.mem (Var.of_id id) aliasset && A.mem (Var.of_pvar pvar) aliasset
    with NoMatch3 ->
      false


  let rec search_target_tuples_by_vardef_inner pv (methname:Procname.t) elements acc = 
    match elements with
    | [] -> acc
    | ((procname, vardef, _, _) as target)::t ->
        if Procname.equal procname methname && Var.equal vardef pv
        then search_target_tuples_by_vardef_inner pv methname t (target::acc)
        else search_target_tuples_by_vardef_inner pv methname t acc


  let search_target_tuples_by_vardef (pv:Var.t) (methname:Procname.t) (tupleset:S.t) =
    let elements = S.elements tupleset in
    let result = search_target_tuples_by_vardef_inner pv methname elements [] in
    if Int.equal (List.length result) 0 then raise NoMatch4 else result 


  let rec search_tuple_by_loc (loc:Location.t) (tuplelist:S.elt list) =
    match tuplelist with
    | [] -> raise NoMatch5
    | ((_,_,l,_) as target)::t ->
        if Location.equal loc l
        then target
        else search_tuple_by_loc loc t


  let rec search_recent_vardef_inner methname id tuplelist =
    match tuplelist with
    | [] -> raise IDontKnow
    | (proc, var, loc, aliasset) as targetTuple::t ->
        L.progress "methname: %a, searching: %a, loc: %a, proc: %a\n" Procname.pp methname Var.pp var Location.pp loc Procname.pp proc;
        let proc_cond = Procname.equal proc methname in
        let id_cond = A.mem id aliasset in
        let var_cond = not @@ Var.equal var (placeholder_vardef proc) in
        if var_cond then 
        (let most_recent_loc = get_most_recent_loc var in
        let loc_cond = Location.equal most_recent_loc loc in
        if proc_cond && id_cond && loc_cond then
        targetTuple else search_recent_vardef_inner methname id t)
        else search_recent_vardef_inner methname id t


  (** id를 토대로 가장 최근의 non-ph 튜플을 찾아내고, 없으면 raise *)
  let search_recent_vardef (methname:Procname.t) (pvar:Var.t) (astate:S.t) =
    let elements = S.elements astate in
    search_recent_vardef_inner methname pvar elements


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
        begin try
          let (_, vardef, _, _) =
                weak_search_target_tuple_by_id var astate
          in
          if Var.is_this vardef then true else false
          with _ -> (* it's a constructor or something abnormal: We give up soundness *)
              true end
    | (Var _, _)::_ -> false
    | (Lvar _, _)::_ -> raise UnexpectedArg1 (* shouldn't all non-constant actual args be pure logical vars? *)
    | (_, _)::_ -> false


  let rec extract_nonthisvar_from_args methname (arg_ts:(Exp.t*Typ.t) list) (astate:S.t) : Exp.t list =
    match arg_ts with
    | [] -> []
    | (Var var as v, _)::t ->
        let (_, _, _, aliasset) = search_target_tuple_by_id var methname astate in
        if not (A.exists Var.is_this aliasset)
        then v::extract_nonthisvar_from_args methname t astate
        else extract_nonthisvar_from_args methname t astate
    | (other, _)::t -> other::extract_nonthisvar_from_args methname t astate


  let leave_only_var_tuples (ziplist:(Exp.t*Var.t) list) =
    let leave_logical = fun (x,_) -> is_logical_var_expr x in
    let map_func = function (Exp.Var id, var) -> (Var.of_id id, var) | (_, _) -> raise UndefinedSemantics4 in
    List.filter ~f:leave_logical ziplist |> List.map ~f:map_func


  (** given a doubleton set of lv and pv, extract the pv. *)
  let rec extract_another_pvar (id:Ident.t) (varsetlist:A.t list) : Var.t =
    match varsetlist with
    | [] -> raise UndefinedSemantics5
    | set::t ->
        if Int.equal (A.cardinal set) 2 && A.mem (Var.of_id id) set
        then
          begin match set |> A.remove (Var.of_id id) |> A.elements with
            | [x] -> x
            | _ -> raise UndefinedSemantics5 end
        else extract_another_pvar id t


(** Takes an actual(logical)-formal binding list and adds the formals to the respective pvar tuples of the actual arguments *)
  let rec add_bindings_to_alias_of_tuples (methname:Procname.t) bindinglist (actualtuples:S.elt list) =
    match bindinglist with
    | [] -> []
    | (actualvar, formalvar)::tl ->
        begin match actualvar with
        | Var.LogicalVar vl ->
            L.progress "Processing (%a, %a)\n" Var.pp actualvar Var.pp formalvar;
            L.progress "methname: %a, id: %a\n" Procname.pp methname Ident.pp vl;
            L.progress "Astate before death: @.:%a@." S.pp (S.of_list actualtuples);
            let actual_pvar = second_of @@ weak_search_target_tuple_by_id vl (S.of_list actualtuples) in
            (* possibly various definitions of the pvar in question. *)
            let candTuples = 
            L.progress "methname: %a, var: %a\n" Procname.pp methname Var.pp actual_pvar; 
            search_target_tuples_by_vardef actual_pvar methname (S.of_list actualtuples) 
            in
            (* the most recent one among the definitions. *)
            let most_recent_loc = get_most_recent_loc actual_pvar in
            let (proc,var,loc,aliasset') = search_tuple_by_loc most_recent_loc candTuples in
            let newTuple = (proc, var, loc, A.add formalvar aliasset') in
            newTuple::add_bindings_to_alias_of_tuples methname tl actualtuples
        | Var.ProgramVar _ -> raise UndefinedSemantics1
        end


  let is_placeholder_vardef (var:Var.t) =
    match var with
    | LogicalVar _ -> false
    | ProgramVar pv -> String.equal (Pvar.to_string pv) "ph"


  let garbage_collect astate = S.filter (fun (_,x,_,_) -> is_placeholder_vardef x) astate


  let double_equal = fun (proc1, var1) (proc2, var2) -> Procname.equal proc1 proc2 && Var.equal var1 var2


  (** astate로부터 (procname, vardef) 쌍을 중복 없이 만든다. *)
  let get_keys astate =
    let elements = S.elements astate in
    let rec enum_nodup (tuplelist:S.elt list) (current:(Procname.t*Var.t) list) =
      match tuplelist with
      | [] -> current
      | (a,b,_,_)::t ->
        if not (List.mem current (a,b) ~equal:double_equal) && not (Var.equal b (placeholder_vardef a) || Var.is_this b)
          then enum_nodup t ((a,b)::current)
          else enum_nodup t current in
    enum_nodup elements []


  (** 실행이 끝난 astate에서 중복된 튜플들 (proc과 vardef가 같음)끼리 묶여 있는 list of list를 만든다. *)
  let group_by_duplicates (astate:S.t) : S.elt list list = 
    let keys = get_keys astate in
    let rec get_tuple_by_key tuplelist key =
      match tuplelist with
      | [] -> []
      | (proc,name,_,_) as targetTuple::t ->
          if double_equal key (proc,name)
          then targetTuple::get_tuple_by_key t key
          else get_tuple_by_key t key in
    let get_tuples_by_keys tuplelist keys = List.map ~f:(get_tuple_by_key tuplelist) keys in
    let elements = S.elements astate in
    get_tuples_by_keys elements keys 


  (** group_by_duplicates가 만든 list of list를 받아서, duplicate된 변수 list를 반환하되, ph와 this는 무시한다. *)
  let rec collect_duplicates (listlist:S.elt list list) : S.elt list list =
    match listlist with
    | [] -> []
    | lst::t ->
        let sample_tuple = List.nth_exn lst 0 in
        let current_var = second_of sample_tuple in
        let ph_for_compare = placeholder_vardef (first_of sample_tuple) in
        if not @@ Var.equal current_var ph_for_compare && not @@ Var.is_this current_var
          then if List.length lst > 1 then lst::collect_duplicates t else collect_duplicates t
          else collect_duplicates t


  (** group_by_duplicates가 만든 list들 중에서 가장 최근의 것들을 찾아다 현재 환경에 맞게 바꿔 추가한다. *)
  let move_to_this_env (my_astate:S.t) (my_methname:Procname.t) (listlist:S.elt list list) =
    L.progress "moving to %a" Procname.pp my_methname;
    let most_recent_tuple = fun lst ->
      let (proc, var, _, alias) = List.nth_exn lst 0 in
      L.progress "get the most recent loc of: %a\n" Var.pp var;
      (proc, var, get_most_recent_loc var, alias) in
    let localize = fun (proc,var,loc,alias) ->
      L.progress "Localizing...";
      let var' = second_of @@ search_target_tuple_by_pvar var my_methname my_astate in
      (proc, var', loc, alias) in
    List.map listlist ~f:(most_recent_tuple >> localize)


  (** callee가 return c;꼴로 끝날 경우 새로 튜플을 만들고 alias set에 c를 추가 *)
  let variable_carryover astate callee_methname ret_id methname summ_read =
    let calleeTuples = find_tuple_with_ret summ_read callee_methname in
    (** 콜리 튜플 하나에 대해, 튜플 하나를 새로 만들어 alias set에 추가 *)
    let carryfunc tup =
      let ph = placeholder_vardef methname in
      let callee_vardef = second_of tup in
      let aliasset = D.doubleton callee_vardef (Var.of_id ret_id) in
      (methname, ph, Location.dummy, aliasset) in
    let carriedover = List.map calleeTuples ~f:carryfunc |> S.of_list in
    S.union astate carriedover
      

  (** 변수가 리턴된다면 그걸 alias set에 넣고 (variable carryover), 현재 환경에 맞게 재정의된 튜플을 변환한다 *)
  let apply_summary astate caller_summary callee_methname ret_id caller_methname : S.t =
    match Payload.read ~caller_summary:caller_summary ~callee_pname:callee_methname with
    | Some summ ->
        let var_carriedover = summ |> variable_carryover astate callee_methname ret_id caller_methname in
        let var_thisenv = var_carriedover |> (group_by_duplicates >> collect_duplicates >> move_to_this_env astate caller_methname) |> S.of_list in
        S.union var_carriedover var_thisenv
    | None -> astate


  let rec zip (l1:'a list) (l2:'b list) =
    match l1, l2 with
    | [], [] -> []
    | h1::t1, h2::t2 -> (h1, h2)::zip t1 t2
    | _, _ -> raise LengthError2


  let convert_from_mangled : Procname.t -> (Mangled.t*Typ.t) -> Var.t = fun methname (m,_) -> Pvar.mk m methname |> Var.of_pvar


  let get_formal_args (caller_procname:Procname.t) (caller_summary:Summary.t) (callee_pname:Procname.t) : Var.t list =
    match Payload.read_full ~caller_summary:caller_summary ~callee_pname:callee_pname with
    | Some (procdesc, _) -> Procdesc.get_formals procdesc |> List.map ~f:(convert_from_mangled caller_procname)
    | None -> (* Oops, it's a native code outside our focus *) []


  let get_my_formal_args (methname:Procname.t) = 
    match Procdesc.load methname with
    | Some pdesc -> L.progress "found procdesc for %a\n" Procname.pp methname; List.map ~f:(convert_from_mangled methname) (Procdesc.get_formals pdesc)
    | None -> raise NoSummary 


  let is_formal (rhs:Pvar.t) (current_meth:Procname.t) : bool =
    let formallist = get_my_formal_args current_meth in
    let rhs_var = Var.of_pvar rhs in
    List.mem formallist rhs_var ~equal:Var.equal


  let exec_store (exp1:Exp.t) (exp2:Exp.t) (methname:Procname.t) (astate:S.t) (node:CFG.Node.t) : S.t =
    match exp1, exp2 with
    | Lvar pv, Var id ->
        begin match Var.is_return (Var.of_pvar pv) with
        | true -> (* A variable is being returned *)
            let (_, _, _, aliasset) as targetTuple =
              try weak_search_target_tuple_by_id id astate
              with _ ->
                  (L.progress "=== Search Failed (1): Astate before search_target_tuple at %a := %a === @.:%a@." Exp.pp exp1 Exp.pp exp2 S.pp astate ; D.bottuple) in
            let pvar_var = A.find_first is_program_var aliasset in
            let most_recent_loc = get_most_recent_loc pvar_var in
            begin try
              let candTuples = search_target_tuples_by_vardef pvar_var methname astate in
              let (proc,var,loc,aliasset') as candTuple = search_tuple_by_loc most_recent_loc candTuples in
              let astate_rmvd = S.remove candTuple astate in
              let logicalvar = Var.of_id id in
              let programvar = Var.of_pvar pv in
              let newstate = (proc,var,loc,A.union aliasset' (D.doubleton logicalvar programvar)) in
              S.add newstate astate_rmvd
            with _ -> (* search failed: the pvar_var is not redefined in the procedure. *)
              S.remove targetTuple astate end
        | false -> (* An ordinary variable assignment. *)
            let (methname_old, vardef, _, aliasset) as targetTuple =
              try weak_search_target_tuple_by_id id astate
              with _ -> (L.progress "id: %a" Ident.pp id ; L.progress "=== Search Failed (2): Astate before search_target_tuple at %a := %a === @.:%a@." Exp.pp exp1 Exp.pp exp2 S.pp astate ; D.bottuple) in
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
          if not (is_placeholder_vardef vardef)
          then let newstate = (procname, vardef, loc, aliasset_new) in
               L.progress "astate before ++u1: @.%a@." S.pp astate;
               add_to_history pvar_var loc;
               S.add newstate astate
          else let newstate = (procname, vardef, loc, aliasset_new) in
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


(** jump from the ph tuple to the definition tuple. *)
let find_def_for_use id methname astate = 
  L.progress "jumping with id: %a\n" Ident.pp id;
  let var = second_of @@ search_target_tuple_by_id id methname astate in
  let vardefs = search_target_tuples_by_vardef var methname astate in
  search_tuple_by_loc (get_most_recent_loc var) vardefs


  let exec_call (ret_id:Ident.t) (e_fun:Exp.t) (arg_ts:(Exp.t*Typ.t) list) (caller_summary:Summary.t) (astate:S.t) (methname:Procname.t) =
    let callee_methname =
      match e_fun with
      | Const (Cfun fn) -> fn
      | _ -> raise NoMethname in
    match input_is_void_type arg_ts astate with
    | true -> (* All Arguments are Just Constants: just apply the summary, make a new tuple and end *)
        let astate_summary_applied = apply_summary astate caller_summary callee_methname ret_id methname in
        let newstate = (methname, placeholder_vardef methname, Location.dummy, A.singleton (Var.of_id ret_id)) in
        S.add newstate astate_summary_applied
    | false -> (* There is at least one argument which is a non-thisvar variable *)
        let astate_summary_applied = apply_summary astate caller_summary callee_methname ret_id methname in
        let formals = get_formal_args methname caller_summary callee_methname |> List.filter ~f:(fun x -> Var.is_this x |> not) in
        begin match formals with
          | [] -> (* Callee in Native Code! *)
              astate_summary_applied
          | _ ->  (* Callee in User Code! *)
              let actuals_logical = extract_nonthisvar_from_args methname arg_ts astate_summary_applied in
              let actuallog_formal_binding = leave_only_var_tuples @@ zip actuals_logical formals in
              (* pvar tuples transmitted as actual arguments *)
              let actuals_pvar_tuples = actuals_logical |> List.filter ~f:is_logical_var_expr |> List.map ~f:(function
                  | Exp.Var id ->
                      L.progress "id: %a, processing: @.:%a@." Ident.pp id S.pp astate;
                      let pvar = search_target_tuples_by_id id methname astate |> List.map ~f:fourth_of |> extract_another_pvar id in
                      search_recent_vardef methname pvar astate
                  | _ -> raise UndefinedSemantics2) in
              let actualpvar_alias_added = add_bindings_to_alias_of_tuples methname actuallog_formal_binding actuals_pvar_tuples |> S.of_list in
              let applied_state_rmvd = S.diff astate_summary_applied (S.of_list actuals_pvar_tuples) in
              S.union applied_state_rmvd actualpvar_alias_added end


  let exec_load (id:Ident.t) (exp:Exp.t) (astate:S.t) (methname:Procname.t) =
    match exp with
    | Lvar pvar ->
        begin match is_formal pvar methname with
          | true ->
              let double = D.doubleton (Var.of_id id) (Var.of_pvar pvar) in
              let ph = placeholder_vardef methname in
              let newstate = (methname, ph, Location.dummy, double) in
              let candTuples = search_target_tuples_by_vardef (Var.of_pvar pvar) methname astate in
              let most_recent_loc = get_most_recent_loc (Var.of_pvar pvar) in
              let (proc,var,loc,aliasset') as targetTuple = search_tuple_by_loc most_recent_loc candTuples in
              (* 파라미터가 등록되었을 때 search_target_tuple_by_id를 하기 위해. *)
              let updatedtuple = (proc,var,loc, A.add (Var.of_id id) aliasset') in
              let astate_rmvd = S.remove targetTuple astate in
              S.add updatedtuple (S.add newstate astate_rmvd)
          | false ->
              begin match search_target_tuples_by_pvar (Var.of_pvar pvar) methname astate with
                  | [] -> (* 한 번도 def된 적 없음 *)
                        let double = D.doubleton (Var.of_id id) (Var.of_pvar pvar) in
                        let ph = placeholder_vardef methname in
                        let newstate = (methname, ph, Location.dummy, double) in
                        S.add newstate astate
                  | h::_ as tuples -> (* 이전에 def된 적 있음 *)
                        let var = second_of h in
                        let most_recent_loc = get_most_recent_loc var in
                        let (proc, vardef, loc, aliasset) as  most_recent_tuple = search_tuple_by_loc most_recent_loc tuples in
                        let astate_rmvd = S.remove most_recent_tuple astate in
                        let mrt_updated = (proc, vardef, loc, A.add (Var.of_id id) aliasset) in
                        let double = D.doubleton (Var.of_id id) (Var.of_pvar pvar) in
                        let ph = placeholder_vardef methname in
                        let newstate = (methname, ph, Location.dummy, double) in
                        S.add mrt_updated astate_rmvd |> S.add newstate
              end
        end
    | _ -> raise UndefinedSemantics3


  let exec_metadata (instr:Sil.instr_metadata) (astate:S.t) =
    match instr with
    | ExitScope _ -> garbage_collect astate
    | _ -> astate


  let is_this_progress (var:Var.t) : unit =
    match var with
    | LogicalVar _ -> L.progress "Logical var: should never happen\n"
    | ProgramVar pv -> if Pvar.is_this pv then L.progress "this-variable\n" else L.progress "Not this-variable\n"


  let rec batch_add_to_history (keys:Var.t list) (loc:Location.t) =
    match keys with
    | [] -> ()
    | h::t -> add_to_history h loc; batch_add_to_history t loc


  (** register tuples for formal arguments before a procedure starts. *)
  let register_formals astate cfg_node methname =
    let node = CFG.Node.underlying_node cfg_node in
    match Procdesc.Node.get_kind node with
    | Start_node ->
        let formals = get_my_formal_args methname in
        let proc = Procdesc.Node.get_proc_name node in
        let targetloc = Procdesc.Node.get_loc node in
        (* 파라미터 라인넘버 보정 *)
        let loc = {Location.line=targetloc.line-1; Location.col=targetloc.col; Location.file=targetloc.file} in
        let bake_newtuple = fun (var:Var.t) -> (proc, var, loc, A.singleton var) in
        let tuplelist = List.map ~f:bake_newtuple formals in
        let tupleset = S.of_list tuplelist in
        batch_add_to_history formals loc ; S.union astate tupleset
    | _ -> astate


  let exec_instr : S.t -> extras ProcData.t -> CFG.Node.t -> Sil.instr -> S.t = fun prev' {summary} node instr ->
    let my_summary = summary in
    let methname = node |> CFG.Node.underlying_node |> Procdesc.Node.get_proc_name in
    let prev = register_formals prev' node methname in
      match instr with
      | Sil.Load {id=id; e=exp} when is_pvar_expr exp ->
          exec_load id exp prev methname
      | Sil.Load _ -> prev (* Complex things are not supported at this point *)
      | Sil.Store {e1=exp1; e2=exp2} ->
          exec_store exp1 exp2 methname prev node
      | Sil.Prune _ -> prev
      | Sil.Call ((ret_id, _), e_fun, arg_ts, _, _) ->
          exec_call ret_id e_fun arg_ts my_summary prev methname
      | Sil.Metadata md ->
          prev
          (* exec_metadata md prev *)


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
