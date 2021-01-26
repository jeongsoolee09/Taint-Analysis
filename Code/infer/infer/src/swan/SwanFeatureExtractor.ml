open! IStd

(**
   |-----------+----------------------------+
   | Feature # | Feature types              |
   |-----------+----------------------------+
   |        01 | IsImplicitMethod           |
   |        02 | AnonymousClass             |
   |        03 | ClassContainsName          |
   |        04 | ClassEndsWithName          |
   |        05 | ClassModifier              |
   |        06 | HasParameters              |
   |        07 | HasReturnType              |
   |        08 | InnerClass                 |
   |        09 | InvocationClassName        |
   |        10 | MethodNameStartsWith       |
   |        11 | MethodNameEquals           |
   |        12 | MethodNameContains         |
   |        13 | ReturnsConstant            |
   |        14 | ParamContainsTypeOrName    |
   |        15 | ParaFlowsToReturn          |
   |        16 | ParamToSink                |
   |        17 | ParamTypeMatchesReturnType |
   |        18 | ReturnTypeContainsName     |
   |        19 | InvocationName             |
   |        20 | IsConstructor              |
   |        21 | IsRealSetter               |
   |        22 | MethodModifier             |
   |        23 | ReturnType                 |
   |        24 | SourceToReturn             |
   |        25 | VoidOnMethod               |
   |-----------+----------------------------+
*)

(** For use in infer_repl:

#mod_use "infer/src/swan/MyCallGraph.ml"
#mod_use "infer/src/swan/SetofAllMeths.ml"
#mod_use "infer/src/swan/SummaryLoader.ml"
#use "infer/src/swan/SwanFeatureExtractor.ml"

*)


(* higher-order features are higher-order functions that return feature extractors *)
(* feature extractors are functions of Procname.t -> bool *)

module L = Logging
module F = Format
module Map = Caml.Map.Make (Procname)
module Search = DefLocAliasSearches
module Test = DefLocAliasLogicTests
module S = DefLocAliasDomain.AbstractStateSetFinite
module A = DefLocAliasDomain.SetofAliases
module MyAccessPath = DefLocAliasDomain.MyAccessPath

exception NotYet

let methnames = SetofAllMeths.calculate_list ()

(* Utils ============================================ *)
(* ================================================== *)

let second_of (_, b, _, _) = b

let fourth_of (_, _, _, d) = d


let rec catMaybes_tuplist (optlist:('a*'b option) list) : ('a*'b) list =
  match optlist with
  | [] -> []
  | (sth1, Some sth2) :: t -> (sth1, sth2)::catMaybes_tuplist t
  | (_, None)::_ -> L.die InternalError "catMaybes_tuplist failed"


let is_call instr =
  match instr with
  | Sil.Call _ -> true
  | _ -> false


let exp_to_pvar (exp:Exp.t) =
  match exp with
  | Lvar pvar -> Var.of_pvar pvar
  | _ -> L.die InternalError
           "%a is not a pvar expression" Exp.pp exp


(* Map from Procname.t to their summaries =========== *)
(* ================================================== *)


let summary_table = SummaryLoader.load_summary_from_disk_to_map Map.empty


let lookup_summary (methname:Procname.t) =
  Map.find_opt methname summary_table


(* Map from Procname.t to their formal args ========= *)
(* ================================================== *)


let batch_add_formal_args map =
  let procnames = Map.fold (fun k _ acc -> k::acc) summary_table [] in
  let pname_and_pdesc_opt = List.map ~f:(fun pname ->
      (pname, Procdesc.load pname)) procnames in
  let pname_and_pdesc = catMaybes_tuplist pname_and_pdesc_opt in
  let pname_and_params_with_type = List.map ~f:(fun (pname, pdesc) ->
      (pname, Procdesc.get_pvar_formals pdesc)) pname_and_pdesc in
  let pname_and_params = List.map ~f:(fun (pname, with_type_list) ->
      (pname, List.map ~f:(fun (a, _) ->
           Var.of_pvar a) with_type_list)) pname_and_params_with_type in
  List.fold ~f:(fun acc (pname, params) ->
      Map.add pname params acc) ~init:map pname_and_params


let formal_arg_table = batch_add_formal_args Map.empty


let get_formal_args (key:Procname.t) = Map.find key formal_arg_table


(* Tabular representation of the callgraph ========== *)
(* ================================================== *)


let callgraph = MyCallGraph.load_callgraph_from_disk_to_map Map.empty


let lookup_callee (methname:Procname.t) : Procname.t option =
  Map.find_opt methname callgraph


(* Map from Procname.t to Procdesc.t ================ *)
(* ================================================== *)


let batch_add_pdesc_to_map (methnames:Procname.t list) map =
  List.fold ~f:(fun acc methname ->
      let procdesc_opt = Procdesc.load methname in
      match procdesc_opt with
      | Some pdesc -> Map.add methname pdesc acc
      | None -> acc) ~init:map methnames


let procdesc_table = batch_add_pdesc_to_map methnames Map.empty


let lookup_pdesc (methname:Procname.t) : Procdesc.t option =
  Map.find_opt methname procdesc_table


(* Feature Value ==================================== *)
(* ================================================== *)


type feature_value = True | False | DontKnow [@@deriving equal]


let return (boolval:bool) : feature_value =
  if boolval then True else False


module Class_Modifier = struct
  type t = Static | Public | Final [@@deriving equal]
end


(** get the modifier of the class that the given methname belongs to *)
let get_class_modifier (methname:Procname.t) =
  match methname with
  | Procname.Java java_meth ->
      let classname : Typ.Name.t = Procname.Java.get_class_type_name java_meth in
      let tenv_global =
        begin match Tenv.load_global () with
          | Some tenv_ -> tenv_
          | None -> L.die InternalError
                      "Could not load global tenv for %a@."
                      Procname.pp methname end in
      let java_struct = Tenv.lookup tenv_global classname in
      begin match java_struct with
        | Some struct_ ->
            let class_annot = struct_.annots in
            if Annot.Item.is_final class_annot
            then Class_Modifier.Final
            else Class_Modifier.Public (* NOTE Static annots are missing *)
        | None -> L.die InternalError "Tenv lookup for %a failed!@." Procname.pp methname end
  | _ -> L.die InternalError "%a is not a Java method!" Procname.pp methname


module Method_Modifier = struct
  type t = Static | Public | Private | Final [@@deriving equal]
end


let is_static_method (meth:Procname.t) =
  match meth with
  | Procname.Java java_meth -> Procname.Java.is_static java_meth
  | _ -> L.die InternalError "%a is not a Java method!" Procname.pp meth


let is_public_method (meth:Procname.t) =
  let procdesc =
    match lookup_pdesc meth with
    | Some pdesc_ -> pdesc_
    | None -> L.die InternalError
                "Could not find pdesc for %a@." Procname.pp meth in
  let procattr = Procdesc.get_attributes procdesc in
  match procattr.access with
  | Public -> true
  | _ -> false


let is_private_method (meth:Procname.t) =
  let procdesc =
    match lookup_pdesc meth with
    | Some pdesc_ -> pdesc_
    | None -> L.die InternalError
                "Could not find pdesc for %a@." Procname.pp meth in
  let procattr = Procdesc.get_attributes procdesc in
  match procattr.access with
  | Private -> true
  | _ -> false


let is_final_method (meth:Procname.t) = 
  let procdesc =
    match lookup_pdesc meth with
    | Some pdesc_ -> pdesc_
    | None -> L.die InternalError
                "Could not find pdesc for %a@." Procname.pp meth in
  let procattr = Procdesc.get_attributes procdesc in
  let {return; params} : Annot.Method.t = procattr.method_annotation in
  List.exists ~f:(fun (annot:Annot.Item.t) ->
      Annot.Item.is_final annot) params || Annot.Item.is_final return


(* Prefix utils ===================================== *)
(* ================================================== *)


(** return "get" when given "getSomethingNow". *)
let get_prefix (camel_case_string:string) : string =
  String.take_while ~f:(fun char -> Char.is_lowercase char) camel_case_string


(** find the index of the last uppercase character in a string. *)
let find_last_uppercase_char_index (camel_case_string:string) =
  String.rfindi camel_case_string ~f:(fun _ char -> Char.is_uppercase char)


(** return "Now" when given "getSomethingNow". *)
let get_last_word (camel_case_string:string) : string =
  let index = find_last_uppercase_char_index camel_case_string in
  match index with
  | Some index ->
      let str_length = String.length camel_case_string in
      String.sub ~pos:index ~len:(str_length-index) camel_case_string
  | None -> camel_case_string
      

(* Higher-order features ============================ *)
(* ================================================== *)


(** Is the method part of class that contains the given name? *)
let extract_ClassContainsName ~(name:string) =
  fun (meth:Procname.t) ->
  String.is_substring (Procname.to_string meth) ~substring:name


(** Is the method part of class that ends with the given name? *)
let extract_ClassEndsWithName ~(name:string) =
  fun (meth:Procname.t) ->
  String.is_substring (Procname.to_string meth) ~substring:name


(** This feature checks the modifier of the class where the method is part of. *)
let extract_ClassModifier ~(modifier:Class_Modifier.t) =
  fun (meth:Procname.t) ->
  let class_modifier = get_class_modifier meth in
  match modifier with
  | Static -> Class_Modifier.equal class_modifier Static
  | Public -> Class_Modifier.equal class_modifier Public
  | Final  -> Class_Modifier.equal class_modifier Final


(** Check if an invocation to a method of a certain class is made. *)
let extract_InvocationClassName ~(classname:string) =
  fun (meth:Procname.t) ->
  (* iterating through the callgraph_table,
     find if the given classname appears on the rhs. *)
  let occurs_on_right_side sth =
    String.is_substring sth ~substring:classname in
  Map.fold (fun k v acc ->
      if (Procname.equal k meth)
      then occurs_on_right_side (Procname.to_string v) || acc
      else acc) callgraph false


(** Does this method's name start with the given word? *)
let extract_MethodNameStartsWith ~(word:string) =
  fun (meth:Procname.t) ->
  String.equal (get_prefix (Procname.get_method meth)) word


(** Is this method's name identical the given word? *)
let extract_MethodNameEquals ~(word:string) =
  fun (meth:Procname.t) ->
  String.equal (Procname.get_method meth) word


(** Does this method's name contain the given word? *)
let extract_MethodNameContains ~(word:string) =
  fun (meth:Procname.t) ->
  String.is_substring (Procname.get_method meth) ~substring:word


(** Do any of the parameters' type contain the given name? *)
let extract_ParamContainsTypeOrName ~(type_name:string) =
  fun (meth:Procname.t) ->
  match meth with
  | Procname.Java java_meth ->
      let raw_params = Procname.Java.get_parameters java_meth in
      let string_params : string list = List.map ~f:(fun param ->
          Typ.to_string param) raw_params in
      List.mem ~equal:String.equal string_params type_name
  | _ -> L.die InternalError "%a is not a Java method!" Procname.pp meth


let big_union_A list_of_sets =
  List.fold ~f:(fun set acc -> A.union set acc) ~init:A.empty list_of_sets


let big_union_S list_of_sets =
  List.fold ~f:(fun set acc -> S.union set acc) ~init:S.empty list_of_sets


let transitively_collect_aliases ap summary methname =
  (* ap를 vardef로 갖고 있는 가장 이른 튜플을 찾는다. *)
  let rec inner methname current_ap =
    let ap_vardef_tuples =
      Search.search_target_tuples_by_vardef (fst current_ap) methname summary in
    (* recursion bottoms out *)
    if Int.equal (List.length ap_vardef_tuples) 0 then A.singleton current_ap else
    let ap_vardef_tuple = Search.find_earliest_astate_within ap_vardef_tuples methname in
    let aliasset = fourth_of ap_vardef_tuple
                   |> A.filter (fun tup ->
                       not @@ Test.is_returnv_ap tup &&
                       not @@ Test.is_callv_ap tup &&
                       not @@ Test.is_logical_var (fst tup) &&
                       not @@ Test.is_frontend_tmp_var (fst tup))
                   |> A.filter (fun tup ->
                       not @@ MyAccessPath.equal current_ap tup)
                   |> A.elements in
    big_union_A @@ List.map ~f:(inner methname) aliasset in
  inner methname ap 


let find_params_and_friends methname summary =
  (* Need to implement a propagation logic *)
  let raw_params = get_formal_args methname in
  let param_aps = List.map ~f:(fun param -> (param, [])) raw_params in
  let friends = A.elements @@ big_union_A @@ List.map ~f:(fun param_ap ->
      transitively_collect_aliases param_ap summary methname) param_aps in
  param_aps @ friends


let extract_args (call_instr:Sil.instr) (methname:Procname.t) (astate_set:S.t) : A.elt list =
  match call_instr with
  | Call (_, _, exp_list, _, _) ->
      exp_list
      |> List.map ~f:fst
      |> List.filter ~f:(fun exp -> not @@ Exp.is_const exp)
      |> List.map ~f:(fun exp ->
          match exp with
          | Exp.Var id -> Search.search_target_tuple_by_id id methname astate_set
          | _ -> L.die InternalError
                   "unexpected exp %a found as arg to method %a@."
                   Exp.pp exp Procname.pp methname)
      |> List.map ~f:second_of
  | _ -> L.die InternalError
           "%a is not a call instruction!"
           (Sil.pp_instr ~print_types:false Pp.text) call_instr


let extract_calleename (call_instr:Sil.instr) : string =
  match call_instr with
  | Call (_, e_fun, _, _, _) -> Exp.to_string e_fun
  | _ -> L.die InternalError
           "%a is not a call instruction!"
           (Sil.pp_instr ~print_types:false Pp.text) call_instr


(** Feature that checks whether a parameter flows to the sink. *)
let extract_ParamToSink ~(sink_name:string) =
  fun (meth:Procname.t) ->
  (* To satisfy this predicate, the given meth should:
     1. have parameters,
     2. contain a call statement,
     3. (that statement should be an invocation to a sink method,)
     4. pass the parameter to the sink method. *)
  (* checking if 1 *)
  if Int.equal (List.length (Procname.get_parameters meth)) 0 then return false else
    (* checking if 2 and 3 *)
    let appears_on_callgraph caller callee_name_piece = 
      Map.fold (fun k v acc ->
          (Procname.equal k caller &&
           (String.is_substring (Procname.to_string v) ~substring:callee_name_piece))
          || acc) callgraph false in
    if not @@ appears_on_callgraph meth sink_name then return false else
      (* checking if 4 *)
      let passing_param_to_sink caller callee_name_piece : feature_value =
        (* need to leverage the static analysis:
           iterate through the set and search for the return variable,
           and see if params or its aliases are return var's aliases *)
        let summary = lookup_summary caller in
        match summary with
        | Some summ ->
            let params_and_its_aliases = find_params_and_friends meth summ in
            let caller_pdesc_opt = Procdesc.load caller in
            begin match caller_pdesc_opt with
              | Some pdesc ->
                  let call_instrs =
                    Procdesc.fold_instrs pdesc ~init:[]
                      ~f:(fun acc _ instr ->
                          if is_call instr && String.is_substring (extract_calleename instr)
                               ~substring:callee_name_piece
                          then instr::acc else acc) in
                  (* at least one of the call instrs should invoke the designated callee *)
                  if Int.equal (List.length call_instrs) 0 then return false else
                    let all_sink_args =
                      List.fold ~f:(fun acc instr ->
                          acc @ (extract_args instr caller summ)) ~init:[] call_instrs in
                    return @@ List.fold ~f:(fun acc param_ap ->
                        List.mem all_sink_args param_ap ~equal:MyAccessPath.equal || acc)
                      ~init:false params_and_its_aliases
              | None -> DontKnow end
        | None -> DontKnow in
      passing_param_to_sink meth sink_name


(** Does the return type contain the given name? *)
let extract_ReturnTypeContainsName ~(name:string) =
  fun (meth:Procname.t) ->
  let verbose_string = Procname.to_string meth in
  match String.is_substring verbose_string ~substring:" " with
  | true -> (* normal method; match with the return type's name *)
      let rtntype_string = String.take_while ~f:(fun char ->
          not @@ Char.equal ' ' char) verbose_string in
      String.is_substring rtntype_string ~substring:name
  | false -> (* special method; match with the entire name *)
      String.is_substring verbose_string ~substring:name


(** Is the return type of the method equal to the type given? *)
let extract_ReturnType ~(type_name:string) =
  fun (meth:Procname.t) ->
  let verbose_string = Procname.to_string meth in
  match String.is_substring verbose_string ~substring:" " with
  | true -> (* normal method; match with the return type's name *)
      let rtntype_string = String.take_while ~f:(fun char ->
          not @@ Char.equal ' ' char) verbose_string in
      String.equal rtntype_string type_name
  | false -> (* special method; match with the entire name *)
      String.equal verbose_string type_name


(** Does the source method return one of its parameters
    (we are only interested in sources with one of the given names)? *)
let extract_ret_id call_instr =
  match call_instr with
  | Sil.Call ((id, _), _, _, _, _) -> id
  | _ -> L.die InternalError
           "%a is not a call_instr!"
           (Sil.pp_instr ~print_types:false Pp.text) call_instr


let extract_SourceToReturn ~(source_name:string) =
  fun (meth:Procname.t) ->
  (* Do any of the following:
     1. values returned from a source
     2. values used as arugments to invoke a source
     flow to the return value? *)
  (* 1. Is there an invocation to the indicated source method? *)
  let appears_on_callgraph caller callee_name_piece = 
    Map.fold (fun k v acc ->
        (Procname.equal k caller &&
         (String.is_substring (Procname.to_string v) ~substring:callee_name_piece))
        || acc) callgraph false in
  if not @@ appears_on_callgraph meth source_name then return false else
    (* 2. Do the aforementioned values flow to a return? *)
    match Summary.OnDisk.get meth with
    | Some summary_payload ->
      begin match summary_payload.Summary.payloads.def_loc_alias with
        | Some summary ->
          let passing_sourceval_to_return (meth:Procname.t) callee_name_piece : feature_value =
            (* need to leverage the static analysis:
               iterate through the set and search for the return variable,
               and see if params or its aliases are return var's aliases *)
            let return_tups = Search.find_tuples_with_ret (fst summary) meth in
            let return_aliases = List.map ~f:(fun return_tup -> fourth_of return_tup) return_tups
                                 |> List.fold ~f:(fun acc set -> A.union acc set) ~init:A.empty
                                 |> A.elements in
            begin match Procdesc.load meth with
              | Some pdesc ->
                let call_instrs =
                  Procdesc.fold_instrs pdesc ~init:[]
                    ~f:(fun acc _ instr ->
                        if is_call instr && String.is_substring (extract_calleename instr)
                             ~substring:callee_name_piece
                        then instr::acc else acc) in
                (* If there are no calls to the designated source, then just return false *)
                if Int.equal (List.length call_instrs) 0 then return false else
                  let ret_id_aliases = List.map ~f:extract_ret_id call_instrs
                                       (* is there a non-ph tuple with the ret_id? *)
                                       |> List.map ~f:(fun id ->
                                           Search.search_target_tuple_by_id id meth (fst summary))
                                       |> List.map ~f:(fun tup -> fourth_of tup)
                                       |> big_union_A
                                       |> A.elements
                                       |> List.map ~f:(fun ap ->
                                           transitively_collect_aliases ap (fst summary) meth)
                                       |> big_union_A
                                       |> A.elements in
                  return @@ List.fold ~f:(fun acc ap ->
                      List.mem ret_id_aliases ap ~equal:MyAccessPath.equal || acc)
                    ~init:false return_aliases
              | None -> DontKnow end in
          passing_sourceval_to_return meth source_name
        | None -> DontKnow end
    | None -> DontKnow



(* This is kinda strange; what category will "public static void main" fall into?
   public or static? *)
(** Feature checking the method modifiers *)
let extract_MethodModifier ~(modifier:Method_Modifier.t) =
  fun (meth:Procname.t) ->
  let meth_modifier = if is_public_method meth then Method_Modifier.Public else
    if is_private_method meth then Method_Modifier.Private else
    if is_static_method meth then Method_Modifier.Static else
    if is_final_method meth then Method_Modifier.Final else
      L.die InternalError "No modifier has been detected for %a@."
        Procname.pp meth in
  Method_Modifier.equal modifier meth_modifier


(* instantiated Higher-order Functions ============== *)
(* ================================================== *)


let classContainsName_features = [
  extract_ClassContainsName ~name:"Saniti"
; extract_ClassContainsName ~name:"Encod"
; extract_ClassContainsName ~name:"Escap"
; extract_ClassContainsName ~name:"Valid"
; extract_ClassContainsName ~name:"Check"
; extract_ClassContainsName ~name:"Verif"
; extract_ClassContainsName ~name:"Authen"
; extract_ClassContainsName ~name:"Security"
; extract_ClassContainsName ~name:"Connect"
; extract_ClassContainsName ~name:"Bind"
; extract_ClassContainsName ~name:"OAuth"
; extract_ClassContainsName ~name:".io."
; extract_ClassContainsName ~name:"web"
; extract_ClassContainsName ~name:".net."
; extract_ClassContainsName ~name:"sql"
; extract_ClassContainsName ~name:"Manager"
; extract_ClassContainsName ~name:"Output"
; extract_ClassContainsName ~name:"Input"
; extract_ClassContainsName ~name:"database"
; extract_ClassContainsName ~name:"db"
; extract_ClassContainsName ~name:"hibernate"
; extract_ClassContainsName ~name:"credential"
; extract_ClassContainsName ~name:"process"
; extract_ClassContainsName ~name:"runtime"
; extract_ClassContainsName ~name:"user"
; extract_ClassContainsName ~name:"jdbc"
; extract_ClassContainsName ~name:"Html"
; extract_ClassContainsName ~name:"Page"
; extract_ClassContainsName ~name:"Request"
; extract_ClassContainsName ~name:"http"
; extract_ClassContainsName ~name:"url"
; extract_ClassContainsName ~name:"servlet"
; extract_ClassContainsName ~name:"Response"
; extract_ClassContainsName ~name:"Redirect"
; extract_ClassContainsName ~name:"Css"
; extract_ClassContainsName ~name:"Dom"
]


let classEndsWithName_features = [
  extract_ClassEndsWithName ~name:"Encoder"
; extract_ClassEndsWithName ~name:"Request"
; extract_ClassEndsWithName ~name:"Render"
]


let classModifier_features = [
  extract_ClassModifier ~modifier:Class_Modifier.Static
; extract_ClassModifier ~modifier:Class_Modifier.Public
; extract_ClassModifier ~modifier:Class_Modifier.Final
]


let invocationClassName_features = [
  extract_InvocationClassName ~classname:"Saniti"
; extract_InvocationClassName ~classname:"regex"
; extract_InvocationClassName ~classname:"escap"
; extract_InvocationClassName ~classname:".io."
; extract_InvocationClassName ~classname:"encod"
; extract_InvocationClassName ~classname:"sql"
; extract_InvocationClassName ~classname:"db"
; extract_InvocationClassName ~classname:"web"
; extract_InvocationClassName ~classname:".net."
; extract_InvocationClassName ~classname:"Log."
]


let methodNameStartsWith_features = [
  extract_MethodNameStartsWith ~word:"get"
; extract_MethodNameStartsWith ~word:"set"
; extract_MethodNameStartsWith ~word:"put"
; extract_MethodNameStartsWith ~word:"has"
; extract_MethodNameStartsWith ~word:"is"
; extract_MethodNameStartsWith ~word:"open"
; extract_MethodNameStartsWith ~word:"close"
; extract_MethodNameStartsWith ~word:"create"
; extract_MethodNameStartsWith ~word:"delete"
]


let methodNameEquals_features = [
  extract_MethodNameEquals ~word:"log"
; extract_MethodNameEquals ~word:"setHeader"
; extract_MethodNameEquals ~word:"sendRedirect"
]


let methodNameContains = [
  extract_MethodNameContains ~word:"saniti"
; extract_MethodNameContains ~word:"escape"
; extract_MethodNameContains ~word:"unescape"
; extract_MethodNameContains ~word:"replac"
; extract_MethodNameContains ~word:"strip"
; extract_MethodNameContains ~word:"encod"
; extract_MethodNameContains ~word:"regex"
; extract_MethodNameContains ~word:"authen"
; extract_MethodNameContains ~word:"check"
; extract_MethodNameContains ~word:"verif"
; extract_MethodNameContains ~word:"privilege"
; extract_MethodNameContains ~word:"login"
; extract_MethodNameContains ~word:"loginpage"
; extract_MethodNameContains ~word:"logout"
; extract_MethodNameContains ~word:"connect"
; extract_MethodNameContains ~word:"disconnect"
; extract_MethodNameContains ~word:"bind"
; extract_MethodNameContains ~word:"unbind"
; extract_MethodNameContains ~word:"read"
; extract_MethodNameContains ~word:"thread"
; extract_MethodNameContains ~word:"load"
; extract_MethodNameContains ~word:"payload"
; extract_MethodNameContains ~word:"request"
; extract_MethodNameContains ~word:"creat"
; extract_MethodNameContains ~word:"decod"
; extract_MethodNameContains ~word:"unescap"
; extract_MethodNameContains ~word:"pars"
; extract_MethodNameContains ~word:"stream"
; extract_MethodNameContains ~word:"retriev"
; extract_MethodNameContains ~word:"Object"
; extract_MethodNameContains ~word:"Name"
; extract_MethodNameContains ~word:"writ"
; extract_MethodNameContains ~word:"updat"
; extract_MethodNameContains ~word:"send"
; extract_MethodNameContains ~word:"handl"
; extract_MethodNameContains ~word:"log"
; extract_MethodNameContains ~word:"run"
; extract_MethodNameContains ~word:"execut"
; extract_MethodNameContains ~word:"compile"
; extract_MethodNameContains ~word:"dump"
; extract_MethodNameContains ~word:"print"
; extract_MethodNameContains ~word:"execute"
; extract_MethodNameContains ~word:"query"
; extract_MethodNameContains ~word:"role"
; extract_MethodNameContains ~word:"authori"
; extract_MethodNameContains ~word:"redirect"
; extract_MethodNameContains ~word:"getParameter"
]


let paramContainsTypeOrName = [
  extract_ParamContainsTypeOrName ~type_name:"java.lang.String"
; extract_ParamContainsTypeOrName ~type_name:"char[]"
; extract_ParamContainsTypeOrName ~type_name:"byte[]"
; extract_ParamContainsTypeOrName ~type_name:"java.lang.CharSequence"
; extract_ParamContainsTypeOrName ~type_name:"java.lang.StringBuilder"
; extract_ParamContainsTypeOrName ~type_name:".io."
; extract_ParamContainsTypeOrName ~type_name:"web"
; extract_ParamContainsTypeOrName ~type_name:"sql"
; extract_ParamContainsTypeOrName ~type_name:"db"
; extract_ParamContainsTypeOrName ~type_name:"credential"
; extract_ParamContainsTypeOrName ~type_name:"url"
]


let paramToSink = [
  extract_ParamToSink ~sink_name:"writ"
; extract_ParamToSink ~sink_name:"set"
; extract_ParamToSink ~sink_name:"updat"
; extract_ParamToSink ~sink_name:"send"
; extract_ParamToSink ~sink_name:"handl"
; extract_ParamToSink ~sink_name:"put"
; extract_ParamToSink ~sink_name:"log"
; extract_ParamToSink ~sink_name:"run"
; extract_ParamToSink ~sink_name:"execut"
; extract_ParamToSink ~sink_name:"dump"
; extract_ParamToSink ~sink_name:"print"
; extract_ParamToSink ~sink_name:"pars"
; extract_ParamToSink ~sink_name:"stream"
]


let returnTypeContainsName = [
  extract_ReturnTypeContainsName ~name:"Document"
; extract_ReturnTypeContainsName ~name:"Node"
; extract_ReturnTypeContainsName ~name:"User"
; extract_ReturnTypeContainsName ~name:"Credential"
; extract_ReturnTypeContainsName ~name:"Servlet"
; extract_ReturnTypeContainsName ~name:"Request"
]


let returnType = [
  extract_ReturnType ~type_name:"byte[]"
; extract_ReturnType ~type_name:"java.lang.String"
; extract_ReturnType ~type_name:"java.lang.CharSequence"
; extract_ReturnType ~type_name:"boolean"
; extract_ReturnType ~type_name:"java.sql.ResultSet"
]


let sourceToReturn = [
  extract_SourceToReturn ~source_name:"get"
; extract_SourceToReturn ~source_name:"read"
; extract_SourceToReturn ~source_name:"decode"
; extract_SourceToReturn ~source_name:"unescape"
; extract_SourceToReturn ~source_name:"load"
; extract_SourceToReturn ~source_name:"request"
; extract_SourceToReturn ~source_name:"create"
]


(* Simple Feature extractors ======================== *)
(* ================================================== *)


(** Implicit methods (e.g. methods from bytecode for access of private fields) *)
let extract_IsImplicitMethod =
  fun (meth:Procname.t) ->
  let string_meth = Procname.to_string meth in
  String.is_substring string_meth ~substring:"$"


(** This feature checks wether the method is part of an anonymous class or not. *)
let extract_AnonymousClass =
  fun (meth:Procname.t) ->
  match meth with
  | Procname.Java java_meth ->
      let classname : Typ.Name.t = Procname.Java.get_class_type_name java_meth in
      Typ.Name.Java.is_anonymous_inner_class_name_exn classname
  | _ -> L.die InternalError "%a is not a Java method!" Procname.pp meth


(** Does this method have parameters? *)
let extract_HasParameters =
  fun (meth:Procname.t) ->
  match lookup_pdesc meth with
  | Some pdesc ->
      return @@ not @@ Int.equal (List.length @@ Procdesc.get_formals @@ pdesc) 0
  | None -> DontKnow


(** Does this method have a return type? *)
let extract_HasReturnType =
  fun (meth:Procname.t) ->
  match lookup_pdesc meth with
  | Some pdesc ->
      return @@ Typ.is_void @@ Procdesc.get_ret_type pdesc
  | None -> DontKnow


(* NOTE extract_InnerClass is excluded since
   Infer does not support a NAMED inner class,
   only the anonymous inner clases. *)


(** Is this method returning a constant (at least once?) *)
let extract_ReturnsConstant =
  fun (meth:Procname.t) ->
  let is_returning_constant (ret_instr:Sil.instr) =
    match ret_instr with
    | Store {e1=lhs; e2=rhs} ->
        if Test.is_program_var_expr lhs && Exp.is_const rhs
        then Var.is_return (exp_to_pvar lhs)
        else false
    | _ -> L.die InternalError "fuck" in
  match Procdesc.load meth with
  | Some pdesc ->
      return @@ Procdesc.fold_instrs pdesc ~init:false
          ~f:(fun acc _ instr ->
              is_returning_constant instr || acc)
  | None -> DontKnow
  

(** Feature that checks wether a parameter flows to return value. *)
let extract_ParaFlowsToReturn = (* TODO: will do it tomorrow *)
  fun (meth:Procname.t) -> raise NotYet


(** Does any of the parameters match the return type? *)
let extract_ParamTypeMatchesReturnType =
  fun (meth:Procname.t) ->
  match lookup_pdesc meth with
  | Some pdesc ->
      let paramtypes = List.map ~f:snd @@ Procdesc.get_formals pdesc in
      let rtntype = Procdesc.get_ret_type pdesc in
      return @@ List.mem paramtypes rtntype ~equal:Typ.equal
  | None -> DontKnow


(** Check if an invocation to a certain method is made. *)
let extract_InvocationName =
  fun (meth:Procname.t) ->
  Map.fold (fun _ v acc ->
    Procname.equal meth v || acc) callgraph false


(** Returns if the method is a constructor or not. *)
let extract_IsConstructor =
  fun (meth:Procname.t) ->
  return @@ Procname.is_constructor meth


(** Feature that checks whether the current method begins with "get", and there
    is a corresponding "set" method in the class. *)
let extract_IsRealSetter =
  fun (meth:Procname.t) ->
  match meth with
  | Procname.Java java_meth ->
    let method_string = Procname.Java.get_method java_meth in
    if not @@ String.equal (get_prefix method_string) "set" then False else
      let classname : Typ.Name.t = Procname.Java.get_class_type_name java_meth in
      let all_methods_of_class =
        methnames
        |> List.map ~f:(fun meth ->
            match meth with
            | Procname.Java java_meth -> java_meth
            | _ -> L.die InternalError "%a is not a Java method!" Procname.pp meth)
        |> List.filter ~f:(fun meth_ ->
            let classname_ = Procname.Java.get_class_type_name meth_ in
            Typ.Name.equal classname_ classname) in
      let method_name_without_set = String.slice method_string 3 (String.length method_string) in
      let corresponding_getter_string = "get"^method_name_without_set in
      return @@ List.fold ~f:(fun acc meth_ ->
          let method_string = Procname.Java.get_method meth_ in
          String.equal corresponding_getter_string method_string || acc) ~init:false all_methods_of_class
  | _ -> L.die InternalError "%a is not a Java method!" Procname.pp meth


(** Feature that matches whenever a method returns void and the method name starts
    with "on". *)
let extract_VoidOnMethod =
  fun (meth:Procname.t) ->
  match lookup_pdesc meth with
  | Some pdesc ->
      return (Typ.is_void @@ Procdesc.get_ret_type pdesc &&
      String.equal (get_prefix (Procname.get_method meth)) "on")
  | None -> DontKnow


(* Main ============================================ *)
(* ================================================= *)


let main () : unit =
  ()
