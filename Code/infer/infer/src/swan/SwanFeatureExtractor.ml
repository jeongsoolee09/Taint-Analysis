open! IStd

open DefLocAlias

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

(* higher-order features are higher-order functions that return feature extractors *)
(* feature extractors are functions of Procname.t -> bool *)

(* module L = Logging *)
module F = Format
module Hashtbl = Caml.Hashtbl

exception NotYet


(* Hash table from Procname.t to Procdesc.t ========= *)
(* ================================================== *)

let procdesc_table = Hashtbl.create 777 


let add_pdesc (methname:Procname.t) : unit =
  let procdesc_opt = Procdesc.load methname in
  match procdesc_opt with
  | Some pdesc -> Hashtbl.add procdesc_table methname pdesc
  | None -> ()


let lookup_pdesc (methname:Procname.t) : Procdesc.t option =
  Hashtbl.find_opt procdesc_table methname


(* Feature Value ==================================== *)
(* ================================================== *)


type feature_value = True | False | DontKnow [@@deriving equal]


let output (boolval:bool) : feature_value =
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
                      "Could not load global tenv for %a@.!"
                      Procname.pp methname end in
      let java_struct = Tenv.lookup tenv_global classname in
      begin match java_struct with
        | Some struct_ ->
            let class_annot = struct_.annots in
            if Annot.Item.is_final class_annot
            then Class_Modifier.Final
            else Class_Modifier.Public (* TODO: Static annots *)
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
  fun (meth:Procname.t) ->      (* TODO *)
  raise NotYet


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
      let raw_params : Procname.Java.java_type list = Procname.Java.get_parameters java_meth in
      let string_params : string list = List.map ~f:(fun param ->
          Typ.Name.Java.Split.type_name param) raw_params in
      List.mem ~equal:String.equal string_params type_name
  | _ -> L.die InternalError "%a is not a Java method!" Procname.pp meth


(** Feature that checks whether a parameter flows to the sink. *)
let extract_ParamToSink ~(sink_name:string) =
  fun (meth:Procname.t) -> raise NotYet (* TODO *)


(** Does the return type contain the given name? *)
let extract_ReturnTypeContainsName ~(name:string) =
  fun (meth:Procname.t) ->
  let verbose_string = Procname.to_string meth in
  match String.is_substring verbose_string ~substring:" " with
  | true -> (* normal method; match with the return type's name *)
      let rtntype_string = String.take_while ~f:(fun char -> not @@ Char.equal ' ' char) "void setSomething()" in
      String.is_substring rtntype_string ~substring:name
  | false -> (* special method; match with the entire name *)
      String.is_substring verbose_string ~substring:name


(** Is the return type of the method equal to the type given? *)
let extract_ReturnType ~(type_name:string) =
  fun (meth:Procname.t) ->
  let verbose_string = Procname.to_string meth in
  match String.is_substring verbose_string ~substring:" " with
  | true -> (* normal method; match with the return type's name *)
      let rtntype_string = String.take_while ~f:(fun char -> not @@ Char.equal ' ' char) "void setSomething()" in
      String.equal rtntype_string type_name
  | false -> (* special method; match with the entire name *)
      String.equal verbose_string type_name


(** Does the source method return one of its parameters
    (we are only interested in sources with one of the given names)? *)
let extract_SourceToReturn ~(source_name:string) =
  fun (meth:Procname.t) -> raise NotYet (* TODO *)


(* This is kinda strange; what category will "public static void main" fall into?
   public or static? *)
(** Feature checking the method modifiers *)
let extract_MethodModifier ~(modifier:Method_Modifier.t) =
  fun (meth:Procname.t) ->
  let meth_modifier =if is_public_method meth then Method_Modifier.Public else
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
let extract_AnonymousClass =    (* TODO *)
  fun (meth:Procname.t) -> raise NotYet


(** Does this method have parameters? *)
let extract_HasParameters =
  fun (meth:Procname.t) ->
  match lookup_pdesc meth with
  | Some pdesc ->
      output @@ not @@ Int.equal (List.length @@ Procdesc.get_formals @@ pdesc) 0
  | None -> DontKnow


(** Does this method have a return type? *)
let extract_HasReturnType =
  fun (meth:Procname.t) ->
  match lookup_pdesc meth with
  | Some pdesc ->
      output @@ Typ.is_void @@ Procdesc.get_ret_type pdesc
  | None -> DontKnow


(** Is the method part of an inner class? *)
let extract_InnerClass =        (* TODO *)
  fun (meth:Procname.t) -> raise NotYet


(** Does this method return a constant? *)
let extract_ReturnsConstant =   (* TODO *)
  fun (meth:Procname.t) -> raise NotYet


(** Feature that checks wether a parameter flows to return value. *)
let extract_ParaFlowsToReturn = (* TODO *)
  fun (meth:Procname.t) -> raise NotYet


(** Does any of the parameters match the return type? *)
let extract_ParamTypeMatchesReturnType =
  fun (meth:Procname.t) ->
  match lookup_pdesc meth with
  | Some pdesc ->
      let paramtypes = List.map ~f:snd @@ Procdesc.get_formals pdesc in
      let rtntype = Procdesc.get_ret_type pdesc in
      output @@ List.mem paramtypes rtntype ~equal:Typ.equal
  | None -> DontKnow


(** Check if an invocation to a certain method is made. *)
let extract_InvocationName =    (* TODO *)
  fun (meth:Procname.t) -> raise NotYet


(** Returns if the method is a constructor or not. *)
let extract_IsConstructor =
  fun (meth:Procname.t) ->
  output @@ Procname.is_constructor meth


(** Feature that checks whether the current method begins with "get", and there
    is a corresponding "set" method in the class. *)
let extract_IsRealSetter =      (* TODO *)
  fun (meth:Procname.t) -> raise NotYet


(** Feature that matches whenever a method returns void and the method name starts
    with "on". *)
let extract_VoidOnMethod =
  fun (meth:Procname.t) ->
  match lookup_pdesc meth with
  | Some pdesc ->
      output (Typ.is_void @@ Procdesc.get_ret_type pdesc &&
      String.equal (get_prefix (Procname.get_method meth)) "on")
  | None -> DontKnow


(* Main ============================================ *)
(* ================================================= *)


let main () : unit =
  ()
