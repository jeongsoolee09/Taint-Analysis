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


(* Feature Value ==================================== *)
(* ================================================== *)


type feature_value = True | False | DontKnow [@@deriving equal]


let output (boolval:bool) : feature_value =
  if boolval then True else False


module Class_Modifier = struct
  type t = Static | Public | Final [@@deriving equal]
end


(** get the modifier of the class that the given methname belongs to *)
let get_class_modifier (methname:Procname) : class_modifier =
  let classname : Typ.Name.t = Procname.get_class_type_name methname in
  let java_struct = Tenv.lookup classname in
  match java_struct with
  | Some struct_ ->
    let class_annot = struct_.annots in
    if Annot.Item.is_final then Final else Public (* TODO: Static annots *)
  | None -> L.die InternalError "This is not a Java method!: %a@." Procname.pp methname


module Method_Modifier = struct
  type t = Static | Public | Private | Final [@@deriving equal]
end


let is_static_method (meth:Procname.t) =
  match meth with
  | Procname.Java java_meth -> Procname.Java.is_static java_meth
  | _ -> DontKnow


let is_public_method (meth:Procname.t) =
  let procdesc = lookup_pdesc meth in
  let procattr = Procdesc.get_attributes procdesc in
  match procattr.access with
  | Public -> true
  | _ -> false


let is_private_method (meth:Procname.t) =
  let procdesc = lookup_pdesc meth in
  let procattr = Procdesc.get_attributes procdesc in
  match procattr.access with
  | Private -> true
  | _ -> false
  

let is_final_method (meth:Procname.t) = 
  let procdesc = lookup_pdesc meth in
  let procattr = Procdesc.get_attributes procdesc in
  let {return; params} : Annot.Method.t = procattr.method_annotation in
  List.exists ~f:(fun (annot:Annot.Item.t) -> Annot.Item.is_final annot) params || Annot.Item.is_final return


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


(* Prefix utils ===================================== *)
(* ================================================== *)


(** return "get" when given "getSomethingNow". *)
let get_prefix (camel_case_string:string) : string =
  String.take_while ~f:(fun char -> Char.is_lowercase char) camel_case_string


(** return "Now" when given "getSometingNow". *)
let get_last_word (camel_case_string:string) : string =
  let last_uppercase_char = find_last_uppercase_char caml_case_string in
  let last_uppercase_char_index = String.rindex camel_case_string last_uppercase_char in
  let str_length = String.length last_uppercase_char in
  String.sub ~pos:last_uppercase_char_index ~len:(str_length-last_uppercase_char)


(* Higher-order features ============================ *)
(* ================================================== *)


(** Is the method part of class that contains the given name? *)
let extract_ClassContainsName ~(name:string) =
  fun (meth:Procname.t) ->
  String.contains (Procname.to_string meth) ~substring:name


(** Is the method part of class that ends with the given name? *)
let extract_ClassEndsWithName ~(name:string) =
  fun (meth:Procname.t) ->
  String.contains (Procname.to_string meth) ~substring:name


(** This feature checks the modifier of the class where the method is part of. *)
let extract_ClassModifier ~(modifier:class_modifier) =
  fun (meth:Procname.t) ->
  let class_modifier = get_class_mod in
  match modifier with
  | Static -> Class_Modifier.equal class_modifier Static
  | Public -> Class_Modifier.equal class_modifier Public
  | Final  -> Class_Modifier.equal class_modifier Final


(** Check if an invocation to a method of a certain class is made. *)
let extract_InvocationClassName ~(classname:string) =
  fun (meth:Procname.t) -> raise NotYet


(** Does this method's name start with the given word? *)
let extract_MethodNameStartsWith ~(word:string) =
  fun (meth:Procname.t) -> raise NotYet


(** Is this method's name identical the given word? *)
let extract_MethodNameEquals ~(word:string) =
  fun (meth:Procname.t) -> raise NotYet


(** Does this method's name contain the given word? *)
let extract_MethodNameContains ~(word:string) =
  fun (meth:Procname.t) -> raise NotYet


(** Do any of the parameters' type contain the given name? *)
let extract_ParamContainsTypeOrName ~(name:string) =
  fun (meth:Procname.t) -> raise NotYet


(** Feature that checks whether a parameter flows to the sink. *)
let extract_ParamToSink ~(sink_name:string) =
  fun (meth:Procname.t) -> raise NotYet


(** Does the return type contain the given name? *)
let extract_ReturnTypeContainsName ~(name:string) =
  fun (meth:Procname.t) -> raise NotYet


(** Does the return type of the method equal to the type given? *)
let extract_ReturnType ~(type_name:string) =
  fun (meth:Procname.t) -> raise NotYet


(** Does the source method return one of its parameters
    (we are only interested in sources with one of the given names)? *)
let extract_SourceToReturn ~(source_name:string) =
  fun (meth:Procname.t) -> raise NotYet


(* Instantiated Higher-order Functions ============== *)
(* ================================================== *)


let classContainsName_features = [
  extract_ClassContainsName "Saniti"
; extract_ClassContainsName "Encod"
; extract_ClassContainsName "Escap"
; extract_ClassContainsName "Valid"
; extract_ClassContainsName "Check"
; extract_ClassContainsName "Verif"
; extract_ClassContainsName "Authen"
; extract_ClassContainsName "Security"
; extract_ClassContainsName "Connect"
; extract_ClassContainsName "Bind"
; extract_ClassContainsName "OAuth"
; extract_ClassContainsName ".io."
; extract_ClassContainsName "web"
; extract_ClassContainsName ".net."
; extract_ClassContainsName "sql"
; extract_ClassContainsName "Manager"
; extract_ClassContainsName "Output"
; extract_ClassContainsName "Input"
; extract_ClassContainsName "database"
; extract_ClassContainsName "db"
; extract_ClassContainsName "hibernate"
; extract_ClassContainsName "credential"
; extract_ClassContainsName "process"
; extract_ClassContainsName "runtime"
; extract_ClassContainsName "user"
; extract_ClassContainsName "jdbc"
; extract_ClassContainsName "Html"
; extract_ClassContainsName "Page"
; extract_ClassContainsName "Request"
; extract_ClassContainsName "http"
; extract_ClassContainsName "url"
; extract_ClassContainsName "servlet"
; extract_ClassContainsName "Response"
; extract_ClassContainsName "Redirect"
; extract_ClassContainsName "Css"
; extract_ClassContainsName "Dom"
]


let classEndsWithName_features = [
  extract_ClassEndsWithName "Encoder"
; extract_ClassEndsWithName "Request"
; extract_ClassEndsWithName "Render"
]


let classModifier_features = [
  extract_ClassModifier Static
; extract_ClassModifier Public
; extract_ClassModifier Final
]


let invocationClassName_features = [
  extract_InvocationClassName "Saniti"
; extract_InvocationClassName "regex"
; extract_InvocationClassName "escap"
; extract_InvocationClassName ".io."
; extract_InvocationClassName "encod"
; extract_InvocationClassName "sql"
; extract_InvocationClassName "db"
; extract_InvocationClassName "web"
; extract_InvocationClassName ".net."
; extract_InvocationClassName "Log."
]


let methodNameStartsWith_features = [
  extract_MethodNameStartsWith "get"
; extract_MethodNameStartsWith "set"
; extract_MethodNameStartsWith "put"
; extract_MethodNameStartsWith "has"
; extract_MethodNameStartsWith "is"
; extract_MethodNameStartsWith "open"
; extract_MethodNameStartsWith "close"
; extract_MethodNameStartsWith "create"
; extract_MethodNameStartsWith "delete"
]


let methodNameEquals_features = [
  extract_MethodNameEquals "log"
; extract_MethodNameEquals "setHeader"
; extract_MethodNameEquals "sendRedirect"
]


let methodNameContains = [
  extract_MethodNameContains "saniti"
; extract_MethodNameContains "escape"
; extract_MethodNameContains "unescape"
; extract_MethodNameContains "replac"
; extract_MethodNameContains "strip"
; extract_MethodNameContains "encod"
; extract_MethodNameContains "regex"
; extract_MethodNameContains "authen"
; extract_MethodNameContains "check"
; extract_MethodNameContains "verif"
; extract_MethodNameContains "privilege"
; extract_MethodNameContains "login"
; extract_MethodNameContains "loginpage"
; extract_MethodNameContains "logout"
; extract_MethodNameContains "connect"
; extract_MethodNameContains "disconnect"
; extract_MethodNameContains "bind"
; extract_MethodNameContains "unbind"
; extract_MethodNameContains "read"
; extract_MethodNameContains "thread"
; extract_MethodNameContains "load"
; extract_MethodNameContains "payload"
; extract_MethodNameContains "request"
; extract_MethodNameContains "creat"
; extract_MethodNameContains "decod"
; extract_MethodNameContains "unescap"
; extract_MethodNameContains "pars"
; extract_MethodNameContains "stream"
; extract_MethodNameContains "retriev"
; extract_MethodNameContains "Object"
; extract_MethodNameContains "Name"
; extract_MethodNameContains "writ"
; extract_MethodNameContains "updat"
; extract_MethodNameContains "send"
; extract_MethodNameContains "handl"
; extract_MethodNameContains "log"
; extract_MethodNameContains "run"
; extract_MethodNameContains "execut"
; extract_MethodNameContains "compile"
; extract_MethodNameContains "dump"
; extract_MethodNameContains "print"
; extract_MethodNameContains "execute"
; extract_MethodNameContains "query"
; extract_MethodNameContains "role"
; extract_MethodNameContains "authori"
; extract_MethodNameContains "redirect"
; extract_MethodNameContains "getParameter"
]


let paramContainsTypeOrName = [
  extract_ParamContainsTypeOrName "java.lang.String"
; extract_ParamContainsTypeOrName "char[]"
; extract_ParamContainsTypeOrName "byte[]"
; extract_ParamContainsTypeOrName "java.lang.CharSequence"
; extract_ParamContainsTypeOrName "java.lang.StringBuilder"
; extract_ParamContainsTypeOrName ".io."
; extract_ParamContainsTypeOrName "web"
; extract_ParamContainsTypeOrName "sql"
; extract_ParamContainsTypeOrName "db"
; extract_ParamContainsTypeOrName "credential"
; extract_ParamContainsTypeOrName "url"
]


let paramToSink = [
  extract_ParamToSink "writ"
; extract_ParamToSink "set"
; extract_ParamToSink "updat"
; extract_ParamToSink "send"
; extract_ParamToSink "handl"
; extract_ParamToSink "put"
; extract_ParamToSink "log"
; extract_ParamToSink "run"
; extract_ParamToSink "execut"
; extract_ParamToSink "dump"
; extract_ParamToSink "print"
; extract_ParamToSink "pars"
; extract_ParamToSink "stream"
]


let returnTypeContainsName = [
  extract_ReturnTypeContainsName "Document"
; extract_ReturnTypeContainsName "Node"
; extract_ReturnTypeContainsName "User"
; extract_ReturnTypeContainsName "Credential"
; extract_ReturnTypeContainsName "Servlet"
; extract_ReturnTypeContainsName "Request"
]


let returnType = [
  extract_ReturnType "byte[]"
; extract_ReturnType "java.lang.String"
; extract_ReturnType "java.lang.CharSequence"
; extract_ReturnType "boolean"
; extract_ReturnType "java.sql.ResultSet"
]


let sourceToReturn = [
  extract_SourceToReturn "get"
; extract_SourceToReturn "read"
; extract_SourceToReturn "decode"
; extract_SourceToReturn "unescape"
; extract_SourceToReturn "load"
; extract_SourceToReturn "request"
; extract_SourceToReturn "create"
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
  match find_pdesc meth with
  | Some pdesc ->
    output @@ not @@ Int.equal (List.length @@ Procdesc.get_formals @@ pdesc) 0
  | None -> DontKnow


(** Does this method have a return type? *)
let extract_HasReturnType =
  fun (meth:Procname.t) ->
  match find_pdesc meth with
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
  match find_pdesc meth with
  | Some pdesc ->
    let paramtypes = List.map ~f:snd @@ Procdesc.get_formals pdesc in
    let rtntype = get_ret_type in
    output @@ List.mem paramtypes rtntype ~equal:Typ.equal
  | None -> DontKnow


(** Check if an invocation to a certain method is made. *)
let extract_InvocationName =    (* TODO *)
  fun (meth:Procname.t) -> raise NotYet


(** Returns if the method is a constructor or not. *)
let extract_IsConstructor =
  fun (meth:Procname.t) ->
  Procname.is_constructor meth


(** Feature that checks whether the current method begins with "get", and there
    is a corresponding "set" method in the class. *)
let extract_IsRealSetter =      (* TODO *)
  fun (meth:Procname.t) -> raise NotYet


(** Feature checking the method modifiers *)
let extract_MethodModifier =
  fun (meth:Procname.t) -> raise NotYet


(** Feature that matches whenever a method returns void and the method name starts
    with "on". *)
let extract_VoidOnMethod =
  fun (meth:Procname.t) ->
  match find_pdesc meth with
  | Some pdesc ->
    Typ.is_void @@ Procdesc.get_ret_type pdesc && 
  | None -> DontKnow


(* Main ============================================ *)
(* ================================================= *)


let main () : unit =
  ()
