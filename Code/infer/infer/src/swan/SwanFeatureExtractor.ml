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

module L = Logging
module F = Format


(* Higher-order features ============================ *)
(* ================================================== *)


(** Is the method part of class that contains the given name? *)
let extract_ClassContainsName ~(name:string) =
  fun (meth:Procname.t) -> raise NotYet


(** Is the method part of class that ends with the given name? *)
let extract_ClassEndsWithName ~(name:string) =
  fun (meth:Procname.t) -> raise NotYet


(** This feature checks the modifier of the class where the method is part of. *)
let extract_ClassModifier ~(modifier:string) =
  fun (meth:Procname.t) -> raise NotYet


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
  extract_ClassModifier "static"
; extract_ClassModifier "public"
; extract_ClassModifier "final"
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
  fun (meth:Procname.t) -> raise NotYet


(** This feature checks wether the method is part of an anonymous class or not. *)
let extract_AnonymousClass =
  fun (meth:Procname.t) -> raise NotYet


(** Does this method have parameters? *)
let extract_HasParameters =
  fun (meth:Procname.t) -> raise NotYet


(** Does this method have a return type? *)
let extract_HasReturnType =
  fun (meth:Procname.t) -> raise NotYet


(** Is the method part of an inner class? *)
let extract_InnerClass =
  fun (meth:Procname.t) -> raise NotYet


(** Does this method return a constant? *)
let extract_ReturnsConstant =
  fun (meth:Procname.t) -> raise NotYet


(** Feature that checks wether a parameter flows to return value. *)
let extract_ParaFlowsToReturn =
  fun (meth:Procname.t) -> raise NotYet


(** Does any of the parameters match the return type? *)
let extract_ParamTypeMatchesReturnType =
  fun (meth:Procname.t) -> raise NotYet


(** Check if an invocation to a certain method is made. *)
let extract_InvocationName =
  fun (meth:Procname.t) -> raise NotYet


(** Returns if the method is a constructor or not. *)
let extract_IsConstructor =
  fun (meth:Procname.t) -> raise NotYet


(** Feature that checks whether the current method begins with "get", and there
    is a corresponding "set" method in the class. *)
let extract_IsRealSetter =
  fun (meth:Procname.t) -> raise NotYet


(** Feature checking the method modifiers *)
let extract_MethodModifier =
  fun (meth:Procname.t) -> raise NotYet


(** Feature that matches whever a method returns void and the method name starts
    with "on". *)
let extract_VoidOnMethod =
  fun (meth:Procname.t) -> raise NotYet


(* Main ============================================ *)
(* ================================================= *)


let main () : unit =
  ()
