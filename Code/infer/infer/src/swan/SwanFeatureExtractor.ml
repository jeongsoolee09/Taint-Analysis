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


let classContainsName_args = [
  "Saniti"
; "Encod"
; "Escap"
; "Valid"
; "Check"
; "Verif"
; "Authen"
; "Security"
; "Connect"
; "Bind"
; "OAuth"
; ".io."
; "web"
; ".net."
; "sql"
; "Manager"
; "Output"
; "Input"
; "database"
; "db"
; "hibernate"
; "credential"
; "process"
; "runtime"
; "user"
; "jdbc"
; "Html"
; "Page"
; "Request"
; "http"
; "url"
; "servlet"
; "Response"
; "Redirect"
; "Css"
; "Dom"
]


let classEndsWithName_features = [
  "Encoder"
; "Request"
; "Render"
]


let classModifier = [
  "static"
; "public"
; "final"
]


let invocationClassName = [
  "Saniti"
; "regex"
; "escap"
; ".io."
; "encod"
; "sql"
; "db"
; "web"
; ".net."
; "Log."
]


let methodNameStartsWith = [
  "get"
; "set"
; "put"
; "has"
; "is"
; "open"
; "close"
; "create"
; "delete"
]


let methodNameEquals = [
  "log"
; "setHeader"
; "sendRedirect"
]


let methodNameContains = [
  "saniti"
; "escape"
; "unescape"
; "replac"
; "strip"
; "encod"
; "regex"
; "authen"
; "check"
; "verif"
; "privilege"
; "login"
; "loginpage"
; "logout"
; "connect"
; "disconnect"
; "bind"
; "unbind"
; "read"
; "thread"
; "load"
; "payload"
; "request"
; "creat"
; "decod"
; "unescap"
; "pars"
; "stream"
; "retriev"
; "Object"
; "Name"
; "writ"
; "updat"
; "send"
; "handl"
; "log"
; "run"
; "execut"
; "compile"
; "dump"
; "print"
; "execute"
; "query"
; "role"
; "authori"
; "redirect"
; "getParameter"
]


let paramContainsTypeOrName = [
  "java.lang.String"
; "char[]"
; "byte[]"
; "java.lang.CharSequence"
; "java.lang.StringBuilder"
; ".io."
; "web"
; "sql"
; "db"
; "credential"
; "url"
]


let paramToSink = [
  "writ"
; "set"
; "updat"
; "send"
; "handl"
; "put"
; "log"
; "run"
; "execut"
; "dump"
; "print"
; "pars"
; "stream"
]


let returnTypeContainsName = [
  "Document"
; "Node"
; "User"
; "Credential"
; "Servlet"
; "Request"
]


let returnType = [
  "byte[]"
; "java.lang.String"
; "java.lang.CharSequence"
; "boolean"
; "java.sql.ResultSet"
]


let sourceToReturn = [
  "get"
; "read"
; "decode"
; "unescape"
; "load"
; "request"
; "create"
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
