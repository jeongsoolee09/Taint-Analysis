open! IStd
open DefLocAlias

module Hashtbl = Caml.Hashtbl
module S = DefLocAliasDomain.AbstractState
module A = DefLocAliasDomain.SetofAliases

module L = Logging
module F = Format

exception NotImplemented

(** map from procname to its formal args. *)
let formal_args = Hashtbl.create 777

let add_formal_args (key:Procname.t) (value:Var.t list) = Hashtbl.add formal_args key value

let get_formal_args (key:Procname.t) = Hashtbl.find formal_args key

let rec batch_add_to_formals (key:Procname.t) (values:Var.t list list)  =
  match values with
  | [] -> ()
  | h::t -> add_formal_args key h; batch_add_to_formals key t

(** collect all formals from a summary *)
let collect_formals summary =
  let astates = S.elements summary in
  raise NotImplemented
  
(** filter all formals from a summary *)
(* let filter_formals *)
