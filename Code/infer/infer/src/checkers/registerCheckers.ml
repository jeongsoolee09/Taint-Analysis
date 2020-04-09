(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd

(** Module for registering checkers. *)

module F = Format

(* make sure SimpleChecker.ml is not dead code *)
let () =
  if false then
    let module SC = SimpleChecker.Make in
    ()


type callback_fun =
  | Procedure of Callbacks.proc_callback_t
  | DynamicDispatch of Callbacks.proc_callback_t
  | Cluster of Callbacks.cluster_callback_t

type callback = callback_fun * Language.t

type checker = {name: string; active: bool; callbacks: callback list}

let all_checkers =
  (* TODO (T24393492): the checkers should run in the order from this list.
     Currently, the checkers are run in the reverse order *)
  [    { name= "Value Definitions, Locations of Definitions, and Aliases"
    ; active= Config.def_loc_alias
    ; callbacks= [ (Procedure DefLocAlias.checker, Language.Clang)
                 ; (Procedure DefLocAlias.checker, Language.Java)] }
  ]
(* IDK :P *)

let get_active_checkers () =
  let filter_checker {active} = active in
  List.filter ~f:filter_checker all_checkers


let register checkers =
  let register_one {name; callbacks} =
    let register_callback (callback, language) =
      match callback with
      | Procedure procedure_cb ->
          Callbacks.register_procedure_callback ~name language procedure_cb
      | DynamicDispatch procedure_cb ->
          Callbacks.register_procedure_callback ~name ~dynamic_dispatch:true language procedure_cb
      | Cluster cluster_cb ->
          Callbacks.register_cluster_callback ~name language cluster_cb
    in
    List.iter ~f:register_callback callbacks
  in
  List.iter ~f:register_one checkers


module LanguageSet = Caml.Set.Make (Language)

let pp_checker fmt {name; callbacks} =
  let langs_of_callbacks =
    List.fold_left callbacks ~init:LanguageSet.empty ~f:(fun langs (_, lang) ->
        LanguageSet.add lang langs )
    |> LanguageSet.elements
  in
  F.fprintf fmt "%s (%a)" name
    (Pp.seq ~sep:", " (Pp.of_string ~f:Language.to_string))
    langs_of_callbacks
