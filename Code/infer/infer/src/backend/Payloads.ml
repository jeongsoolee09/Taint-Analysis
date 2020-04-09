(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
module F = Format

type t =
  { def_loc_alias: DefLocAliasDomain.summary option
  }
[@@deriving fields]

let poly_fields = PolyFields.make Fields.map_poly

type 'a pp = Pp.env -> F.formatter -> 'a -> unit

type field = F : {field: (t, 'a option) Field.t; name: string; pp: 'a pp} -> field

let fields =
  let mk field name pp = F {field; name; pp= (fun _ -> pp)} in
  let mk_pe field name pp = F {field; name; pp} in
  Fields.to_list
    ~def_loc_alias:(fun f -> mk f "def/loc/alias" DefLocAliasDomain.pp)


let pp pe f payloads =
  List.iter fields ~f:(fun (F {field; name; pp}) ->
      Field.get field payloads |> Option.iter ~f:(fun x -> F.fprintf f "%s: %a@\n" name (pp pe) x)
  )


let empty =
  { def_loc_alias= None}
