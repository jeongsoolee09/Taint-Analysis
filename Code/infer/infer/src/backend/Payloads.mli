(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd

include sig
  (* ignore dead modules added by @@deriving fields *)
  [@@@warning "-60"]

  (** analysis results *)
  type t =
    { def_loc_alias: DefLocAliasDomain.summary option}
  [@@deriving fields]
end

val pp : Pp.env -> Format.formatter -> t -> unit

val empty : t

val poly_fields : t PolyFields.t
