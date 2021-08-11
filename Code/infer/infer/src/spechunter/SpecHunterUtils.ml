open! IStd

(** Util functions *)

module L = Logging
module F = Format

let option_get : 'a option -> 'a = function
  | None ->
      L.die InternalError "Given option is empty"
  | Some elem ->
      elem


let rec catMaybes_tuplist (optlist : ('a * 'b option) list) : ('a * 'b) list =
  match optlist with
  | [] ->
      []
  | (sth1, Some sth2) :: t ->
      (sth1, sth2) :: catMaybes_tuplist t
  | (_, None) :: t ->
      catMaybes_tuplist t
