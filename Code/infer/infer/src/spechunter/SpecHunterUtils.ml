open! IStd

(** Util functions *)

module L = Logging
module F = Format

exception FindIndexFailed

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


let find_index_of (elem : 'a) (lst : 'a list) ~(equal : 'a -> 'a -> bool) : int =
  let rec inner (acc : int) (lst : 'a list) =
    match lst with
    | [] ->
        raise FindIndexFailed
    | h :: t ->
        if equal h elem then acc else inner (acc + 1) t
  in
  inner 0 lst
