open! IStd

(** Util functions *)

module L = Logging
module F = Format

exception FindIndexFailed

exception NoWitness

let option_get : 'a option -> 'a = function
  | None ->
      L.die InternalError "Given option is empty"
  | Some elem ->
      elem


let rec catMaybes (optlist : 'a option list) : 'a list =
  match optlist with
  | [] ->
      []
  | None :: rest ->
      catMaybes rest
  | Some x :: rest ->
      x :: catMaybes rest


let get_class_name (procname : Procname.t) : string =
  match Procname.get_class_name procname with
  | None ->
      ""
  | Some raw_class_name ->
      List.last_exn @@ String.split ~on:' ' @@ List.hd_exn @@ String.split ~on:'.' raw_class_name


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


(** Find the *first* element to match the predicate *)
let find_witness_exn (lst : 'a list) ~(pred : 'a -> bool) : 'a =
  let opt =
    List.fold_left ~f:(fun acc elem -> if pred elem then Some elem else acc) ~init:None
    @@ List.rev lst
  in
  match opt with
  | None ->
      F.kasprintf
        (fun msg ->
          L.progress "%s@." msg ;
          raise NoWitness )
        "find_witness_exn failed.@."
  | Some elem ->
      elem


let ( >> ) f g x = g (f x)

let ( << ) f g x = f (g x)
