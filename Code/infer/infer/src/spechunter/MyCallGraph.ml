(** A Very Naive Call Graph Module:
 *   각 파일의 각 Procdesc.t의 각 노드의 각 instr를 뽑아서 해당 메소드의 콜리를 계산해 낸다. **)

open! IStd

open DefLocAliasPredicates

module Hashtbl = Caml.Hashtbl
module Map = Caml.Map.Make (Procname)
module L = Logging


let rec catMaybes_tuplist (optlist:('a*'b option) list) : ('a*'b) list =
  match optlist with
  | [] -> []
  | (sth1, Some sth2) :: t -> (sth1, sth2)::catMaybes_tuplist t
  | (_, None) :: _ -> L.die InternalError "catMaybes_tuplist failed"


(** load callgraph from disk to the given hashtable. *)
let load_callgraph_from_disk_to hashtbl ~(exclude_test: bool) =
  let callees_and_callers =
    SourceFiles.get_all ~filter:(fun _ -> true) ()
    |> List.map ~f:SourceFiles.proc_names_of_source
    |> List.concat
    |> List.map ~f:(fun pname ->
           (pname, Procdesc.load pname))
    |> List.filter ~f:(fun (_, opt) ->
           Option.is_some opt)
    |> catMaybes_tuplist
    |> List.map ~f:(fun (p, pdesc) ->
           (p, Procdesc.get_static_callees pdesc)) in
  List.iter callees_and_callers ~f:(fun (k, values) ->
    List.iter ~f:(fun v ->
        match exclude_test, (is_test_method k || is_test_method v) with
          | true, true -> ()
          | true, false -> Hashtbl.add hashtbl k v
          | false, true -> Hashtbl.add hashtbl k v
          | false, false -> Hashtbl.add hashtbl k v ) values)


(** The map version of the above. *)
let load_callgraph_from_disk_to_map map =
  let callees_and_callers =
    SourceFiles.get_all ~filter:(fun _ -> true) ()
    |> List.map ~f:SourceFiles.proc_names_of_source
    |> List.concat
    |> List.map ~f:(fun pname ->
        (pname, Procdesc.load pname))
    |> List.filter ~f:(fun (_, opt) ->
        Option.is_some opt)
    |> catMaybes_tuplist
    |> List.map ~f:(fun (p, pdesc) ->
        (p, Procdesc.get_static_callees pdesc)) in
  List.fold ~f:(fun acc (caller, callees) ->
      List.fold ~f:(fun acc_ callee ->
          Map.add caller callee acc_) ~init:acc callees) ~init:map callees_and_callers
