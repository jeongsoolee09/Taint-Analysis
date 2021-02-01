open! IStd

module Hashtbl = Caml.Hashtbl
module Map = Caml.Map.Make (Procname)
module L = Logging


let rec catMaybes_tuplist (optlist:('a*'b option) list) : ('a*'b) list =
  match optlist with
  | [] -> []
  | (sth1, Some sth2) :: t -> (sth1, sth2)::catMaybes_tuplist t
  | (_, None)::_ -> L.die InternalError "catMaybes_tuplist failed"


(** 디스크에서 써머리를 읽어와서 해시테이블에 정리 *)
let load_summary_from_disk_to hashtbl =
  SourceFiles.get_all ~filter:(fun _ -> true) ()
  |> List.map ~f:SourceFiles.proc_names_of_source
  |> List.concat
  |> List.map ~f:(fun proc -> (proc, Summary.OnDisk.get proc))
  |> List.filter ~f:(fun (_, summ) -> Option.is_some summ)
  |> catMaybes_tuplist
  |> List.map ~f:(fun (proc, summ) ->
      (proc, summ.Summary.payloads.def_loc_alias))
  |> catMaybes_tuplist
  |> List.map ~f:(fun (x, (y, _)) -> (x, y))
  |> List.iter ~f:(fun (proc, astate) ->
      Hashtbl.add hashtbl proc astate)


(** The map version of the above. *) 
let load_summary_from_disk_to_map map =
  SourceFiles.get_all ~filter:(fun _ -> true) ()
  |> List.map ~f:SourceFiles.proc_names_of_source
  |> List.concat
  |> List.map ~f:(fun proc -> (proc, Summary.OnDisk.get proc))
  |> List.filter ~f:(fun (_, summ) -> Option.is_some summ)
  |> catMaybes_tuplist
  |> List.map ~f:(fun (proc, summ) ->
      (proc, summ.Summary.payloads.def_loc_alias))
  |> catMaybes_tuplist
  |> List.map ~f:(fun (x, (y, _)) -> (x, y))
  |> List.fold ~f:(fun acc (proc, astate) ->
      Map.add proc astate acc) ~init:map
