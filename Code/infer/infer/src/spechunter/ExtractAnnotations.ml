open! IStd
open Yojson.Basic

module Hashtbl = Caml.Hashtbl

module F = Format
module L = Logging

type json = Yojson.Basic.t


let method_annot_table = Hashtbl.create 777


let rec catMaybes_tuplist (optlist:('a*'b option) list) : ('a*'b) list =
  match optlist with
  | [] -> []
  | (sth1, Some sth2) :: t -> (sth1, sth2)::catMaybes_tuplist t
  | (_, None) :: _ -> L.die InternalError "catMaybes_tuplist failed"


(** 디스크에서 pdesc를 읽어와서 해시테이블에 (Methname.t, annotation) 등록 *)
let load_annots_from_disk_to (hashtbl:(Procname.t, Annot.Method.t) Hashtbl.t) : unit =
  let methods_and_annots =
    SourceFiles.get_all ~filter:(fun _ -> true) ()
    |> List.map ~f:SourceFiles.proc_names_of_source
    |> List.concat
    |> List.map ~f:(fun pname ->
        (pname, Procdesc.load pname))
    |> List.filter ~f:(fun (_, opt) ->
        Option.is_some opt)
    |> catMaybes_tuplist
    |> List.map ~f:(fun (p, pdesc) ->
        (p, (Procdesc.get_attributes pdesc).ProcAttributes.method_annotation)) in
  List.iter methods_and_annots ~f:(fun (k, annot) -> Hashtbl.add hashtbl k annot)


(** Hashtbl을 순회하면서 json repr로 바꾸기 **)
let to_json_repr (hashtbl:(Procname.t, Annot.Method.t) Hashtbl.t) : json =
  let to_key_attr meth annot =
    if not @@ Annot.Method.is_empty annot
    then (Procname.to_string meth, `String (F.asprintf "%a" (Annot.Method.pp "") annot))
    else (Procname.to_string meth, `String "no annotation") in
  let key_attr_list = Hashtbl.fold (fun k v acc ->
      (to_key_attr k v)::acc) hashtbl [] in
  `Assoc key_attr_list


let write_json_to_file (json_repr:json) : unit =
  let out_channel = Out_channel.create "Annotations.json" in
  to_channel out_channel json_repr;
  Out_channel.flush out_channel;
  Out_channel.close out_channel


let main () : unit =
  L.progress "Extracting Annotations from methods...\n";
  load_annots_from_disk_to method_annot_table;
  let json_repr = to_json_repr method_annot_table in
  write_json_to_file json_repr;
  L.progress "Extracting Annotations from methods...done\n"
