open! IStd
open DefLocAlias.TransferFunctions
open Yojson.Basic

module Hashtbl = Caml.Hashtbl

module F = Format
module L = Logging

type json = Yojson.Basic.t


let method_annot_table = Hashtbl.create 777


(** 디스크에서 pdesc를 읽어와서 해시테이블에 (Methname.t, annotation) 등록 *)
let load_annots_from_disk_to (hashtbl:(Procname.t, Annot.Method.t) Hashtbl.t) : unit =
  let all_source_files = SourceFiles.get_all ~filter:(fun _ -> true) () in
  let all_procnames_list = List.map ~f:SourceFiles.proc_names_of_source all_source_files in
  let all_procnames = List.concat all_procnames_list in
  let all_pnames_and_pdesc_opts = List.map ~f:(fun pname -> (pname,  Procdesc.load pname)) all_procnames in
  let all_pnames_and_pdesc_opts_ = List.filter ~f:(fun (_, opt) -> match opt with Some _ -> true | None -> false) all_pnames_and_pdesc_opts in
  let all_pnames_and_pdesc = catMaybes_tuplist all_pnames_and_pdesc_opts_ in
  let methods_and_annots = List.map ~f:(fun (p, pdesc) ->
      (p, (Procdesc.get_attributes pdesc).ProcAttributes.method_annotation)) all_pnames_and_pdesc in
  List.iter methods_and_annots ~f:(fun (k, annot) -> Hashtbl.add hashtbl k annot)


(** Hashtbl을 순회하면서 json repr로 바꾸기 **)
let to_json_repr (hashtbl:(Procname.t, Annot.Method.t) Hashtbl.t) : json =
  let to_key_attr meth annot =
    if not (Annot.Method.is_empty annot)
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
