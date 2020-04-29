open! IStd

module L = Logging
module F = Format
module D = DefLocAlias


(** 대상 SourceFile에 들어 있는 Set of all method를 계산한다. *)
let calculate () =
  let all_source_files = SourceFiles.get_all ~filter:(fun _ -> true) () in
  let all_procnames_listlist = List.map ~f:SourceFiles.proc_names_of_source all_source_files in
  (* 아직은 파일이 하나밖에 없으니까 *)
  let all_procnames = List.concat all_procnames_listlist in
  let all_procnames_str = List.map ~f:Procname.to_string all_procnames in
  let out_channel = Out_channel.create "Methods.txt" in
  List.iter ~f:(fun str -> Out_channel.output_string out_channel @@ str ^"\n" ) all_procnames_str
