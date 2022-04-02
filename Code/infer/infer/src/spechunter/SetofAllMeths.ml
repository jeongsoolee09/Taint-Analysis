open! IStd

module L = Logging
module F = Format
module D = DefLocAlias


(** 대상 SourceFile에 들어 있는 Set of all method를 계산한다. *)
let calculate_unique_id () =
  let out_channel = Out_channel.create "UDFs_unique_id.txt" in
    SourceFiles.get_all ~filter:(fun _ -> true) ()
    |> List.map ~f:SourceFiles.proc_names_of_source
    |> List.concat
    |> List.map ~f:(fun procname -> F.asprintf "%a" Procname.pp_unique_id procname)
    |> List.iter ~f:(fun str ->
        Out_channel.output_string out_channel @@ str ^"\n" )


let calculate_methname () =
  let out_channel = Out_channel.create "UDFs.txt" in
  SourceFiles.get_all ~filter:(fun _ -> true) ()
  |> List.map ~f:SourceFiles.proc_names_of_source
  |> List.concat
  |> List.map ~f:(fun procname -> F.asprintf "%s" (Procname.to_string procname))
  |> List.iter ~f:(fun str ->
      Out_channel.output_string out_channel @@ str ^"\n" )
