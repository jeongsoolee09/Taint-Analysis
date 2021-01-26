open! IStd

module L = Logging
module F = Format
module D = DefLocAlias


(** 대상 SourceFile에 들어 있는 Set of all method를 계산한다. *)
let calculate () =
  let out_channel = Out_channel.create "Methods.txt" in
    SourceFiles.get_all ~filter:(fun _ -> true) ()
    |> List.map ~f:SourceFiles.proc_names_of_source
    |> List.concat
    |> List.map ~f:Procname.to_string
    |> List.iter ~f:(fun str ->
        Out_channel.output_string out_channel @@ str ^"\n" )


let calculate_list () : Procname.t list =
  SourceFiles.get_all ~filter:(fun _ -> true) ()
  |> List.map ~f:SourceFiles.proc_names_of_source
  |> List.concat
