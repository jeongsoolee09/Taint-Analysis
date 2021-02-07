open! IStd

module ProcnameSet = Caml.Set.Make (Procname)
module Hashtbl = Caml.Hashtbl
module F = Format
module L = Logging

let all_procnames = SetofAllMeths.calculate_list ()

let exclude_keywords = In_channel.read_lines "exclude_keywords.txt"


(** A predicate that exploits the fact that
    get_formals fail on skip_functions *)
let is_skip_function procname =
  try
    ignore @@ Procdesc.load procname; (* OCaml uses strict eval strategy *)
    false
  with _ ->
    true


let callgraph = Hashtbl.create 777

 
let apis : Procname.t list =
  all_procnames
    (* An API is a bodiless function *)
  |> List.filter ~f:(fun proc -> is_skip_function proc)
    (* An API does not have any of the exclude_keywords *)
  |> List.filter ~f:(fun proc ->
      let proc_string = Procname.to_string proc in
      not @@ List.fold ~f:(fun acc keyword ->
          String.is_substring proc_string ~substring:keyword || acc)
        ~init:false exclude_keywords)


let count_occurrence_of_API (proc:Procname.t) : int =
  let cnt = ref 0 in
  List.iter apis ~f:(fun api ->
      Hashtbl.iter (fun _ v ->
          if Procname.equal v api then cnt := !cnt + 1) callgraph);
  !cnt

 
let count_occurrence_of_each_API () : (Procname.t * int) list =
  apis
    (* deduping *)
  |> ProcnameSet.of_list
  |> ProcnameSet.elements
    (* count'em all! *)
  |> List.map ~f:(fun proc -> (proc, count_occurrence_of_API proc))


let to_csv (api_count_list: (Procname.t * int) list) : unit =
  let to_csv_repr ((proc, cnt):Procname.t * int) : string list =
    [Procname.to_string proc; Int.to_string cnt] in
  let out_chan =
    Out_channel.create "API-count.csv"
    |> Csv.to_channel ~quote_all:false in
  Csv.output_all out_chan @@ List.map ~f:to_csv_repr api_count_list;
  Csv.close_out out_chan


let main () =
  MyCallGraph.load_callgraph_from_disk_to callgraph;
  to_csv @@ count_occurrence_of_each_API ()
