open! IStd
open DefLocAliasDomain
open Yojson.Basic
module S = DefLocAliasDomain.AbstractStateSetFinite
module A = DefLocAliasDomain.SetofAliases
module L = Logging
module F = Format
module Hashtbl = Caml.Hashtbl

type json = Yojson.Basic.t

let method_summary_table = Hashtbl.create 777

let get_summary (key : Procname.t) : S.t =
  match Hashtbl.find_opt method_summary_table key with None -> S.empty | Some res -> res


let return_stmt_locset_table = Hashtbl.create 777

let get_return_stmt_locset (key : Procname.t) : LocationSet.t =
  match Hashtbl.find_opt return_stmt_locset_table key with
  | None ->
      LocationSet.empty
  | Some res ->
      res


let find_return_stmt_locset (key : Procname.t) (summary : S.t) : LocationSet.t =
  let acc = ref LocationSet.empty in
  S.iter
    (fun (_, _, locset, aliasset) ->
      if A.exists (fun (var, _) -> Var.is_return var) aliasset then
        acc := LocationSet.union !acc locset )
    summary ;
  !acc


let make_json_repr (proc : Procname.t) (locset : LocationSet.t) : string * json =
  ( Procname.to_string proc
  , `List
      (List.map
         ~f:(fun locset -> `String (Location.to_string locset))
         (LocationSet.elements locset) ) )


let main () : unit =
  L.progress "Detecting locations of return statements...\n" ;
  SummaryLoader.load_summary_from_disk_to method_summary_table ~exclude_test:true ;
  Hashtbl.iter
    (fun proc summary ->
      let proc_return_stmt_locset = find_return_stmt_locset proc summary in
      Hashtbl.add return_stmt_locset_table proc proc_return_stmt_locset )
    method_summary_table ;
  let json_repr_set =
    Hashtbl.fold
      (fun proc locset acc -> make_json_repr proc locset :: acc)
      return_stmt_locset_table []
  in
  let out_channel = Out_channel.create "return_stmt_locations.json" in
  pretty_to_channel out_channel (`Assoc json_repr_set) ;
  Out_channel.close out_channel ;
  L.progress "Detecting locations of return statements...done\n"
