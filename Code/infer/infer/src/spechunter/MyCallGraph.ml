(** A Very Naive Call Graph Module:
 *   각 파일의 각 Procdesc.t의 각 노드의 각 instr를 뽑아서 해당 메소드의 콜리를 계산해 낸다. **)

open! IStd
open DefLocAlias.TransferFunctions
open DefLocAliasSearches
open DefLocAliasLogicTests
open DefLocAliasDomain

module Hashtbl = Caml.Hashtbl
module S = DefLocAliasDomain.AbstractState
module A = DefLocAliasDomain.SetofAliases

module L = Logging
module F = Format

exception NotImplemented
exception IDontKnow


(* Procdesc.get_static_callees*)
(* Procdesc.SQLite.load *)
(** 디스크에서 써머리를 읽어와서 해시테이블에 정리 *)
let load_summary_from_disk_to hashtbl : unit =
  let all_source_files = SourceFiles.get_all ~filter:(fun _ -> true) () in
  let all_procnames_list = List.map ~f:SourceFiles.proc_names_of_source all_source_files in
  (* 아직은 파일이 하나밖에 없으니까 *)
  let all_procnames = List.concat all_procnames_list in
  let all_pnames_and_pdesc_opts = List.map ~f:(fun pname -> (pname,  Procdesc.load pname)) all_procnames in
  let all_pnames_and_pdesc_opts_ = List.filter ~f:(fun (_, opt) -> match opt with Some _ -> true | None -> false) all_pnames_and_pdesc_opts in
  let all_pnames_and_pdecs = catMaybes_tuplist all_pnames_and_pdesc_opts_  in
  let callees_and_callers = List.map ~f:(fun (p, pdesc) -> (p, Procdesc.get_static_callees pdesc)) all_pnames_and_pdecs in
  List.iter callees_and_callers ~f:(fun (k,v) -> Hashtbl.add hashtbl k v)