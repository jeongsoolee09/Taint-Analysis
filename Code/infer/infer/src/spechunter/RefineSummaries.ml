open! IStd

(* open DefLocAliasPP *)
open DefLocAliasSearches
open DefLocAliasPredicates
open DefLocAliasDomain
open Partitioners

(* open DefLocAliasPP *)
module Hashtbl = Caml.Hashtbl
module P = DefLocAliasDomain.AbstractPair
module S = DefLocAliasDomain.AbstractStateSetFinite
module A = DefLocAliasDomain.SetofAliases
module T = DefLocAliasDomain.AbstractState
module L = Logging
module F = Format

(* Exceptions ======================================= *)
(* ================================================== *)

exception TODO

exception NotASingleton of string

exception TooManyMatches of string

exception ConsolidateByLocsetFailed of string

(** Return the first matching value for a key in a association list. *)
let rec assoc (alist : ('a * 'b) list) (key : 'a) ~equal : 'b =
  match alist with
  | [] ->
      raise (Failure "Could not find matching ones")
  | (key', value) :: t ->
      if equal key key' then value else assoc t key ~equal


(* Remove Class Initializers ======================== *)
(* ================================================== *)

let remove_clinit (table : (Procname.t, S.t) Hashtbl.t) : (Procname.t, S.t) Hashtbl.t =
  Hashtbl.iter (fun proc _ -> if is_clinit proc then Hashtbl.remove table proc) table ;
  table


(* Remove Ternary frontend vars ===================== *)
(* ================================================== *)

let remove_ternary_frontend (table : (Procname.t, S.t) Hashtbl.t) : (Procname.t, S.t) Hashtbl.t =
  let one_pass_S (astate_set : S.t) : S.t =
    S.fold
      (fun (proc, vardef, locset, aliasset) acc ->
        match is_ternary_frontend_ap vardef with
        | true ->
            acc
        | false ->
            S.add
              (proc, vardef, locset, A.filter (fun ap -> not @@ is_ternary_frontend_ap ap) aliasset)
              acc )
      astate_set S.empty
  in
  Hashtbl.iter (fun proc astate_set -> Hashtbl.replace table proc (one_pass_S astate_set)) table ;
  table


(* Consolidate duplicated Pvar tuples =============== *)
(* ================================================== *)

let consolidate_dup_pvars (table : (Procname.t, S.t) Hashtbl.t) : (Procname.t, S.t) Hashtbl.t =
  let one_pass_S (astate_set : S.t) : S.t =
    let pvar_astates =
      S.filter
        (fun astate ->
          let ap = second_of astate in
          (not @@ is_this_ap ap)
          && (not @@ is_placeholder_vardef (fst ap))
          && (not @@ is_returnv_ap ap)
          && (not @@ is_return_ap ap)
          && (not @@ is_param_ap ap)
          && (not @@ is_callv_ap ap) )
        astate_set
    in
    let non_pvar_astates = S.filter (fun astate -> not @@ S.mem astate pvar_astates) astate_set in
    let partitions = partition_statetups_by_vardef_and_locset pvar_astates in
    let partition_mapfunc (partition : S.t) : T.t =
      (* sanity check *)
      let proc, vardef, locset, aliasset = List.hd_exn @@ S.elements partition in
      let other_threes_are_all_equal =
        S.fold
          (fun (proc', vardef', locset', _) acc ->
            Procname.equal proc proc' && MyAccessPath.equal vardef vardef'
            && LocationSet.equal locset locset' && acc )
          partition true
      in
      assert other_threes_are_all_equal ;
      let aliasset_combined =
        S.fold (fun statetup acc -> A.union acc @@ fourth_of statetup) partition A.empty
      in
      (proc, vardef, locset, aliasset_combined)
    in
    let processed_pvar_astates = S.of_list @@ List.map partitions ~f:partition_mapfunc in
    S.union processed_pvar_astates non_pvar_astates
  in
  Hashtbl.iter (fun proc astate_set -> Hashtbl.replace table proc (one_pass_S astate_set)) table ;
  table


(* removing unimportant elements ==================== *)
(* ================================================== *)

let remove_unimportant_elems (table : (Procname.t, S.t) Hashtbl.t) : (Procname.t, S.t) Hashtbl.t =
  let filter_garbage_astate (tup : T.t) =
    let var, _ = second_of tup in
    (not @@ is_placeholder_vardef var) && (not @@ is_logical_var var)
  in
  let filter_garbage_aliastup (ap : MyAccessPath.t) =
    let var = fst ap in
    (not @@ is_placeholder_vardef var) && (not @@ is_logical_var var)
  in
  Hashtbl.iter
    (fun key summary ->
      let filtered_astates =
        S.filter filter_garbage_astate summary
        |> S.map (fun (proc, vardef, locset, aliasset) ->
               let filtered_aliastup = A.filter filter_garbage_aliastup aliasset in
               (proc, vardef, locset, filtered_aliastup) )
      in
      Hashtbl.replace table key filtered_astates )
    table ;
  table


(* Delete compensating parmas and returnvs ========== *)
(* ================================================== *)

(** Extract the callee's method name embedded in returnv, callv, or param. *)
let extract_callee_from (ap : MyAccessPath.t) =
  let special, _ = ap in
  match special with
  | LogicalVar _ ->
      L.die InternalError "extract_callee_from failed"
  | ProgramVar pv -> (
    match Pvar.get_declaring_function pv with
    | Some procname ->
        procname
    | None ->
        L.die InternalError "extract_callee_from failed" )


let delete_compensating_param_returnv (table : (Procname.t, S.t) Hashtbl.t) :
    (Procname.t, S.t) Hashtbl.t =
  let one_pass_A (aliasset : A.t) : A.t =
    let returnvs = A.elements @@ A.filter is_returnv_ap aliasset in
    let params = A.elements @@ A.filter is_param_ap aliasset in
    let carpro =
      let open List in
      returnvs >>= fun returnv -> params >>= fun param -> return (returnv, param)
    in
    let compensating_pairs =
      List.filter
        ~f:(fun (returnv, param) ->
          let returnv_meth_simple = Procname.get_method @@ extract_callee_from returnv in
          let param_meth_simple = Procname.get_method @@ extract_callee_from param in
          String.equal returnv_meth_simple param_meth_simple )
        carpro
    in
    let to_delete =
      List.fold ~f:(fun acc (returnv, param) -> returnv :: param :: acc) ~init:[] compensating_pairs
    in
    (* once we identified the compensating pairs, we remove them from the aliasset *)
    A.filter (fun alias_ap -> not @@ List.mem to_delete alias_ap ~equal:MyAccessPath.equal) aliasset
  in
  let one_pass_S (astate_set : S.t) : S.t =
    S.map
      (fun (proc, vardef, locset, aliasset) -> (proc, vardef, locset, one_pass_A aliasset))
      astate_set
  in
  Hashtbl.iter (fun proc astate_set -> Hashtbl.replace table proc (one_pass_S astate_set)) table ;
  table


(* Remove initializer calls ========================= *)
(* ================================================== *)

let delete_initializer_callv_param (table : (Procname.t, S.t) Hashtbl.t) :
    (Procname.t, S.t) Hashtbl.t =
  let one_pass_A (aliasset : A.t) : A.t =
    A.filter
      (fun ap ->
        not
          ( (is_callv_ap ap || is_param_ap ap)
          &&
          let procname = extract_callee_from ap in
          is_initializer procname ) )
      aliasset
  in
  let one_pass_S (astate_set : S.t) : S.t =
    S.map
      (fun (proc, vardef, locset, aliasset) -> (proc, vardef, locset, one_pass_A aliasset))
      astate_set
  in
  Hashtbl.iter (fun proc astate_set -> Hashtbl.replace table proc (one_pass_S astate_set)) table ;
  table


(* EXPERIMENTAL: consolidate all frontend temp vars by their LocationSet.ts *)
(* ================================================== *)

let consolidate_by_locset (table : (Procname.t, S.t) Hashtbl.t) : (Procname.t, S.t) Hashtbl.t =
  let one_pass_S (astate_set : S.t) : S.t =
    let irvars = S.filter (fun astate -> is_irvar_ap @@ second_of astate) astate_set in
    let pvars =
      S.filter
        (fun astate ->
          let ap = second_of astate in
          (not @@ is_this_ap ap)
          && (not @@ is_placeholder_vardef @@ fst ap)
          && (not @@ is_bcvar_ap ap)
          && (not @@ is_irvar_ap ap)
          && (not @@ is_returnv_ap ap)
          && (not @@ is_return_ap ap)
          && (not @@ is_param_ap ap)
          && (not @@ is_callv_ap ap) )
        astate_set
    in
    (* save this for merging later *)
    let rest = S.diff (S.diff astate_set irvars) pvars in
    let partitions = partition_statetups_by_locset irvars in
    try
      (* al iz wel *)
      let processed =
        S.of_list
        @@ List.map
             ~f:(fun (partition : S.t) ->
               let this_partition_locset = third_of @@ List.hd_exn @@ S.elements partition in
               let pvar_astate = search_astate_by_loc this_partition_locset (S.elements pvars) in
               S.fold
                 (fun astate (proc, vardef, locset, aliasset) ->
                   let aliasset' = fourth_of astate in
                   let aliasset_updated = A.remove vardef (A.union aliasset aliasset') in
                   (proc, vardef, locset, aliasset_updated) )
                 partition pvar_astate )
             partitions
      in
      let failed_pvars = S.filter (fun astate -> not @@ S.mem astate processed) pvars in
      S.union rest processed |> S.union failed_pvars
    with SearchAstateByLocFailed _ ->
      (* some trials are borken *)
      let process_succeeded, leftovers =
        List.fold
          ~f:(fun (succeeded_irvars, failed_irvars) partition ->
            let this_partition_locset = third_of @@ List.hd_exn @@ S.elements partition in
            let pvar_astates = search_tuples_by_loc this_partition_locset (S.elements pvars) in
            match pvar_astates with
            | [] ->
                (succeeded_irvars, S.union failed_irvars partition)
            | [pvar_astate] ->
                ( S.add
                    (S.fold
                       (fun astate (proc, vardef, locset, aliasset) ->
                         let aliasset' = fourth_of astate in
                         let aliasset_updated = A.remove vardef (A.union aliasset aliasset') in
                         (proc, vardef, locset, aliasset_updated) )
                       partition pvar_astate )
                    succeeded_irvars
                , failed_irvars )
            | _ ->
                F.kasprintf
                  (fun msg -> raise @@ ConsolidateByLocsetFailed msg)
                  "consolidate_by_locset failed. astate_set: %a@." S.pp astate_set )
          ~init:(S.empty, S.empty) partitions
      in
      (* We now extract only the failed pvars *)
      let failed_pvars = S.filter (fun astate -> not @@ S.mem astate process_succeeded) pvars in
      process_succeeded |> S.union rest |> S.union leftovers |> S.union failed_pvars
  in
  (* one_pass_S end *)
  Hashtbl.iter (fun proc astate_set -> Hashtbl.replace table proc (one_pass_S astate_set)) table ;
  table


(* Remove unnecessary Java constants ================ *)
(* ================================================== *)

let remove_java_constants (table : (Procname.t, S.t) Hashtbl.t) : (Procname.t, S.t) Hashtbl.t =
  let one_pass_S (astate_set : S.t) : S.t =
    S.fold
      (fun ((proc, vardef, locset, aliasset) as astate) acc ->
        (* Hopefully this list will grow... *)
        let java_constant_var_string = ["lang.System"] in
        let vardef_is_java_constant =
          let var_string = F.asprintf "%a" Var.pp (fst vardef) in
          List.mem java_constant_var_string var_string ~equal:String.equal
        and aliasset_has_java_constant =
          A.exists
            (fun ap ->
              let ap_string = F.asprintf "%a" Var.pp (fst ap) in
              List.mem java_constant_var_string ap_string ~equal:String.equal )
            aliasset
        in
        if vardef_is_java_constant then acc
        else if aliasset_has_java_constant then
          let updated_aliasset =
            A.filter
              (fun ap ->
                let ap_string = F.asprintf "%a" Var.pp (fst ap) in
                not @@ List.mem java_constant_var_string ap_string ~equal:String.equal )
              aliasset
          in
          S.add (proc, vardef, locset, updated_aliasset) acc
        else S.add astate acc )
      astate_set S.empty
  in
  Hashtbl.iter (fun proc astate_set -> Hashtbl.replace table proc (one_pass_S astate_set)) table ;
  table


(* Return =========================================== *)
(* ================================================== *)

let return (table : (Procname.t, S.t) Hashtbl.t) : unit = ()

(* For debugging ==================================== *)
(* ================================================== *)

let print_summary_table table =
  L.progress "==================== printing from RefineSummaries! ====================@." ;
  Hashtbl.iter
    (fun proc summary ->
      L.progress "procname: %a, " Procname.pp proc ;
      L.progress "summary: %a@." S.pp summary )
    table ;
  L.progress "========================================================================@."


let summary_table_to_file_and_return (filename : string) (table : (Procname.t, S.t) Hashtbl.t) :
    (Procname.t, S.t) Hashtbl.t =
  let out_chan = Out_channel.create filename in
  Hashtbl.iter
    (fun proc astate_set ->
      let proc_string = Procname.to_string proc in
      let astate_set_string = F.asprintf "%a" S.pp astate_set in
      let string_to_write =
        F.asprintf "Summary for %s: ========================@. %s@.@." proc_string astate_set_string
      in
      Out_channel.output_string out_chan string_to_write )
    table ;
  Out_channel.close out_chan ;
  table


(* Main ============================================= *)
(* ================================================== *)

let main : (Procname.t, S.t) Hashtbl.t -> unit =
 fun table ->
  table
  |> summary_table_to_file_and_return "1_raw_astate_set.txt"
  |> remove_clinit
  |> summary_table_to_file_and_return "2_remove_clinit.txt"
  |> remove_ternary_frontend
  |> summary_table_to_file_and_return "3_remove_ternary_frontend.txt"
  |> consolidate_dup_pvars
  |> summary_table_to_file_and_return "4_consolidate_dup_pvars.txt"
  (* |> consolidate_by_locset *)
  (* |> summary_table_to_file_and_return "5_consolidate_by_locset.txt" *)
  (* |> delete_initializer_callv_param *)
  (* |> summary_table_to_file_and_return "6_delete_initizalizer_callv_param.txt" *)
  |> remove_unimportant_elems
  |> summary_table_to_file_and_return "7_remove_unimportant_elems.txt"
  |> remove_java_constants
  |> summary_table_to_file_and_return "8_remove_java_constants.txt"
  |> return
