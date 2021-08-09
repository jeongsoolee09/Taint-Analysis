open! IStd
open DefLocAliasPP
open DefLocAliasSearches
open DefLocAliasPredicates
open DefLocAliasDomain

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

(* Partitioners ===================================== *)
(* ================================================== *)

let partition_statetups_by_procname (statetups : S.t) : S.t list =
  let procnames =
    List.stable_dedup
    @@ S.fold
         (fun astate acc ->
           let procname = first_of astate in
           procname :: acc)
         statetups []
  in
  List.fold
    ~f:(fun acc procname ->
      let matches =
        S.fold
          (fun statetup acc' ->
            if Procname.equal procname (first_of statetup) then S.add statetup acc' else acc')
          statetups S.empty
      in
      matches :: acc)
    ~init:[] procnames


let partition_statetups_by_vardef (statetups : S.t) : S.t list =
  let vardefs =
    List.stable_dedup
    @@ S.fold
         (fun astate acc ->
           let vardef = second_of astate in
           vardef :: acc)
         statetups []
  in
  List.fold
    ~f:(fun acc vardef ->
      let matches =
        S.fold
          (fun statetup acc' ->
            if MyAccessPath.equal vardef (second_of statetup) then S.add statetup acc' else acc')
          statetups S.empty
      in
      matches :: acc)
    ~init:[] vardefs


let partition_statetups_by_locset (statetups : S.t) : S.t list =
  let locsets : LocationSet.t list =
    List.stable_dedup
    @@ S.fold
         (fun astate acc ->
           let locset = third_of astate in
           locset :: acc)
         statetups []
  in
  List.fold
    ~f:(fun acc locset ->
      let matches =
        S.fold
          (fun statetup acc' ->
            if LocationSet.equal locset (third_of statetup) then S.add statetup acc' else acc')
          statetups S.empty
      in
      matches :: acc)
    ~init:[] locsets


let partition_statetups_by_aliasset (statetups : S.t) : S.t list =
  let locsets =
    List.stable_dedup
    @@ S.fold
         (fun astate acc ->
           let aliasset = fourth_of astate in
           aliasset :: acc)
         statetups []
  in
  List.fold
    ~f:(fun acc locset ->
      let matches =
        S.fold
          (fun statetup acc' ->
            if A.equal locset (fourth_of statetup) then S.add statetup acc' else acc')
          statetups S.empty
      in
      matches :: acc)
    ~init:[] locsets


let partition_statetups_by_vardef_and_locset (statetups : S.t) : S.t list =
  let vardefs =
    List.stable_dedup
    @@ S.fold
         (fun astate acc ->
           let vardef = second_of astate in
           vardef :: acc)
         statetups []
  in
  let locsets : LocationSet.t list =
    List.stable_dedup
    @@ S.fold
         (fun astate acc ->
           let locset = third_of astate in
           locset :: acc)
         statetups []
  in
  let vardef_locset_pairs =
    let open List in
    vardefs >>= fun vardef -> locsets >>= fun locset -> return (vardef, locset)
  in
  List.fold
    ~f:(fun acc (vardef, locset) ->
      let matches =
        S.fold
          (fun ((_, vardef', locset', _) as statetup) acc' ->
            if MyAccessPath.equal vardef vardef' && LocationSet.equal locset locset' then
              S.add statetup acc'
            else acc')
          statetups S.empty
      in
      if S.is_empty matches then acc else matches :: acc)
    ~init:[] vardef_locset_pairs


(** Return the first matching value for a key in a association list. *)
let rec assoc (alist : ('a * 'b) list) (key : 'a) ~equal : 'b =
  match alist with
  | [] ->
      raise (Failure "Could not find matching ones")
  | (key', value) :: t ->
      if equal key key' then value else assoc t key ~equal


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
          (* && (not @@ is_frontend_tmp_var_ap ap) *)
          && (not @@ is_returnv_ap ap)
          && (not @@ is_return_ap ap)
          && (not @@ is_param_ap ap)
          && (not @@ is_callv_ap ap))
        astate_set
    in
    let non_pvar_astates = S.filter (fun astate -> not @@ S.mem astate pvar_astates) astate_set in
    let partitions = partition_statetups_by_vardef pvar_astates in
    let partition_mapfunc ((ap, partition) : MyAccessPath.t * S.t) : T.t =
      (* sanity check *)
      let proc, vardef, locset, aliasset = List.hd_exn @@ S.elements partition in
      let other_threes_are_all_equal =
        S.fold
          (fun (proc', vardef', locset', _) acc ->
            Procname.equal proc proc' && MyAccessPath.equal vardef vardef'
            && LocationSet.equal locset locset' && acc)
          partition true
      in
      assert other_threes_are_all_equal ;
      let aliasset_combined =
        S.fold (fun statetup acc -> A.union acc @@ fourth_of statetup) partition A.empty
      in
      (proc, vardef, locset, aliasset_combined)
    in
    let processed_pvar_astates = S.of_list @@ List.( >>| ) partitions partition_mapfunc in
    S.union processed_pvar_astates non_pvar_astates
  in
  Hashtbl.iter (fun proc astate_set -> Hashtbl.replace table proc (one_pass_S astate_set)) table ;
  table


(* removing unimportant elements ==================== *)
(* ================================================== *)

let remove_unimportant_elems (table : (Procname.t, S.t) Hashtbl.t) : (Procname.t, S.t) Hashtbl.t =
  let filter_garbage_astate tup =
    let var, _ = second_of tup in
    (not @@ is_placeholder_vardef var)
    && (not @@ is_logical_var var)
    && (not @@ is_frontend_tmp_var var)
  in
  let filter_garbage_aliastup ap =
    let var = fst ap in
    (not @@ is_placeholder_vardef var)
    && (not @@ is_logical_var var)
    && (not @@ is_frontend_tmp_var var)
  in
  Hashtbl.iter
    (fun key summary ->
      let filtered_garbage_astates =
        S.filter filter_garbage_astate summary
        |> S.map (fun (proc, vardef, locset, aliasset) ->
               let filtered_aliastup = A.filter filter_garbage_aliastup aliasset in
               (proc, vardef, locset, filtered_aliastup))
      in
      Hashtbl.replace table key filtered_garbage_astates)
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
          String.equal returnv_meth_simple param_meth_simple)
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
          is_initializer procname ))
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

let consolidate_frontend_by_locset (table : (Procname.t, S.t) Hashtbl.t) :
    (Procname.t, S.t) Hashtbl.t =
  let one_pass_S (astate_set : S.t) : S.t =
    let pvar_astates =
      S.filter
        (fun astate ->
          let ap = second_of astate in
          (not @@ is_this_ap ap)
          && (not @@ is_placeholder_vardef (fst ap))
          && (not @@ is_frontend_tmp_var_ap ap)
          && (not @@ is_returnv_ap ap)
          && (not @@ is_return_ap ap)
          && (not @@ is_param_ap ap)
          && (not @@ is_callv_ap ap))
        astate_set
    and frontend_var_astates =
      S.filter
        (fun astate ->
          let ap = second_of astate in
          is_frontend_tmp_var_ap ap)
        astate_set
    in
    let locsets =
      List.stable_dedup @@ S.fold (fun astate acc -> third_of astate :: acc) astate_set []
    in
    let there_is_only_one_pvar_per_locset =
      List.fold
        ~f:(fun acc locset ->
          let there_is_only_one =
            Int.( > ) 2 @@ S.cardinal
            @@ S.filter (fun astate -> LocationSet.equal locset @@ third_of astate) pvar_astates
          in
          there_is_only_one && acc)
        ~init:true locsets
    in
    assert there_is_only_one_pvar_per_locset ;
    S.fold
      (fun frontend_astate acc ->
        let frontend_proc, _, frontend_locset, frontend_aliasset = frontend_astate in
        match
          List.filter ~f:(fun statetup -> S.mem statetup pvar_astates)
          @@ search_tuples_by_loc frontend_locset (S.elements acc)
        with
        | [] ->
            acc
        | [((pvar_proc, pvar_vardef, pvar_locset, pvar_aliasset) as pvar_astate)] ->
            if LocationSet.equal pvar_locset frontend_locset then
              let new_pvar_astate =
                (pvar_proc, pvar_vardef, pvar_locset, A.union frontend_aliasset pvar_aliasset)
              in
              S.strong_update acc pvar_astate new_pvar_astate
            else acc
        | lst ->
            F.kasprintf
              (fun msg -> raise @@ TooManyMatches msg)
              "consolidate_frontend_by_locset failed: %a@." pp_tuplelist lst)
      frontend_var_astates astate_set
  in
  (* one_pass_S end *)
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
      L.progress "summary: %a@." S.pp summary)
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
      Out_channel.output_string out_chan string_to_write)
    table ;
  Out_channel.close out_chan ;
  table


(* Main ============================================= *)
(* ================================================== *)

let main : (Procname.t, S.t) Hashtbl.t -> unit =
 fun table ->
  table
  |> summary_table_to_file_and_return "1_raw_astate_set.txt"
  |> consolidate_dup_pvars
  |> summary_table_to_file_and_return "2_consolidate_dup_pvars.txt"
  |> consolidate_frontend_by_locset
  |> summary_table_to_file_and_return "3_consolidate_by_locset.txt"
  |> delete_initializer_callv_param
  |> summary_table_to_file_and_return "4_delete_initizalizer_callv_param.txt"
  |> remove_unimportant_elems
  |> summary_table_to_file_and_return "5_remove_unimportant_elems.txt"
  |> return
