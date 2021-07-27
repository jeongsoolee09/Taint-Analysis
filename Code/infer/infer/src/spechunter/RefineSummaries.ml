open! IStd
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

exception TODO

let partition_statetups_by_locset (statetups : S.t) : (LocationSet.t * S.t) list =
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
      (locset, matches) :: acc)
    ~init:[] locsets


(** Return the first matching value for a key in a association list. *)
let rec assoc (alist : ('a * 'b) list) (key : 'a) ~equal : 'b =
  match alist with
  | [] ->
      L.die InternalError "Could not found matching ones"
  | (key', value) :: t ->
      if equal key key' then value else assoc t key ~equal


(* Consolidating $irvars ============================ *)
(* ================================================== *)

let consolidate_irvars (astate_set : S.t) : S.t =
  let irvars =
    S.fold
      (fun astate acc ->
        let ap = second_of astate in
        if is_irvar_ap ap then S.add astate acc else acc)
      astate_set S.empty
  in
  let get_singleton (locset : LocationSet.t) : Location.t =
    match LocationSet.elements locset with
    | [loc] ->
        loc
    | _ ->
        L.die InternalError "This is not a singleton location set!: %a@." LocationSet.pp locset
  in
  let partitions = partition_statetups_by_locset irvars in
  List.fold
    ~f:(fun acc (locset, partition) ->
      let location = get_singleton locset in
      let statetups_holding_param =
        search_target_tuples_holding_param location.line (S.elements acc)
        |> List.filter ~f:(fun statetup -> not @@ LocationSet.equal locset @@ third_of statetup)
        |> S.of_list
      in
      let locset_aliasset_combined =
        S.fold
          (fun statetup acc' ->
            let aliasset = fourth_of statetup in
            A.union acc' aliasset)
          partition A.empty
      in
      let updated_tuples =
        S.map
          (fun (proc, vardef, loc, aliasset) ->
            let new_aliasset = A.union aliasset locset_aliasset_combined in
            (proc, vardef, loc, new_aliasset))
          statetups_holding_param
      in
      let acc_updated =
        (* strong-update *)
        let acc_rmvd =
          S.filter (fun statetup -> not @@ S.mem statetup statetups_holding_param) acc
        in
        S.union acc_rmvd updated_tuples
      in
      acc_updated)
    ~init:astate_set partitions


let consolidate_irvar_table (table : (Methname.t, S.t) Hashtbl.t) : (Methname.t, S.t) Hashtbl.t =
  Hashtbl.iter
    (fun proc summary ->
      if String.equal (Procname.to_string proc) "void RelationalDataAccessApplication.run()" then (
        let consolidated = consolidate_irvars summary in
        Hashtbl.remove table proc ;
        Hashtbl.add table proc consolidated ))
    table ;
  table


(* removing unimportant elements ==================== *)
(* ================================================== *)

let remove_unimportant_elems (table : (Methname.t, S.t) Hashtbl.t) : (Methname.t, S.t) Hashtbl.t =
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


let delete_compensating_param_returnv (table : (Methname.t, S.t) Hashtbl.t) :
    (Methname.t, S.t) Hashtbl.t =
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


(* Remove initializer calls *)
(* ================================================== *)

let delete_initializer_callv_param (table : (Methname.t, S.t) Hashtbl.t) :
    (Methname.t, S.t) Hashtbl.t =
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

let consolidate_frontend_by_locset (table : (Methname.t, S.t) Hashtbl.t) :
    (Methname.t, S.t) Hashtbl.t =
  let get_singleton (astate_set : S.t) : T.t =
    match S.elements astate_set with
    | [statetup] ->
        statetup
    | _ ->
        L.die InternalError "This is not a singleton location set!: %a@." S.pp astate_set
  in
  let one_pass_S (astate_set : S.t) : S.t =
    let real_var_astates =
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
    in
    let frontend_var_astates =
      S.filter
        (fun astate ->
          let ap = second_of astate in
          is_frontend_tmp_var_ap ap)
        astate_set
    in
    let real_var_astates_partitioned = partition_statetups_by_locset real_var_astates in
    let frontend_var_astates_partitioned = partition_statetups_by_locset frontend_var_astates in
    let locsets : LocationSet.t list =
      List.stable_dedup
      @@ S.fold
           (fun astate acc ->
             let locset = third_of astate in
             locset :: acc)
           astate_set []
    in
    (* We got the locsets, so pair the real_var astates and frontend_var_astates by the locset *)
    let realvar_frontendvar_pairedup : (S.t * S.t) list =
      List.map
        ~f:(fun locset ->
          let matching_realvar_partition =
            assoc real_var_astates_partitioned locset ~equal:LocationSet.equal
          in
          let matching_frontendvar_partition =
            assoc frontend_var_astates_partitioned locset ~equal:LocationSet.equal
          in
          (* sanity check *)
          assert (Int.equal (S.cardinal matching_realvar_partition) 1) ;
          (matching_realvar_partition, matching_frontendvar_partition))
        locsets
    in
    (* Now, combine them together! *)
    List.fold
      ~f:(fun acc (realvar_set, frontendvar_set) ->
        let real_proc, real_vardef, real_locset, real_aliasset = get_singleton realvar_set in
        let frontendvar_sets_aliasset =
          S.fold
            (fun statetup acc ->
              let aliasset = fourth_of statetup in
              A.union acc aliasset)
            frontendvar_set A.empty
        in
        let combined_aliasset = A.fold A.add frontendvar_sets_aliasset real_aliasset in
        let newtuple = (real_proc, real_vardef, real_locset, combined_aliasset) in
        S.add newtuple acc)
      ~init:S.empty realvar_frontendvar_pairedup
    (* one_pass_S end *)
  in
  Hashtbl.iter (fun proc astate_set -> Hashtbl.replace table proc (one_pass_S astate_set)) table ;
  table


(* Return =========================================== *)
(* ================================================== *)

let return (table : (Methname.t, S.t) Hashtbl.t) : unit = Hashtbl.iter (fun _ _ -> ()) table

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


(* Main ============================================= *)
(* ================================================== *)

let main : (Methname.t, S.t) Hashtbl.t -> unit = fun table -> raise TODO
