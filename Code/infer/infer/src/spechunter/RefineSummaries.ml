open! IStd
open DefLocAliasSearches
open DefLocAliasPredicates
open DefLocAliasDomain
module Hashtbl = Caml.Hashtbl
module P = DefLocAliasDomain.AbstractPair
module S = DefLocAliasDomain.AbstractStateSetFinite
module A = DefLocAliasDomain.SetofAliases
module T = DefLocAliasDomain.AbstractState
module L = Logging
module F = Format

exception TODO

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
  let partition_statetups_by_locset (statetups : S.t) : (S.t * LocationSet.t) list =
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
        (matches, locset) :: acc)
      ~init:[] locsets
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
    ~f:(fun acc (partition, locset) ->
      let location = get_singleton locset in
      let statetups_holding_param =
        search_target_tuples_holding_param location.col (S.elements acc)
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
          (fun statetup ->
            let aliasset = fourth_of statetup in
            let new_aliasset = A.union aliasset locset_aliasset_combined in
            raise TODO)
          statetups_holding_param
      in
      let acc_updated =
        (* strong-update *)
        let acc_rmvd =
          S.filter (fun statetup -> not @@ S.mem statetup statetups_holding_param) acc
        in
        S.union acc_rmvd statetups_holding_param
      in
      acc_updated)
    ~init:astate_set partitions


let consolidate_irvar_table (table : (Methname.t, S.t) Hashtbl.t) : (Methname.t, S.t) Hashtbl.t =
  Hashtbl.iter
    (fun proc summary ->
      let consolidated = consolidate_irvars summary in
      Hashtbl.remove table proc ;
      Hashtbl.add table proc consolidated)
    table ;
  table


let return (table : (Methname.t, S.t) Hashtbl.t) : unit = Hashtbl.iter (fun _ _ -> ()) table

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


(* Refining functions =============================== *)
(* ================================================== *)

let main : (Methname.t, S.t) Hashtbl.t -> unit =
  consolidate_irvar_table >> remove_unimportant_elems >> return
