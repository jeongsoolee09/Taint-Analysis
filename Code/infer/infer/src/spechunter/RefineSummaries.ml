open DefLocAliasSearches
open DefLocAliasPredicates
open DefLocAliasDomain
open DefLocAliasPP
open Partitioners
open SpecHunterUtils
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

exception ConsolidateByLocsetFailed of string

let ( >>| ) = List.( >>| )

let ( >>= ) = List.( >>= )

(** Return the first matching value for a key in a association list. *)
let rec assoc (alist : ('a * 'b) list) (key : 'a) ~equal : 'b =
  match alist with
  | [] ->
      raise (Failure "Could not find matching ones")
  | (key', value) :: t ->
      if equal key key' then value else assoc t key ~equal


(* Utils ============================================ *)
(* ================================================== *)

let callv_and_returnv_matches ~(callv : MyAccessPath.t) ~(returnv : MyAccessPath.t) =
  let callv_counter = extract_counter_from_callv callv
  and callv_linum = extract_linum_from_callv callv in
  let returnv_counters = extract_counter_from_returnv returnv
  and returnv_linum = extract_linum_from_returnv returnv in
  List.mem returnv_counters callv_counter ~equal:Int.( = ) && Int.( = ) returnv_linum callv_linum


let extract_java_procname (methname : Procname.t) : Procname.Java.t =
  match methname with
  | Java procname ->
      procname
  | _ ->
      L.die InternalError
        "extract_java_procname failed, methname: %a (maybe you ran this analysis on a non-Java \
         project?)@."
        Procname.pp methname


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


(* Subsitute all __new returnvs with <init> returnvs  *)
(* ================================================== *)

let substitute_frontend_new_returnv_with_init_returnv (table : (Procname.t, S.t) Hashtbl.t) :
    (Procname.t, S.t) Hashtbl.t =
  let one_pass_S (astate_set : S.t) : S.t =
    if is_lambda @@ first_of @@ List.hd_exn @@ S.elements astate_set then astate_set
    else
      (* L.progress "astate_Set: %a@." S.pp astate_set ; *)
      let is_matching_new_returnv new_returnv init_returnv =
        (* L.progress "new_returnv: %a " MyAccessPath.pp new_returnv ; *)
        (* L.progress "returnv: %a@." MyAccessPath.pp init_returnv ; *)
        is_new_returnv new_returnv
        && Int.( = )
             (extract_linum_from_returnv new_returnv)
             (extract_linum_from_returnv init_returnv)
        &&
        let new_returnv_classname = extract_classname_from_new_returnv new_returnv
        and init_returnv_classname = extract_classname_from_init_returnv init_returnv in
        String.equal new_returnv_classname init_returnv_classname
      in
      let new_returnv_astates =
        S.filter
          (fun astate ->
            let aliasset = fourth_of astate in
            A.exists is_new_returnv aliasset )
          astate_set
      in
      (* sanity check on the astates holding <init> returnvs *)
      let astates_holding_init_returnvs =
        S.filter
          (fun astate ->
            let aliasset = fourth_of astate in
            A.exists is_init_returnv aliasset )
          astate_set
      in
      S.iter
        (fun astate -> assert (is_placeholder_vardef_ap (second_of astate)))
        astates_holding_init_returnvs ;
      (* now, update the new_returnv_astates *)
      let new_returnv_astates_updated =
        S.map
          (fun (proc, vardef, loc, aliasset) ->
            let new_returnv = List.find_exn ~f:is_new_returnv (A.elements aliasset) in
            let matching_init_returnv_astates =
              List.filter
                ~f:(fun astate_holding_returnv ->
                  let init_returnvs =
                    List.filter ~f:is_init_returnv (A.elements @@ fourth_of astate_holding_returnv)
                  in
                  List.exists
                    ~f:(fun init_returnv -> is_matching_new_returnv new_returnv init_returnv)
                    init_returnvs )
                (S.elements astates_holding_init_returnvs)
            in
            let matching_init_returnv_astate_returnvs =
              List.filter
                ~f:(fun ap -> is_init_returnv ap && is_matching_new_returnv new_returnv ap)
                (matching_init_returnv_astates >>| (fourth_of >> A.elements) |> List.concat)
            in
            ( proc
            , vardef
            , loc
            , A.union aliasset
                (A.filter
                   (fun ap -> (not @@ is_callv_ap ap) && (not @@ is_returnv_ap ap))
                   ( matching_init_returnv_astates >>| (fourth_of >> A.elements) |> List.concat
                   |> A.of_list ) )
              |> A.union (A.of_list matching_init_returnv_astate_returnvs)
              |> A.filter (not << is_new_returnv)
              |> A.remove new_returnv ) )
          new_returnv_astates
      in
      S.diff astate_set new_returnv_astates |> S.union new_returnv_astates_updated
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


(* merge cast's returnv with return ================= *)
(* ================================================== *)

let merge_cast_returnv_with_return (table : (Procname.t, S.t) Hashtbl.t) :
    (Procname.t, S.t) Hashtbl.t =
  let is_problematic (astate_set : S.t) : bool =
    S.exists
      (fun astate ->
        let aliasset = fourth_of astate in
        let there_is_return_in_aliasset = A.exists (fun ap -> is_return_ap ap) aliasset in
        let there_is_cast_returnv =
          A.exists (fun ap -> is_returnv_ap ap && is_cast (extract_callee_from ap)) aliasset
        in
        there_is_return_in_aliasset && there_is_cast_returnv )
      astate_set
  in
  let is_cast_returnv ap = is_returnv_ap ap && is_cast (extract_callee_from ap) in
  let is_cast_callv ap = is_callv_ap ap && is_cast (extract_callee_from ap) in
  let one_pass_S (astate_set : S.t) : S.t =
    if is_problematic astate_set then
      let astates_holding_cast_returnv_and_return =
        S.filter
          (fun astate ->
            A.exists is_cast_returnv (fourth_of astate) && A.exists is_return_ap (fourth_of astate)
            )
          astate_set
      in
      let astates_holding_cast_callv =
        S.filter (fun astate -> A.exists is_cast_callv (fourth_of astate)) astate_set
      in
      let astates_holding_cast_returnv_and_return_updated =
        S.map
          (fun astate ->
            let cast_returnv =
              List.find_exn
                ~f:(fun ap -> is_returnv_ap ap && is_cast (extract_callee_from ap))
                (A.elements (fourth_of astate))
            in
            let cast_returnv_counter = extract_counter_from_returnv cast_returnv
            and cast_returnv_linum = extract_linum_from_returnv cast_returnv in
            let ( (callv_proc, callv_vardef, callv_loc, callv_aliasset) as
                astate_holding_matching_cast_callv ) =
              List.find_exn
                ~f:(fun other_astate ->
                  let other_aliasset = fourth_of other_astate in
                  A.exists is_cast_callv other_aliasset
                  &&
                  let cast_callv = List.find_exn ~f:is_cast_callv (A.elements other_aliasset) in
                  let cast_callv_counter = extract_counter_from_callv cast_callv
                  and cast_callv_linum = extract_linum_from_callv cast_callv in
                  List.mem cast_returnv_counter cast_callv_counter ~equal:Int.( = )
                  && Int.( = ) cast_returnv_linum cast_callv_linum )
                (S.elements astates_holding_cast_callv)
            in
            let callv_aliasset_updated =
              A.union callv_aliasset (fourth_of astate)
              |> A.filter (not << is_cast_callv)
              |> A.filter (not << is_cast_returnv)
            in
            (callv_proc, callv_vardef, callv_loc, callv_aliasset_updated) )
          astates_holding_cast_returnv_and_return
      in
      astate_set
      |> (fun astate_set -> S.diff astate_set astates_holding_cast_callv)
      |> S.union astates_holding_cast_returnv_and_return_updated
    else astate_set
  in
  Hashtbl.iter (fun proc astate_set -> Hashtbl.replace table proc (one_pass_S astate_set)) table ;
  table


(* handling void calls ============================== *)
(* ================================================== *)

let move_void_callee_returnv_and_remove_ph (table : (Procname.t, S.t) Hashtbl.t) :
    (Procname.t, S.t) Hashtbl.t =
  let is_void_method_returnv (ap : MyAccessPath.t) : bool =
    is_returnv_ap ap && return_type_is_void (extract_callee_from ap)
  and is_void_method_callv (ap : MyAccessPath.t) : bool =
    is_callv_ap ap && return_type_is_void (extract_callee_from ap)
  in
  let one_pass_S (astate_set : S.t) : S.t =
    let ph_tuples_with_void_returnvs =
      S.filter
        (fun astate ->
          is_placeholder_vardef_ap (second_of astate)
          && A.exists is_void_method_returnv (fourth_of astate) )
        astate_set
    in
    let void_returnvs =
      A.elements
      @@ ( S.fold
             (fun astate acc ->
               let void_returnvs = A.filter is_void_method_returnv (fourth_of astate) in
               A.union acc void_returnvs )
             ph_tuples_with_void_returnvs A.empty
         |> A.filter (fun ap ->
                let java_proc = extract_java_procname (extract_callee_from ap) in
                not @@ Procname.Java.is_static java_proc ) )
    in
    let astates_holding_corresponding_callvs =
      try
        List.map
          ~f:(fun returnv ->
            find_witness_exn (S.elements astate_set) ~pred:(fun astate ->
                A.exists
                  (fun ap -> is_callv_ap ap && callv_and_returnv_matches ~callv:ap ~returnv)
                  (fourth_of astate) ) )
          void_returnvs
      with NoWitness -> []
    in
    let astates_holding_corresponding_callvs_updated =
      try
        List.map
          ~f:(fun (proc, vardef, loc, aliasset) ->
            let void_callv = find_witness_exn ~pred:is_void_method_callv (A.elements aliasset) in
            let corresponding_returnv =
              find_witness_exn
                ~pred:(fun void_returnv ->
                  callv_and_returnv_matches ~callv:void_callv ~returnv:void_returnv )
                void_returnvs
            in
            (proc, vardef, loc, A.add corresponding_returnv aliasset) )
          astates_holding_corresponding_callvs
      with _ -> []
    in
    astate_set
    |> (fun astate_set -> S.diff astate_set ph_tuples_with_void_returnvs)
    |> (fun astate_set -> S.diff astate_set (S.of_list astates_holding_corresponding_callvs))
    |> S.union (S.of_list astates_holding_corresponding_callvs_updated)
  in
  Hashtbl.iter (fun proc astate_set -> Hashtbl.replace table proc (one_pass_S astate_set)) table ;
  table


let merge_cast_returnv_aliasset_with_callv_ones (table : (Procname.t, S.t) Hashtbl.t) :
    (Procname.t, S.t) Hashtbl.t =
  let is_cast_callv ap = is_callv_ap ap && is_cast (extract_callee_from ap) in
  let is_cast_returnv ap = is_returnv_ap ap && is_cast (extract_callee_from ap) in
  let one_pass_S (astate_set : S.t) : S.t =
    let ph_tuple_with_cast_returnv =
      S.filter
        (fun (_, vardef, _, aliasset) ->
          is_placeholder_vardef_ap vardef && A.exists is_cast_returnv aliasset )
        astate_set
    in
    S.fold
      (fun ph_astate acc ->
        let cast_returnv = List.find_exn ~f:is_cast_returnv (A.elements (fourth_of ph_astate)) in
        let matching_tuple_opt =
          List.find
            ~f:(fun astate ->
              A.exists
                (fun ap ->
                  is_cast_callv ap && callv_and_returnv_matches ~callv:ap ~returnv:cast_returnv )
                (fourth_of astate) )
            (S.elements acc)
        in
        match matching_tuple_opt with
        | Some ((matching_proc, matching_vardef, matching_loc, matching_aliasset) as matching_tuple)
          ->
            let matching_tuple_updated =
              ( matching_proc
              , matching_vardef
              , matching_loc
              , A.union (fourth_of ph_astate) matching_aliasset
                |> A.filter (fun ap ->
                       not
                         ( MyAccessPath.equal cast_returnv ap
                         || is_cast_callv ap
                            && callv_and_returnv_matches ~callv:ap ~returnv:cast_returnv
                         || (is_param_ap ap && (is_cast @@ extract_callee_from ap)) ) ) )
            in
            acc |> S.remove ph_astate |> S.remove matching_tuple |> S.add matching_tuple_updated
        | None ->
            acc )
      ph_tuple_with_cast_returnv astate_set
  in
  Hashtbl.iter (fun proc astate_set -> Hashtbl.replace table proc (one_pass_S astate_set)) table ;
  table


let promote_ph_to_pvar_with_get_array_length_returnv (table : (Procname.t, S.t) Hashtbl.t) :
    (Procname.t, S.t) Hashtbl.t =
  let has_get_array_length_returnv (aliasset : A.t) : bool =
    A.exists
      (fun (var, _) ->
        String.is_substring (F.asprintf "%a" Var.pp var) ~substring:"__get_array_length"
        && is_returnv var )
      aliasset
  in
  let one_pass_S (astate_set : S.t) : S.t =
    let counter = ref 1 in
    S.fold
      (fun ((proc, vardef, locset, aliasset) as astate) acc ->
        if has_get_array_length_returnv aliasset && is_placeholder_vardef (fst vardef) then
          S.remove astate acc
          |> S.add
               ( proc
               , (Var.of_pvar @@ Pvar.mk_tmp (F.sprintf "promoted%d" !counter) proc, [])
               , locset
               , aliasset )
        else acc )
      astate_set astate_set
  in
  Hashtbl.iter (fun proc astate_set -> Hashtbl.replace table proc (one_pass_S astate_set)) table ;
  table


let remove_too_many_callv_returnv_setters (table : (Procname.t, S.t) Hashtbl.t) :
    (Procname.t, S.t) Hashtbl.t =
  let is_setter (procname : Procname.t) : bool =
    return_type_is_void procname && String.is_prefix (Procname.get_method procname) ~prefix:"set"
  in
  let all_callv_in_astate_set (astate_set : S.t) : MyAccessPath.t list =
    A.elements
    @@ S.fold
         (fun astate big_acc ->
           let this_astate_void_callvs =
             A.filter
               (fun ap -> is_callv_ap ap && is_setter (extract_callee_from ap))
               (fourth_of astate)
           in
           A.union this_astate_void_callvs big_acc )
         astate_set A.empty
  in
  let more_than_one_callv_per_void_method_in_astate_set (astate_set : S.t) =
    let all_void_callvs = all_callv_in_astate_set astate_set in
    let all_void_callvs_partitioned = partition_callvs_by_procname all_void_callvs in
    List.for_all all_void_callvs_partitioned ~f:(fun partition -> List.length partition >= 2)
  in
  let leave_only_earliest_callv (callvs : MyAccessPath.t list) : MyAccessPath.t =
    Option.value ~default:MyAccessPath.dummy
    @@ List.min_elt callvs ~compare:(fun callv1 callv2 ->
           Int.compare (extract_counter_from_callv callv1) (extract_counter_from_callv callv2) )
  in
  let one_pass_S (astate_set : S.t) : S.t =
    if
      String.equal
        (Procname.to_string @@ first_of @@ List.hd_exn @@ S.elements astate_set)
        "ImportStatus ExcelImporter.importFile(File)"
    then
      Out_channel.with_file "excel.bin" ~f:(fun out_chan ->
          Marshal.to_channel out_chan astate_set [] ) ;
    L.progress "astate_set : %a@." S.pp astate_set ;
    Out_channel.flush stdout ;
    if
      List.length (all_callv_in_astate_set astate_set) > 2
      && more_than_one_callv_per_void_method_in_astate_set astate_set
    then (
      let all_callvs_for_void_methods = all_callv_in_astate_set astate_set in
      let all_callvs_partitioned_by_callee =
        partition_callvs_by_procname all_callvs_for_void_methods
      in
      let only_earliest_callvs : MyAccessPath.t list =
        all_callvs_partitioned_by_callee >>| leave_only_earliest_callv
      in
      L.progress "only_earliest_callvs: %a@." pp_ap_list only_earliest_callvs ;
      S.fold
        (fun ((proc, vardef, locset, aliasset) as astate) acc ->
          let aliasset_dieted =
            A.filter
              (fun ap ->
                match ap with
                | callv when is_callv_ap callv ->
                    (* use only_earliest_callvs *)
                    List.mem only_earliest_callvs callv ~equal:MyAccessPath.equal
                | returnv when is_returnv_ap returnv ->
                    (* use only_earliest_callvs *)
                    List.exists all_callvs_for_void_methods ~f:(fun callv ->
                        callv_and_returnv_matches ~callv ~returnv
                        && List.mem only_earliest_callvs callv ~equal:MyAccessPath.equal )
                | _ ->
                    true )
              aliasset
          in
          S.remove astate acc |> S.add (proc, vardef, locset, aliasset_dieted) )
        astate_set astate_set )
    else astate_set
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
    let carpro = returnvs >>= fun returnv -> params >>= fun param -> List.return (returnv, param) in
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
  |> substitute_frontend_new_returnv_with_init_returnv
  |> summary_table_to_file_and_return "5_substitute_frontend_new_returnv_with_init_returnv.txt"
  (* |> merge_cast_returnv_with_return *)
  (* |> summary_table_to_file_and_return "6_merge_cast_returnv_with_return.txt" *)
  |> move_void_callee_returnv_and_remove_ph
  |> summary_table_to_file_and_return "7_move_void_callee_returnv_and_remove_ph.txt"
  (* |> merge_cast_returnv_aliasset_with_callv_ones *)
  (* |> summary_table_to_file_and_return "8_merge_cast_returnv_aliasset_with_callv_ones.txt" *)
  |> promote_ph_to_pvar_with_get_array_length_returnv
  |> summary_table_to_file_and_return "9_promote_ph_to_pvar_with_get_array_length_returnv.txt"
  |> remove_too_many_callv_returnv_setters
  |> summary_table_to_file_and_return "10_remove_too_many_callv_returnv_setters.txt"
  |> remove_unimportant_elems
  |> summary_table_to_file_and_return "11_remove_unimportant_elems.txt"
  |> remove_java_constants
  |> summary_table_to_file_and_return "12_remove_java_constants.txt"
  |> return
