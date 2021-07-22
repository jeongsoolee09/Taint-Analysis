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

(* Summary Table ==================================== *)
(* ================================================== *)

let summary_table =
  let new_table = Hashtbl.create 777 in
  SummaryLoader.load_summary_from_disk_to new_table ;
  new_table


let get_summary (key : Procname.t) : S.t = try Hashtbl.find summary_table key with _ -> S.empty

let pp_summary_table fmt hashtbl : unit =
  Hashtbl.iter (fun k v -> F.fprintf fmt "%a -> %a\n" Procname.pp k S.pp v) hashtbl


let extract_linum_from_param (ap : MyAccessPath.t) : int =
  match fst ap with
  | LogicalVar _ ->
      L.die InternalError "extract_linum_from_param failed: ap: %a@." MyAccessPath.pp ap
  | ProgramVar pv -> (
    match is_param_ap ap with
    | true ->
        Pvar.to_string pv |> String.split ~on:'_'
        |> fun str_list -> List.nth_exn str_list 2 |> int_of_string
    | false ->
        L.die InternalError "extract_linum_from_param failed: ap: %a@." MyAccessPath.pp ap )


let consolidate_irvars (astate_set : S.t) : S.t =
  (* 1. irvar들을 모두 긁어모아 리스트 (irvars)에 담아둔다. *)
  let irvars =
    S.fold
      (fun astate acc ->
        let ap = second_of astate in
        if is_irvar_ap ap then S.add astate acc else acc)
      astate_set S.empty
  in
  (* 2. irvar들의 locationset에 따라 irvars를 파티션한다. *)
  (* 하나의 S.t가 하나의 파티션 *)
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
      in
      raise TODO)
    ~init:astate_set partitions
