(** methods 중에서 단순 Getter와 Setter를 찾아낸다. *)

open! IStd
open DefLocAlias.TransferFunctions
open DefLocAliasSearches
open DefLocAliasLogicTests
open DefLocAliasDomain
open Yojson.Basic


module LocSet = DefLocAliasDomain.LocationSet
module S = DefLocAliasDomain.AbstractStateSetFinite
module A = DefLocAliasDomain.SetofAliases
module T = DefLocAliasDomain.AbstractState
module L = Logging
module F = Format


module Hashtbl = Caml.Hashtbl


type json = Yojson.Basic.t


type methods =
  | Getter of Procname.t
  | Setter of Procname.t
  | None


(** Procname.t에서 그 써머리로 가는 테이블. *)
let method_summary_table = Hashtbl.create 777


let get_summary (key:Procname.t) : S.t =
  try
    Hashtbl.find method_summary_table key
  with _ ->
    S.empty


(** 주어진 methname을 가진 메소드가 단순 getter인지를 판단한다.
    검출 방법: (this, [fieldName]) 와 return 각각의 aliasset이 동일한 logicalvar를 갖고 있는지를 확인. *)
let detect_getter (methname:Procname.t) : methods =
  let summary = get_summary methname in
  match S.cardinal summary with
  | 0 -> L.die InternalError "Methname %s does not exist" (Procname.to_string methname)
  | _ ->

    (* summary에서 this.fieldName이 aliasset에 들어있는 튜플 찾기 *)
    (* 우선 우리가 찾고자 하는 튜플에만 true flag를 세워 줌  *)
    let this_fieldname_tuples = S.fold (fun tup acc ->
        let aliasset = fourth_of tup in
        let is_this_fieldname = A.fold (fun aliastup acc ->
            acc || (Var.is_this @@ fst aliastup) && (not @@ List.is_empty @@ snd aliastup)) aliasset false in
        (tup, is_this_fieldname)::acc) summary [] in

    (* true flag와 결부된 튜플만 필터링 *)
    let this_fieldname_tuples' = List.filter ~f:(fun tup -> Bool.equal true @@ snd tup) this_fieldname_tuples in
    let this_fieldname_tuple = 
      match this_fieldname_tuples' with
      | [tuple] -> fst tuple
      | _       -> bottuple in  (* 나중에 false를 리턴하게 할 것 *)

    (* summary에서 return이 aliasset에 들어있는 튜플 찾기 *)
    let return_tuples = S.fold (fun tup acc ->
        let aliasset = fourth_of tup in
        let is_return = A.fold (fun aliastup acc ->
            acc || Var.is_return @@ fst aliastup) aliasset false in
        (tup, is_return)::acc) summary [] in

    (* true flag와 결부된 튜플만 필터링 *)
    let return_tuples' = List.filter ~f:(fun tup -> Bool.equal true @@ snd tup) return_tuples in
    let return_tuple =
      match return_tuples' with
      | [tuple] -> fst tuple
      | _       -> bottuple in  (* 나중에 false를 리턴하게 할 것 *)
    
    (* 해당 안 되면 일찍 빠지시고요 *)
    if T.equal this_fieldname_tuple bottuple || T.equal return_tuple bottuple then None else
    (* 두 튜플의 aliasset이 동일한 logical variable을 갖고 있는지를 확인하기 *)
    let this_fieldname_tuple_aliasset = fourth_of this_fieldname_tuple in
    let return_tuple_aliasset = fourth_of return_tuple in
    
    (* intersection이 있는지 파악: intersection이 있다면 그것은 동일한 logical variable이 있기 때문 *)
    match A.elements @@ A.inter this_fieldname_tuple_aliasset return_tuple_aliasset with
    | [] -> None
    | _ -> Getter methname


(** 주어진 methname을 가진 메소드가 단순 setter인지를 판단한다.
    검출 방법: (this, [fieldName])이 vardef로 들어 있는 튜플이 파라미터인 fieldName을 가지고 있고,
    그 line number는 fieldName이 정의된 line number보다 크거나 같다. *)
let detect_setter (methname:Procname.t) : methods =
  (* Phase 1: this.fieldName이 vardef로 들어 있는 튜플을 찾는다: 로직 재탕 *)
  (* 우선 우리가 찾고자 하는 튜플에만 true flag를 세워 줌  *)
  let summary = get_summary methname in
  let this_fieldname_tuples = S.fold (fun tup acc ->
      let aliasset = fourth_of tup in
      let is_this_fieldname = A.fold (fun aliastup acc ->
          acc || (Var.is_this @@ fst aliastup) && (not @@ List.is_empty @@ snd aliastup)) aliasset false in
      (tup, is_this_fieldname)::acc) summary [] in

  (* true flag와 결부된 튜플만 필터링 *)
  let this_fieldname_tuples' = List.filter ~f:(fun tup -> Bool.equal true @@ snd tup)
      this_fieldname_tuples in
  let this_fieldname_tuple = 
    match this_fieldname_tuples' with
    | [tuple] -> fst tuple
    | _       -> bottuple in  (* 나중에 false를 리턴하게 할 것 *)

  (* sanity check: 발견된 튜플의 aliasset에 logicalvar, this.fieldName이 아닌 다른 튜플이 *하나만* 있는지를 확인한다. *)
  let aliasset = fourth_of this_fieldname_tuple in
  let alias_tuples = A.elements aliasset in
  let sanity = List.fold_left ~f:(fun acc tup ->
      if (is_logical_var @@ fst tup) && (Var.is_this @@ fst tup)
      then acc
      else tup::acc) ~init:[] alias_tuples in
  let sanity_check = Int.equal 1 @@ List.length sanity in
  if not sanity_check then None else  (* 중간 sanity check 들어가실게요 *)

    (* Phase 2: *하나만* 있는 그 튜플 (파라미터)의 line number가 Phase 1에서 발견한 튜플의 line number 이전인지 확인한다. *)
    let ap = List.nth_exn sanity 0 in
    let target_tuple = search_target_tuple_by_vardef_ap ap methname summary in
    let ap_linenum = List.nth_exn (LocSet.elements @@ third_of target_tuple) 0 in
    let target_linenum = List.nth_exn (LocSet.elements @@ third_of target_tuple) 0 in
    if ap_linenum.line >= target_linenum.line then Setter methname else None


(** Procname들 중에서 Getter만을 모은다. *)
let collect_getter (meths:Procname.t list) : methods list =
  List.map ~f:detect_getter meths
  |> List.filter ~f:(fun meth ->
      match meth with
      | Getter _ -> true
      | _ -> false)


(** Procname들 중에서 Setter만을 모은다. *)
let collect_setter (meths:Procname.t list) : methods list =
  List.map ~f:detect_setter meths
  |> List.filter ~f:(fun meth ->
      match meth with
      | Setter _ -> true
      | _ -> false)


(** Getter 또는 Setter로 label된 method 한 개를 json 형식으로 찍어낸다. key: method name, attr: "getter" 혹은 "setter". *)
let json_repr (labelled_method:methods) : json =
    match labelled_method with
    | Getter name ->
        `Assoc [(Procname.to_string name, `String "getter")]
    | Setter name -> 
        `Assoc [((Procname.to_string name, `String "setter"))]
    | None -> L.die InternalError "trying to write a non-getter/setter method" 


let batch_json_repr (labelled_methods:methods list) : json list =
  List.map ~f:json_repr labelled_methods


let write_json_to_file (json_list:json list) : unit =
  let out_channel = Out_channel.create "GetterSetter.json" in
  let iterfunc = fun json ->
    to_channel out_channel json in
  List.iter ~f:iterfunc json_list;
  Out_channel.flush out_channel;
  Out_channel.close out_channel
 

let main () : unit =
  load_summary_from_disk_to method_summary_table;
  let meths = Hashtbl.fold (fun k _ acc -> k::acc) method_summary_table [] in
  let getter_methods = collect_getter meths in
  let setter_methods = collect_setter meths in
  let labelled_methods = getter_methods @ setter_methods in
  let json_list = batch_json_repr labelled_methods in
  write_json_to_file json_list
