open! IStd
open DefLocAliasDomain
open DefLocAliasSearches
module S = DefLocAliasDomain.AbstractStateSetFinite
module A = DefLocAliasDomain.SetofAliases
module T = DefLocAliasDomain.AbstractState

exception TODO

let partition_statetups_by_procname (statetups : S.t) : S.t list =
  let procnames =
    List.stable_dedup
    @@ S.fold
         (fun astate acc ->
           let procname = first_of astate in
           procname :: acc )
         statetups []
  in
  List.fold
    ~f:(fun acc procname ->
      let matches =
        S.fold
          (fun statetup acc' ->
            if Procname.equal procname (first_of statetup) then S.add statetup acc' else acc' )
          statetups S.empty
      in
      matches :: acc )
    ~init:[] procnames


let partition_statetups_by_vardef (statetups : S.t) : S.t list =
  let vardefs =
    List.stable_dedup
    @@ S.fold
         (fun astate acc ->
           let vardef = second_of astate in
           vardef :: acc )
         statetups []
  in
  List.fold
    ~f:(fun acc vardef ->
      let matches =
        S.fold
          (fun statetup acc' ->
            if MyAccessPath.equal vardef (second_of statetup) then S.add statetup acc' else acc' )
          statetups S.empty
      in
      matches :: acc )
    ~init:[] vardefs


let partition_statetups_by_locset (statetups : S.t) : S.t list =
  let locsets : LocationSet.t list =
    List.stable_dedup
    @@ S.fold
         (fun astate acc ->
           let locset = third_of astate in
           locset :: acc )
         statetups []
  in
  List.fold
    ~f:(fun acc locset ->
      let matches =
        S.fold
          (fun statetup acc' ->
            if LocationSet.equal locset (third_of statetup) then S.add statetup acc' else acc' )
          statetups S.empty
      in
      matches :: acc )
    ~init:[] locsets


let partition_statetups_by_aliasset (statetups : S.t) : S.t list =
  let locsets =
    List.stable_dedup
    @@ S.fold
         (fun astate acc ->
           let aliasset = fourth_of astate in
           aliasset :: acc )
         statetups []
  in
  List.fold
    ~f:(fun acc locset ->
      let matches =
        S.fold
          (fun statetup acc' ->
            if A.equal locset (fourth_of statetup) then S.add statetup acc' else acc' )
          statetups S.empty
      in
      matches :: acc )
    ~init:[] locsets


let partition_statetups_by_vardef_and_locset (statetups : S.t) : S.t list =
  let vardefs =
    List.stable_dedup
    @@ S.fold
         (fun astate acc ->
           let vardef = second_of astate in
           vardef :: acc )
         statetups []
  in
  let locsets : LocationSet.t list =
    List.stable_dedup
    @@ S.fold
         (fun astate acc ->
           let locset = third_of astate in
           locset :: acc )
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
            else acc' )
          statetups S.empty
      in
      if S.is_empty matches then acc else matches :: acc )
    ~init:[] vardef_locset_pairs


let partition_aps_by_procname (aps : MyAccessPath.t list) : MyAccessPath.t list list =
  let open List in
  let callees = aps >>| get_declaring_function_ap_exn |> List.stable_dedup in
  let mapfunc proc =
    List.fold
      ~f:(fun acc ap ->
        if Procname.equal (get_declaring_function_ap_exn ap) proc then ap :: acc else acc )
      aps ~init:[]
  in
  callees >>| mapfunc


let partition_callvs_by_procname_and_location (callvs : MyAccessPath.t list) :
    MyAccessPath.t list list =
  let open List in
  let callees =
    callvs
    >>| (fun callv -> (get_declaring_function_ap_exn callv, extract_linum_from_callv callv))
    |> List.stable_dedup
  in
  let mapfunc (proc, linum) =
    List.fold
      ~f:(fun acc callv ->
        if
          Procname.equal (get_declaring_function_ap_exn callv) proc
          && Int.equal (extract_linum_from_callv callv) linum
        then callv :: acc
        else acc )
      callvs ~init:[]
  in
  callees >>| mapfunc


let partition_statetups_modulo_123 (statetups : S.t) : S.t list =
  let procnames : Procname.t list =
    List.stable_dedup
    @@ S.fold
         (fun astate acc ->
           let vardef = first_of astate in
           vardef :: acc )
         statetups []
  in
  let vardefs : MyAccessPath.t list =
    List.stable_dedup
    @@ S.fold
         (fun astate acc ->
           let vardef = second_of astate in
           vardef :: acc )
         statetups []
  in
  let locsets : LocationSet.t list =
    List.stable_dedup
    @@ S.fold
         (fun astate acc ->
           let locset = third_of astate in
           locset :: acc )
         statetups []
  in
  let triples =
    let open List in
    procnames
    >>= fun procname ->
    vardefs >>= fun vardef -> locsets >>= fun locset -> return (procname, vardef, locset)
  in
  List.fold
    ~f:(fun acc (procname, vardef, locset) ->
      let matches =
        S.fold
          (fun ((procname', vardef', locset', _) as statetup) acc' ->
            if
              Procname.equal procname procname' && MyAccessPath.equal vardef vardef'
              && LocationSet.equal locset locset'
            then S.add statetup acc'
            else acc' )
          statetups S.empty
      in
      if S.is_empty matches then acc else matches :: acc )
    ~init:[] triples
