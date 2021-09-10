open! IStd

open DefLocAliasDomain

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


let partition_callvs_by_procname (callvs: MyAccessPath.t) : MyAccessPath.t list list =
  raise TODO
