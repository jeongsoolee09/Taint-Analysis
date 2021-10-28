open Yojson.Basic
open GraphRepr

exception TODO

type json = Yojson.Basic.t

(* TEMP DON'T SHIP WITH THIS CODE *)
let x = Deserializer.deserialize_json "Chain.json"

module ChainRefiners = struct
  let delete_inner_deads (chain_slices : ChainSlice.t list) : ChainSlice.t list =
    let all_but_last = List.slice chain_slices 0 (List.length chain_slices - 1) in
    let dead_filtered =
      List.filter ~f:(fun chain_slice -> not @@ ChainSlice.is_dead chain_slice) all_but_last
    in
    dead_filtered @ [List.last_exn chain_slices]
end
