open Yojson.Basic

exception TODO

type json = Yojson.Basic.t

let ( >> ) g f x = f (g x)

(* TEMP DON'T SHIP WITH THIS CODE *)
let x = Deserializer.deserialize_json "Chain.json"

module JsonSliceManager = struct
  let divide_raw_chains_by_ap : json -> json list = Util.to_list

  let divide_ap_chain_by_status : json -> json list = Util.member "chain" >> Util.to_list

  (* This is why I love Yojson!! *)
end

module StatusPredicates = struct
  (** check if a association is present in an *unwrapped* chain. *)
  let status_is_member statusname unwrapped_chain =
    List.mem
      ~equal:(fun (key1, jsonval1) (key2, jsonval2) ->
        String.equal key1 key2 && Yojson.Basic.equal jsonval1 jsonval2 )
      unwrapped_chain
      ("status", `String statusname)


  let is_define = status_is_member "Define"

  let is_call = status_is_member "Call"

  let is_redefine = status_is_member "Redefine"

  let is_voidcall = status_is_member "VoidCall"

  let is_dead = status_is_member "Dead"

  let is_deadbycycle = status_is_member "DeadByCycle"
end

module JsonQuerier = struct
  (* Use these with JsonSliceManager!! *)
  let find_chains_holding_redefine : json -> json list =
   (* TODO *)
   (* can we write this point-free? *)
   fun json ->
    let jsons =
      json
      |> ( JsonSliceManager.divide_raw_chains_by_ap
         >> List.map ~f:JsonSliceManager.divide_ap_chain_by_status )
    in
    raise TODO
end
