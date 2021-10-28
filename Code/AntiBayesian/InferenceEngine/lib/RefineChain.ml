open Yojson.Basic

exception TODO

type json = Yojson.Basic.t

(* TEMP DON'T SHIP WITH THIS CODE *)
let x = Deserializer.deserialize_json "Chain.json"

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
