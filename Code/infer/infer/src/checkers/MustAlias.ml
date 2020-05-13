open! IStd

(* Faithful implementation of CC'18 paper *)

module Hashtbl = Caml.Hashtbl

exception NotImplemented

module V = struct
  include Var
  let hash = Hashtbl.hash
end

module E = struct
  type t = Fieldname.t [@@deriving compare]
  let default =
    let dummy_java_classname = JavaClassName.from_string "DummyClass" in
    Fieldname.make (JavaClass dummy_java_classname) "dummy"
end

module G = Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (V) (E)


(** mapping from procname to graph *)
module GlobalInfo = PrettyPrintable.MakePPMap (Procname)  


let global_info = ref GlobalInfo.empty


let update_global_info (key:Procname.t) (value:G.t) =
  global_info := GlobalInfo.add key value !global_info


(** 대상 SourceFile에 들어 있는 Set of all method를 계산한다. *)
let calculate () =
  let all_source_files = SourceFiles.get_all ~filter:(fun _ -> true) () in
  let all_procnames_listlist = List.map ~f:SourceFiles.proc_names_of_source all_source_files in
  (* 아직은 파일이 하나밖에 없으니까 *)
  List.concat all_procnames_listlist
  

(** init the graph for every procnames: read the set of all methods *)
let batch_initialize_graph () =
  let set_of_all_methods = calculate () in
  List.iter set_of_all_methods ~f:(fun meth -> update_global_info meth (G.create ()))


(** updates the graph based on instruction types *)
let update_graph (instr:Sil.instr) (graph:G.t) =
  match instr with
  | Load {id=id; e=exp} -> raise NotImplemented
  | Store {e1=exp1; e2=exp2} -> raise NotImplemented
  | Prune _ -> graph
  | Call ((ret_id, _), e_fun, arg_ts, _, _) -> raise NotImplemented
  | Metadata md -> raise NotImplemented (* maybe gc here? *)


(** implements all_aliases *)
let all_aliases ap = raise NotImplemented


(** implements intersect *)
let intersect g1 g2 = raise NotImplemented


(** implements gc *)
let gc g = raise NotImplemented

let main () =
  raise NotImplemented
