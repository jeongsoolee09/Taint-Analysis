open SpecHunterUtils
module F = Format
module Hashtbl = Caml.Hashtbl

let ( >>= ) = List.( >>= )

and ( >>| ) = List.( >>| )

module ResolveByDirectory = struct
  let is_directory (abs_dir : string) : bool =
    match Sys.is_directory abs_dir with `Yes -> true | _ -> false


  let walk_for_extension (root_dir : string) (extension : string) : string list =
    let rec inner (current_dir : string) (filename_acc : string list) =
      let subdirectories =
        Array.filter ~f:is_directory
          (Array.map ~f:(fun name -> current_dir ^ "/" ^ name) (Sys.readdir current_dir))
      in
      let files_matching_extension =
        Array.filter ~f:(not << is_directory)
          (Array.map ~f:(fun name -> current_dir ^ "/" ^ name) (Sys.readdir current_dir))
        |> Array.fold
             ~f:(fun acc elem ->
               if String.is_suffix elem ~suffix:extension then elem :: acc else acc )
             ~init:[]
      in
      if Array.is_empty subdirectories then filename_acc @ files_matching_extension
      else
        Array.fold subdirectories
          ~f:(fun acc subdirectory -> inner subdirectory acc)
          ~init:(filename_acc @ files_matching_extension)
    in
    inner root_dir []


  let extract_filename_without_extension_and_dirs (full_filename : string) : string =
    let filename_only = List.last_exn @@ String.split ~on:'/' full_filename in
    List.hd_exn @@ String.split ~on:'.' filename_only


  (** does this directory have any java file (recursively?) *)
  let has_java (dir : string) : bool = not @@ List.is_empty @@ walk_for_extension dir ".java"

  (** get the subdirs containing .java files. *)
  let get_compilation_unit_absdirs (root_dir : string) : string list =
    Sys.readdir root_dir
    |> Array.map ~f:(fun subdir -> root_dir ^ subdir)
    |> Array.filter ~f:is_directory |> Array.filter ~f:has_java |> Array.to_list


  let get_compilation_unit_subdirs (root_dir : string) : string list =
    let absdirs = get_compilation_unit_absdirs root_dir in
    List.map ~f:(fun absdir -> List.last_exn @@ String.split ~on:'/' absdir) absdirs


  let get_test_classnames =
    let cache = Hashtbl.create 777 in
    fun (root_dir : string) : string list ->
      match Hashtbl.find_opt cache root_dir with
      | None ->
          let out =
            walk_for_extension root_dir ".java"
            |> List.filter ~f:(String.is_substring ~substring:"/test/")
            >>| extract_filename_without_extension_and_dirs
          in
          Hashtbl.add cache root_dir out ;
          out
      | Some res ->
          res


  let is_testcode (proc : Procname.t) : bool =
    let classname =
      List.last_exn @@ String.split ~on:'.' @@ Option.value ~default:""
      @@ Procname.get_class_name proc
    in
    let test_classnames = get_test_classnames @@ Sys.getcwd () in
    List.mem test_classnames classname ~equal:String.equal
end

module ResolveByAnnotation = struct
  let get_annotation (procname : Procname.t) : Annot.Method.t =
    match Procdesc.load procname with
    | None ->
        L.die InternalError "get_annotation failed, procname: %a" Procname.pp procname
    | Some pdesc ->
        (Procdesc.get_attributes pdesc).ProcAttributes.method_annotation


  let is_testcode (proc : Procname.t) : bool =
    let annots = ExtractAnnotations.load_annot_for proc in
    List.exists
      ~f:(fun ((annot : Annot.t), _) ->
        String.equal annot.class_name "org.junit.Test"
        || String.equal annot.class_name "org.testng.annotations.Test" )
      annots.return
end

module ResolveByClassname = struct
  let is_testcode (proc : Procname.t) : bool =
    String.is_substring (get_class_name proc) ~substring:"Test"
end

let is_test_method =
  let cache = Hashtbl.create 777 in
  fun (proc : Procname.t) : bool ->
    match Hashtbl.find_opt cache proc with
    | None ->
        let out =
          ResolveByDirectory.is_testcode proc
          || ResolveByAnnotation.is_testcode proc
          || ResolveByClassname.is_testcode proc
        in
        Hashtbl.add cache proc out ;
        out
    | Some res ->
        res


let make_class_table (hashtbl : (string, bool) Hashtbl.t) : unit =
  let all_procs =
    SourceFiles.get_all ~filter:(fun _ -> true) ()
    |> List.map ~f:SourceFiles.proc_names_of_source
    |> List.concat
  in
  let all_test_methods = List.filter ~f:is_test_method all_procs in
  List.iter
    ~f:(fun meth -> Hashtbl.add hashtbl (get_class_name meth) (is_test_method meth))
    all_test_methods


let belongs_to_test_class (class_table : (string, bool) Hashtbl.t) (proc : Procname.t) : bool =
  match Hashtbl.find_opt class_table (get_class_name proc) with None -> false | Some res -> res
