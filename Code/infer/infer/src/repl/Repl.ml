open! IStd
module CLOpt = CommandLineOption
module L = Logging

let run driver_mode =
  let open Driver in
  run_prologue driver_mode ;
  let changed_files = read_config_changed_files () in
  InferAnalyze.invalidate_changed_procedures changed_files ;
  capture driver_mode ~changed_files ;
  analyze_and_report driver_mode ~changed_files ;
  run_epilogue ()


let run driver_mode = ScubaLogging.execute_with_time_logging "run" (fun () -> run driver_mode)

let setup () =
  let db_start =
    let already_started = ref false in
    fun () ->
      if (not !already_started) && CLOpt.is_originator && DBWriter.use_daemon then (
        DBWriter.start () ;
        Epilogues.register ~f:DBWriter.stop ~description:"Stop Sqlite write daemon" ;
        already_started := true )
  in
  ( match Config.command with
  | Analyze ->
      ResultsDir.assert_results_dir "have you run capture before?"
  | Report | ReportDiff ->
      ResultsDir.create_results_dir ()
  | Capture | Compile | Run ->
      let driver_mode = Lazy.force Driver.mode_from_command_line in
      if
        Config.(
          (* In Buck mode, delete infer-out directories inside buck-out to start fresh and to
             avoid getting errors because some of their contents is missing (removed by
             [Driver.clean_results_dir ()]). *)
          (buck && Option.exists buck_mode ~f:BuckMode.is_clang_flavors) || genrule_mode)
        || not
             ( Driver.is_analyze_mode driver_mode
             || Config.(
                  continue_capture || infer_is_clang || infer_is_javac || reactive_mode
                  || incremental_analysis) )
      then ResultsDir.remove_results_dir () ;
      ResultsDir.create_results_dir () ;
      if
        CLOpt.is_originator && (not Config.continue_capture)
        && not (Driver.is_analyze_mode driver_mode)
      then (
        db_start () ;
        SourceFiles.mark_all_stale () )
  | Explore ->
      ResultsDir.assert_results_dir "please run an infer analysis first"
  | SpecHunter ->
      ResultsDir.assert_results_dir "hello world! you shouldn't be seeing this"
  | Swan ->
      ResultsDir.assert_results_dir "hello world! you shouldn't be seeing this"
  | Debug ->
      ResultsDir.assert_results_dir "please run an infer analysis or capture first"
  | Help ->
      () ) ;
  let has_result_dir =
    match Config.command with
    | Analyze | Capture | Compile | Debug | Explore | Report | ReportDiff | Run | SpecHunter | Swan
      ->
        true
    | Help ->
        false
  in
  if has_result_dir then (
    db_start () ;
    if CLOpt.is_originator then ResultsDir.RunState.add_run_to_sequence () ) ;
  has_result_dir


let print_active_checkers () =
  (if Config.print_active_checkers && CLOpt.is_originator then L.result else L.environment_info)
    "Active checkers: %a@."
    (Pp.seq ~sep:", " RegisterCheckers.pp_checker)
    (RegisterCheckers.get_active_checkers ())


let print_scheduler () =
  L.environment_info "Scheduler: %s@\n"
    ( match Config.scheduler with
    | File ->
        "file"
    | Restart ->
        "restart"
    | SyntacticCallGraph ->
        "callgraph" )


let print_cores_used () = L.environment_info "Cores used: %d@\n" Config.jobs

let log_environment_info () =
  L.environment_info "CWD = %s@\n" (Sys.getcwd ()) ;
  ( match Config.inferconfig_file with
  | Some file ->
      L.environment_info "Read configuration in %s@\n" file
  | None ->
      L.environment_info "No .inferconfig file found@\n" ) ;
  L.environment_info "Project root = %s@\n" Config.project_root ;
  let infer_args =
    Sys.getenv CLOpt.args_env_var
    |> Option.map ~f:(String.split ~on:CLOpt.env_var_sep)
    |> Option.value ~default:["<not set>"]
  in
  L.environment_info "INFER_ARGS = %a@\n"
    (Pp.cli_args_with_verbosity ~verbose:Config.debug_mode)
    infer_args ;
  L.environment_info "command line arguments: %a@\n"
    (Pp.cli_args_with_verbosity ~verbose:Config.debug_mode)
    (Array.to_list Sys.(get_argv ())) ;
  ( match Utils.get_available_memory_MB () with
  | None ->
      L.environment_info "Could not retrieve available memory (possibly not on Linux)@\n"
  | Some available_memory ->
      L.environment_info "Available memory at startup: %d MB@\n" available_memory ;
      ScubaLogging.log_count ~label:"startup_mem_avail_MB" ~value:available_memory ) ;
  print_active_checkers () ;
  print_scheduler () ;
  print_cores_used ()


(* ============ Let's invoke Infer from Utop! ============ *)

(** `infer analyze -- mvn compile` *)
let repl_run_mvn_compile () =
  if CommandLineOption.is_originator then ScubaLogging.register_global_log_flushing_at_exit () ;
  let has_results_dir = setup () in
  if has_results_dir then log_environment_info () ;
  if has_results_dir && Config.debug_mode && CLOpt.is_originator then (
    L.progress "Logs in %s@." (ResultsDir.get_path Logs) ;
    Option.iter Config.scuba_execution_id ~f:(fun id -> L.progress "Execution ID %Ld@." id) ) ;
  run @@ Driver.Maven {prog= "mvn"; args= ["compile"]}


let repl_analyze () =
  if CommandLineOption.is_originator then ScubaLogging.register_global_log_flushing_at_exit () ;
  let has_results_dir = setup () in
  if has_results_dir then log_environment_info () ;
  if has_results_dir && Config.debug_mode && CLOpt.is_originator then (
    L.progress "Logs in %s@." (ResultsDir.get_path Logs) ;
    Option.iter Config.scuba_execution_id ~f:(fun id -> L.progress "Execution ID %Ld@." id) ) ;
  run Driver.Analyze


let repl_spechunter = SpecHunter.main
