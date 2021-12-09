open! IStd
module L = Logging
module F = Format
module D = DefLocAlias
module Hashtbl = Caml.Hashtbl
module TestMap = PrettyPrintable.MakePPMap (Int)


let run_only_when_not_file_exists (f: unit -> unit) (filename: string) : unit =
    match Sys.file_exists (F.asprintf "%s/%s" (Sys.getcwd ()) filename) with
    | `No | `Unknown -> f ()
    | `Yes -> L.progress "Skipped calculating %s because it's already there.@." filename


let infer_analyze_main () =
    InferAnalyze.main ~changed_files:None;
    let hashtbl = Hashtbl.create 777 in
    SummaryLoader.load_summary_from_disk_to hashtbl ~exclude_test:true;
    let out_chan = Out_channel.create "AnalysisResult.bin" in
    Marshal.to_channel out_chan hashtbl [];
    Out_channel.close out_chan


let main () =
  run_only_when_not_file_exists infer_analyze_main "AnalysisResult.bin";
  run_only_when_not_file_exists SetofAllMeths.calculate "Methods.txt";
  run_only_when_not_file_exists ExtractAnnotations.main "Annotations.json";
  run_only_when_not_file_exists LiveRange.main "Chain.json";
  run_only_when_not_file_exists GetterSetter.main  "GetterSetter.json"
