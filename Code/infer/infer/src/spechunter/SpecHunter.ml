open! IStd

module L = Logging
module F = Format
module D = DefLocAlias

module Hashtbl = Caml.Hashtbl

let main () =
  InferAnalyze.main ~changed_files:None; (* checker를 돌리고 *)
  L.progress "%s" D.teststring;
  L.progress "%d\n" D.testint;
  L.progress "length in main: %d@." (Hashtbl.length D.summaries);
  L.progress "length in main: %d@." (Hashtbl.length DefLocAlias.TransferFunctions.history);
  L.progress "length in main: %d@." (Hashtbl.length DefLocAlias.TransferFunctions.callgraph);
  LiveRange.run_lrm () (* LRM 돌리고 *)
