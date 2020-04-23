open! IStd

module L = Logging
module F = Format
module D = DefLocAlias

let main () =
  InferAnalyze.main ~changed_files:None; (* checker를 돌리고 *)
  LiveRange.run_lrm () (* LRM 돌리고 *)