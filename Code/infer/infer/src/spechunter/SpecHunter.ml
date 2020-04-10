open! IStd

module L = Logging
module F = Format
module D = DefLocAlias

exception NotImplemented

(* LRM을 돌린다 *)
let run_lrm summary_table : unit = raise NotImplemented

(* (DFA를 포함한) 체커들을 돌리고, DFA 모듈의 해시 테이블을 가져온 다음, 그 해시 테이블을 LRM에 넘긴다 *)
let main () =
  InferAnalyze.main ~changed_files:None;
  let summary_table = DefLocAlias.TransferFunctions.summaries in
  run_lrm summary_table;
  ()
