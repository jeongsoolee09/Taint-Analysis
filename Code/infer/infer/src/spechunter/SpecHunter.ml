open! IStd

module L = Logging
module F = Format
module D = DefLocAlias

module Hashtbl = Caml.Hashtbl
module TestMap = PrettyPrintable.MakePPMap (Int)

let main () =
  InferAnalyze.main ~changed_files:None; (* checker를 돌리고 *)
  SetofAllMeths.calculate ();
  LiveRange.main ();
  GetterSetter.main ()

