open! IStd
module L = Logging
module F = Format
module D = DefLocAlias
module Hashtbl = Caml.Hashtbl
module TestMap = PrettyPrintable.MakePPMap (Int)

let main () =
  InferAnalyze.main ~changed_files:None ;
  SetofAllMeths.calculate () ;
  ExtractAnnotations.main () ;
  LiveRange.main () ;
  GetterSetter.main ()
