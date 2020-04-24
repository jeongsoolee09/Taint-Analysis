(** A Very Naive Call Graph Module:
 *   각 파일의 각 Procdesc.t의 각 노드의 각 instr를 뽑아서 해당 메소드의 콜리를 계산해 낸다. **)

open! IStd
open DefLocAlias.TransferFunctions
open DefLocAliasSearches
open DefLocAliasLogicTests
open DefLocAliasDomain

module Hashtbl = Caml.Hashtbl
module S = DefLocAliasDomain.AbstractState
module A = DefLocAliasDomain.SetofAliases

module L = Logging
module F = Format

