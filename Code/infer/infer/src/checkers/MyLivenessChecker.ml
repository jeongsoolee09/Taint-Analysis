(** An Intraprocedural Liveness Analyzer. *)

exception NotImplemented
exception UndefinedSemantics
exception IDontKnow

module L = Logging
module F = Format

module M = MyLivenessCheckerDomain
module Payload = SummaryPayload.Make (struct
    type t = M.t

    let field = Payloads.Fields.my_liveness_checker
  end)

module TransferFunctions = struct
  module CFG = ProcCfg.OneInstrPerNode (ProcCfg.Backward (ProcCfg.Exceptional))
  module Domain = M
  type extras = ProcData.no_extras
  type instr = Sil.instr

  (** get the set of variables from a Prune condition expression.
      For now, we assume that only variables and conditions are contained in the conditions *)
  let rec extract_vars_from_cond (exp : Exp.t) =
    match exp with
    | BinOp (_, e1, e2) -> M.join (extract_vars_from_cond e2) (extract_vars_from_cond e1)
    | Lvar pv -> M.singleton pv
    | _ -> M.empty

  let use_of = function
    | Sil.Load {id=_; e=Lvar pv} -> M.singleton pv
    | Sil.Store {e1=_; e2=exp2} ->
        begin match exp2 with
          | Lvar pv -> M.singleton pv
          | _ -> M.empty
        end
    | Sil.Prune (exp, _, _, _) -> extract_vars_from_cond exp
    | Sil.Call _ -> M.empty 
    | Sil.Metadata _ -> M.empty
    | _ -> M.empty

  let def_of = function
    | Sil.Load {id=_; e=_} -> M.empty
    | Sil.Store {e1=exp1; e2=_;} ->
        begin match exp1 with
          | Lvar pv -> M.singleton pv
          | _ -> M.empty
        end
    | Sil.Prune (_, _, _, _) -> M.empty
    | Sil.Call _ -> M.empty
    | Sil.Metadata _ -> M.empty

  let exec_instr pre _ _ instr =
    M.join (use_of instr) (M.diff pre (def_of instr))

  let pp_session_name node fmt = F.fprintf fmt "JSL liveness %a" CFG.Node.pp_id (CFG.Node.id node)

  let widening_threshold = 20

  let widen ~(prev:M.t) ~(next:M.t) ~num_iters:_ : M.t = M.join prev next
end

module Analyzer = AbstractInterpreter.MakeRPO (TransferFunctions)

let checker {Callbacks.summary=summary; exe_env} : Summary.t =
  let proc_name = Summary.get_proc_name summary in
  let tenv = Exe_env.get_tenv exe_env proc_name in
  match Analyzer.compute_post (ProcData.make_default summary tenv) ~initial:M.empty with
  | Some post ->
      Payload.update_summary post summary
  | None -> raise IDontKnow
