(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Util
open Names
open Tacexpr
open Tacinterp

DECLARE PLUGIN "coretactics"

TACTIC EXTEND reflexivity
  [ "reflexivity" ] -> [ Tactics.intros_reflexivity ]
END

TACTIC EXTEND assumption
  [ "assumption" ] -> [ Tactics.assumption ]
END

let make_vars len =
  List.init len (fun i -> Id.of_string (Printf.sprintf "_%i" i))

let dummy_id = Id.of_string "_"

(** Add a tactic that only uses constrs arguments. Such tactics actually do
    not need to define grammar rules, because tactic arguments are already
    parsed as constrs. So we add them manually. *)
(** TODO: do this automagically in TACTIC EXTEND and use it in this file *)
let add_constr_tactic name len tac =
  let vars = make_vars len in
  (** We pass the arguments through the environment rather than through the
      tactic, to overcome the way tactics arguments are interpreted. *)
  let tac _ ist = Proofview.Goal.raw_enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let map id =
      let c = Id.Map.find id ist.lfun in
      try Taccoerce.coerce_to_closed_constr env c
      with Taccoerce.CannotCoerceTo ty ->
        error_ltac_variable Loc.ghost dummy_id (Some env) c ty
    in
    let args = List.map map vars in
    tac args ist
  end in
  let () = Tacenv.register_ml_tactic name tac in
  let ref = Libnames.Ident (Loc.ghost, Id.of_string name) in
  let args = List.map (fun id -> Some id) vars in
  let body = TacExtend (Loc.ghost, name, []) in
  let body = TacFun (args, TacAtom (Loc.ghost, body)) in
  let obj () = Tacenv.register_ltac false false [ref, false, body] in
  Mltop.declare_cache_obj obj "coretactics"

let () =
  let tac args _ = match args with [c] _ -> Tactics.cut c | _ -> assert false in
  add_constr_tactic "cut" 1 tac

let () =
  let tac args _ = match args with [c] -> Proofview.V82.tactic (Tactics.exact_no_check c) | _ -> assert false in
  add_constr_tactic "exact_no_check" 1 tac

let () =
  let tac args _ = match args with [c] -> Proofview.V82.tactic (Tactics.vm_cast_no_check c) | _ -> assert false in
  add_constr_tactic "vm_cast_no_check" 1 tac

let () =
  let tac args _ = match args with [c] -> Proofview.V82.tactic (Tactics.case_type c) | _ -> assert false in
  add_constr_tactic "casetype" 1 tac

let () =
  let tac args _ = match args with [c] -> Proofview.V82.tactic (Tactics.elim_type c) | _ -> assert false in
  add_constr_tactic "elimtype" 1 tac

let () =
  let tac args _ = match args with [c] -> Tactics.cut_and_apply c | _ -> assert false in
  add_constr_tactic "lapply" 1 tac
