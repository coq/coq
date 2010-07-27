(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Libobject
open Proof_type
open Pp

let declare_tactic_option ?(default=Tacexpr.TacId []) name =
  let default_tactic_expr : Tacexpr.glob_tactic_expr ref = ref default in
  let default_tactic : Proof_type.tactic ref = ref (Tacinterp.eval_tactic !default_tactic_expr) in
  let locality = ref false in
  let set_default_tactic local t = 
    locality := local;
    default_tactic_expr := t; default_tactic := Tacinterp.eval_tactic t 
  in
  let cache (_, (local, tac)) = set_default_tactic local tac in
  let load (_, (local, tac)) =
    if not local then set_default_tactic local tac
  in
  let subst (s, (local, tac)) =
    (local, Tacinterp.subst_tactic s tac)
  in
  let input, _output = 
    declare_object
      { (default_object name) with
	cache_function = cache;
	load_function = (fun _ -> load);
	open_function = (fun _ -> load);
	classify_function = (fun (local, tac) ->
	  if local then Dispose else Substitute (local, tac));
	subst_function = subst}
  in
  let put local tac =
    set_default_tactic local tac;
    Lib.add_anonymous_leaf (input (local, tac))
  in
  let get () = !locality, !default_tactic in
  let print () = 
    Pptactic.pr_glob_tactic (Global.env ()) !default_tactic_expr ++
      (if !locality then str" (locally defined)" else str" (globally defined)")
  in
  let freeze () = !locality, !default_tactic_expr in
  let unfreeze (local, t) = set_default_tactic local t in
  let init () = () in
    Summary.declare_summary name
      { Summary.freeze_function = freeze;
        Summary.unfreeze_function = unfreeze;
        Summary.init_function = init };
    put, get, print
      
