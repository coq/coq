(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Libobject
open Pp

let declare_tactic_option ?(default=Tacexpr.TacId []) name =
  let locality = Summary.ref false ~name:(name^"-locality") in
  let default_tactic_expr : Tacexpr.glob_tactic_expr ref =
    Summary.ref default ~name:(name^"-default-tacexpr")
  in
  let default_tactic : Tacexpr.glob_tactic_expr ref =
    Summary.ref !default_tactic_expr ~name:(name^"-default-tactic")
  in
  let set_default_tactic local t =
    locality := local;
    default_tactic_expr := t;
    default_tactic := t
  in
  let cache (_, (local, tac)) = set_default_tactic local tac in
  let load (_, (local, tac)) =
    if not local then set_default_tactic local tac
  in
  let subst (s, (local, tac)) =
    (local, Tacsubst.subst_tactic s tac)
  in
  let input : bool * Tacexpr.glob_tactic_expr -> obj =
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
  let get () = !locality, Tacinterp.eval_tactic !default_tactic in
  let print () = 
    Pptactic.pr_glob_tactic (Global.env ()) !default_tactic_expr ++
      (if !locality then str" (locally defined)" else str" (globally defined)")
  in
  put, get, print
