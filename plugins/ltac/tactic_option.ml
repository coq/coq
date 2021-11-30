(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Libobject

let declare_tactic_option ?(default=CAst.make (Tacexpr.TacId[])) name =
  let default_tactic : Tacexpr.glob_tactic_expr ref =
    Summary.ref default ~name:(name^"-default-tactic")
  in
  let set_default_tactic t =
    default_tactic := t
  in
  let cache (local, tac) = set_default_tactic tac in
  let load (local, tac) =
    if not local then set_default_tactic tac
  in
  let subst (s, (local, tac)) =
    (local, Tacsubst.subst_tactic s tac)
  in
  let input : bool * Tacexpr.glob_tactic_expr -> obj =
    declare_object
      { (default_object name) with
        cache_function = cache;
        load_function = (fun _ -> load);
        open_function = simple_open (fun _ -> load);
        classify_function = (fun (local, _) -> if local then Dispose else Substitute);
        subst_function = subst}
  in
  let put local tac =
    Lib.add_leaf (input (local, tac))
  in
  let get () = Tacinterp.eval_tactic !default_tactic in
  let print () = Pptactic.pr_glob_tactic (Global.env ()) !default_tactic in
  put, get, print
