(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Tacbindings

(** Printing of bindings *)
let pr_binding prc = let open CAst in function
  | {loc;v=(NamedHyp id, c)} -> hov 1 (Names.Id.print id ++ str " := " ++ cut () ++ prc c)
  | {loc;v=(AnonHyp n, c)} -> hov 1 (int n ++ str " := " ++ cut () ++ prc c)

let pr_bindings prc prlc = function
  | ImplicitBindings l ->
    brk (1,1) ++ str "with" ++ brk (1,1) ++
    pr_sequence prc l
  | ExplicitBindings l ->
    brk (1,1) ++ str "with" ++ brk (1,1) ++
    pr_sequence (fun b -> str"(" ++ pr_binding prlc b ++ str")") l
  | NoBindings -> mt ()

let pr_bindings_no_with prc prlc = function
  | ImplicitBindings l ->
    brk (0,1) ++ prlist_with_sep spc prc l
  | ExplicitBindings l ->
    brk (0,1) ++ prlist_with_sep spc (fun b -> str"(" ++ pr_binding prlc b ++ str")") l
  | NoBindings -> mt ()

let pr_with_bindings prc prlc (c,bl) =
  hov 1 (prc c ++ pr_bindings prc prlc bl)

