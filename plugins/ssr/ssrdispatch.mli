(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type _ ffi =
| Arg : ('a,'b,'c) Genarg.genarg_type * 'f ffi -> ('c -> 'f) ffi
| Nil : unit Proofview.tactic ffi

(* [register_overloaded name ffi f] registers an Ltac symbol ["ssr_"^name]
 * pointing to [f] and returns some code [f'] that goes trough the Hint Extern
 * db called ["ssr_"^name]. The designer is expected to put in the
 * Hint db a default entry with the Ltac symbol. The user can add more
 * entries to overload the meaning of [name] *)
val register_overloaded : string -> 'a ffi -> 'a -> 'a
