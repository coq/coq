(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t =
  { boot : bool
  ; sort : bool
  ; vos : bool
  ; noglob : bool
  ; coqproject : string option
  ; ml_path : string list
  ; vo_path : (bool * bool * string * string) list
  ; dyndep : string
  ; meta_files : string list
  ; files : string list
  }

val make : unit -> t
val usage : unit -> 'a
val parse : t -> string list -> t
