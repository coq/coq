(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type nativecompiler = NativeYes | NativeNo | NativeOndemand

module Prefs : sig

(** User-setable options from command line [configure] arugments *)
type t =
  { prefix : string option
  (** root prefix for installation  *)
  ; quiet : bool
  (** whether to display a summary *)
  ; interactive : bool
  (** whether to ask for unspecified values *)
  ; libdir : string option
  (** override $prefix/lib/coq *)
  ; configdir : string option
  (** override /etc/xdg/coq *)
  ; datadir : string option
  (** override $prefix/share/coq *)
  ; mandir : string option
  (** override $prefix/man *)
  ; docdir : string option
  (** override $prefix/doc *)
  ; arch : string option
  (** override arch auto-detection *)
  ; natdynlink : bool
  (** native dynlink enabled [only relevant to coq_makefile] *)
  ; browser : string option
  (** override default browser command [for RocqIDE] *)
  ; bytecodecompiler : bool
  (** Enable/disable Rocq's VM *)
  ; nativecompiler : nativecompiler
  (** Enable/disable Rocq's native compiler *)
  ; coqwebsite : string
  (** Override Rocq's website, used by distributions  *)
  ; debug : bool
  (** Debug package and environment detection *)
  }

end

val parse_args : unit -> Prefs.t

val cprintf : Prefs.t -> ('a, out_channel, unit, unit) format4 -> 'a
