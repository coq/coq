(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This is to be eventually deprecated in favor of packages *)
type ide = Opt | Byte | No

type nativecompiler = NativeYes | NativeNo | NativeOndemand

module Prefs : sig

(** User-setable options from command line [configure] arugments *)
type t =
  { prefix : string option
  (** root prefix for installation  *)
  ; interactive : bool
  (** whether to display a summary *)
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
  ; coqide : ide option
  (** coqide build [yes/no/byte] *)
  ; macintegration : bool
  (** whether to integrate CoqIDE with OSX  *)
  ; browser : string option
  (** override default browser command [for CoqIDE] *)
  ; withdoc : bool
  (** Build documentation [controls makefile variable]  *)
  ; bin_annot : bool
  ; annot : bool
  (** OCaml annot options [only relevant to coq_makefile] *)
  ; bytecodecompiler : bool
  (** Enable/disable Coq's VM *)
  ; nativecompiler : nativecompiler
  (** Enable/disable Coq's native compiler *)
  ; coqwebsite : string
  (** Override Coq's website, used by distributions  *)
  ; warn_error : bool
  (** Enable/disable warn-error in makefile build *)
  ; debug : bool
  (** Debug package and environment detection *)
  }

end

val parse_args : unit -> Prefs.t

val cprintf : Prefs.t -> ('a, out_channel, unit, unit) format4 -> 'a
