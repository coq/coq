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

type t = {
  prefix : string option;
  interactive : bool;
  output_summary : bool;
  vmbyteflags : string option;
  custom : bool option;
  libdir : string option;
  configdir : string option;
  datadir : string option;
  mandir : string option;
  docdir : string option;
  ocamlfindcmd : string option;
  arch : string option;
  natdynlink : bool;
  coqide : ide option;
  macintegration : bool;
  browser : string option;
  withdoc : bool;
  byteonly : bool;
  flambda_flags : string list;
  debug : bool;
  profile : bool;
  bin_annot : bool;
  annot : bool;
  bytecodecompiler : bool;
  nativecompiler : nativecompiler;
  coqwebsite : string;
  force_caml_version : bool;
  force_findlib_version : bool;
  warn_error : bool;
  dune_profile : string;
  install_enabled : bool;
}

end

val parse_args : unit -> Prefs.t
