(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type deprecation = { since : string option ; note : string option }

val mk_deprecation : ?since: string option -> ?note: string option -> unit -> deprecation

type t = {
  loc : Loc.t option;
  locality : bool option;
  polymorphic : bool;
  template : bool option;
  program : bool;
  deprecated : deprecation option;
}

val mk_atts : ?loc: Loc.t option -> ?locality: bool option ->
  ?polymorphic: bool -> ?template:bool option ->
  ?program: bool -> ?deprecated: deprecation option -> unit -> t
