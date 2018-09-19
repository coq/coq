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

type t

val mk_atts :
  ?polymorphic: bool ->
  ?program: bool -> unit -> t

val attributes_of_flags : Vernacexpr.vernac_flags -> t ->
  bool option (* polymorphism attr *) * t

val locality : t -> bool option
val polymorphic : t -> bool
val template : t -> bool option
val program : t -> bool
val deprecated : t -> deprecation option

val set_polymorphic : t -> bool -> t
