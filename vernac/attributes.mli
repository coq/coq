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
(** The type of parsed attributes *)

type 'a attribute
(** Used to get the value for some attribute out of [t] in a typed
   way. *)

val read : 'a attribute -> t -> 'a option
(** [read x atts] returns the value of attribute [x] if it is set in
   [atts] *)

val mk_atts :
  ?polymorphic: bool ->
  ?program: bool -> unit -> t

val attributes_of_flags : Vernacexpr.vernac_flags -> t ->
  bool option (* polymorphism attr *) * t


type 'a flag_parser = 'a option -> Vernacexpr.vernac_flag_value -> 'a
(** How to parse some specific attribute key (eg "polymorphic" and
   "monomorphic" are separate keys for the same attribute). The
   previous value of the attribute if set is also passed, allowing
   handling of multiply set attributes as you desire (error, make a
   list, etc). *)

val register_attribute : name:string -> 'a flag_parser CString.Map.t ->
  'a attribute
(** You can register multiple keys for the same attribute, eg
   "template" and "notemplate" keys produce values for the same
   "templateness" attribute. The [name] is currently not used. *)

val locality : t -> bool option
val polymorphic : t -> bool
val template : t -> bool option
val program : t -> bool
val deprecated : t -> deprecation option

val set_polymorphic : t -> bool -> t
