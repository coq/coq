(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

class type message_view =
  object
    inherit GObj.widget
    method clear : unit
    method add : string -> unit
    method set : string -> unit
    method push : Pp.message_level -> string -> unit
      (** same as [add], but with an explicit level instead of [Notice] *)
    method buffer : GText.buffer
      (** for more advanced text edition *)
    method modify_font : Pango.font_description -> unit
  end

val message_view : unit -> message_view
