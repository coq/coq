(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

class type message_view_signals =
object
  inherit GObj.misc_signals
  inherit GUtil.add_ml_signals
  method pushed : callback:Ideutils.logger -> GtkSignal.id
end

class type message_view =
  object
    inherit GObj.widget
    method connect : message_view_signals
    method clear : unit
    method add : Richpp.richpp -> unit
    method add_string : string -> unit
    method set : Richpp.richpp -> unit
    method push : Ideutils.logger
      (** same as [add], but with an explicit level instead of [Notice] *)
    method buffer : GText.buffer
      (** for more advanced text edition *)
  end

val message_view : unit -> message_view
