(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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
    method source_buffer : GSourceView3.source_buffer
    method connect : message_view_signals
    method clear : unit
    method add : Pp.t -> unit
    method add_string : string -> unit
    method set : Pp.t -> unit
    method refresh : bool -> unit
    method push : Ideutils.logger
      (** same as [add], but with an explicit level instead of [Notice] *)

    (** In use by the ltac debugger *)
    method debug_prompt : Pp.t -> unit

    method has_selection : bool
    method get_selected_text : string
  end

val message_view : unit -> message_view

val forward_send_db_cmd : (string -> unit) ref
