(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

class command_window : string -> RocqDriver.rocqtop -> RocqOps.rocqops ->
    Wg_RoutedMessageViews.message_views_router -> int ->
  object
    method new_query : ?command:string -> ?term:string -> unit -> unit
    method pack_in : (GObj.widget -> unit) -> unit
    method show : unit
    method hide : unit
    method visible : bool
  end
