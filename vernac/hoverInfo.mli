(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type hover = {
    docstring : Pp.t;
    types : Pp.t option;
    def_loc : Loc.t; (* shifted *)
    id : Stateid.t;
}

type t
val empty : unit -> t
val query : t -> Loc.t -> hover option
val shift : t -> from:int -> amount:int -> t
val add_docstring : t -> ?types:Pp.t -> Stateid.t -> Loc.t -> docstring:Pp.t -> t
val prune : t -> Stateid.t list -> t

(* can be called by any client *)
val update_current_info :
 uri:string -> sentence_id:Stateid.t -> (t -> t) -> unit

(* can be called by the owner once *)
val set_update_current_info : (uri:string -> sentence_id:Stateid.t -> (t -> t) -> unit) -> unit
