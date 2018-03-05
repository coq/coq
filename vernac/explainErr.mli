(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Toplevel Exception *)
exception EvaluatedError of Pp.t * exn option

(** Pre-explain a vernac interpretation error *)

val process_vernac_interp_error : ?allow_uncaught:bool -> Util.iexn -> Util.iexn

(** General explain function. Should not be used directly now,
    see instead function [Errors.print] and variants *)

val explain_exn_default : exn -> Pp.t

val register_additional_error_info : (Util.iexn -> (Pp.t option Loc.located) option) -> unit
