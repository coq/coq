(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Error report. *)

val print_loc : Loc.t -> Pp.std_ppcmds

(** Pre-explain a vernac interpretation error *)

val process_vernac_interp_error : Util.iexn -> Util.iexn

(** General explain function. Should not be used directly now,
    see instead function [Errors.print] and variants *)

val explain_exn_default : exn -> Pp.std_ppcmds

