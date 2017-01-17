(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Toplevel Exception *)
exception EvaluatedError of Pp.std_ppcmds * exn option

(** Pre-explain a vernac interpretation error *)

val process_vernac_interp_error : ?allow_uncaught:bool -> Util.iexn -> Util.iexn

(** General explain function. Should not be used directly now,
    see instead function [Errors.print] and variants *)

val explain_exn_default : exn -> Pp.std_ppcmds

val register_additional_error_info : (Util.iexn -> (Pp.std_ppcmds option Loc.located) option) -> unit
