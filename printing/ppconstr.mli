(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module implements pretty-printers for constr_expr syntactic
    objects and their subcomponents. *)

(** The default pretty-printers produce {!Pp.std_ppcmds} that are
    interpreted as raw strings. *)
include Ppconstrsig.Pp

(** The rich pretty-printers produce {!Pp.std_ppcmds} that are
    interpreted as annotated strings. The annotations can be
    retrieved using {!RichPp.rich_pp}. Their definitions are
    located in {!Ppannotation.t}. *)

module Richpp : Ppconstrsig.Pp
