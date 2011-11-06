(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Pp
open Genarg
open Vernacexpr
open Names
open Nameops
open Nametab
open Util
open Ppconstr
open Pptactic
open Rawterm
open Pcoq
open Libnames
open Ppextend
open Topconstr

val sep_end : unit -> std_ppcmds

val pr_vernac : vernac_expr -> std_ppcmds
