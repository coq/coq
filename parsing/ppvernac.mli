(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Genarg
open Vernacexpr
open Names
open Nameops
open Nametab
open Util
open Ppconstr
open Pptactic
open Glob_term
open Pcoq
open Libnames
open Ppextend
open Topconstr

val sep_end : unit -> std_ppcmds

val pr_vernac : vernac_expr -> std_ppcmds
