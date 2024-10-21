(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* (c) Copyright 2006-2015 Microsoft Corporation and Inria.             *)

open Genarg
open Ssrmatching

(** CS cpattern: (f _), (X in t), (t in X in t), (t as X in t) *)
val cpattern         : cpattern Procq.Entry.t
val wit_cpattern     : cpattern uniform_genarg_type

(** OS cpattern: f _, (X in t), (t in X in t), (t as X in t) *)
val lcpattern         : cpattern Procq.Entry.t
val wit_lcpattern     : cpattern uniform_genarg_type

(** OS rpattern: f _, in t, X in t, in X in t, t in X in t, t as X in t *)
val rpattern         : rpattern Procq.Entry.t
val wit_rpattern     : rpattern uniform_genarg_type

val wit_ssrpatternarg : rpattern uniform_genarg_type
