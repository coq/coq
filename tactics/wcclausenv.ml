(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Nameops
open Term
open Termops
open Sign
open Reductionops
open Environ
open Logic
open Refiner
open Tacmach
open Evd
open Proof_trees
open Clenv
open Evar_refiner

(* If you have a precise idea of the intended use of the following code, please
   write to Eduardo.Gimenez@inria.fr and ask for the prize :-)
   -- Eduardo (11/8/97) *)

