(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Mod_subst
open Libobject

(**
  This module implements a hook for the "print" function, which
  is instantiated in theories/Init/Specif.v. The code is 
  partly inspired by tactics/extratactics.ml4
 *)

(** create a persistent set to store printing functions *)
module ConstrSet = Set.Make (Constr)

let print_ref = Summary.ref ~name:"printing-side-effect" ConstrSet.empty

(** a test to know whether a constant is actually the printing function *)
let is_print_ref c = ConstrSet.exists (Constr.equal c) !print_ref

let cache_reduction_printing_effect (_,x) =
  print_ref := ConstrSet.add x !print_ref

let subst_reduction_printing_effect (subst,x) =
  subst_mps subst x

let inReductionPrintingEffect : Constr.constr -> obj =
  declare_object {(default_object "REDUCTION-PRINTING-EFFECT") with
    cache_function = cache_reduction_printing_effect;
    open_function = (fun i o -> if Int.equal i 1 then cache_reduction_printing_effect o);
    subst_function = subst_reduction_printing_effect;
    classify_function = (fun o -> Substitute o) }

(** A function to set the value of the print function *)
let set_print_ref x =
  Lib.add_anonymous_leaf (inReductionPrintingEffect (Universes.constr_of_global x))
