(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Names

type precedence (* on kernel_name *)

type result = Equivalent | Smaller | Greater | Uncomparable

(* precedence where equal names are Equivalent
   and distinct names are Uncomparable *)
val empty_prec : precedence

val compare : precedence -> kernel_name -> kernel_name -> result

val is_equiv : precedence -> kernel_name -> kernel_name -> bool
val is_smaller : precedence -> kernel_name -> kernel_name -> bool
val is_greater : precedence -> kernel_name -> kernel_name -> bool
val is_smaller_eq : precedence -> kernel_name -> kernel_name -> bool
val is_greater_eq : precedence -> kernel_name -> kernel_name -> bool
val are_uncomparable : precedence -> kernel_name -> kernel_name -> bool

exception Incompatible

val add_equiv : precedence -> kernel_name -> kernel_name -> precedence
val add_greater : precedence -> kernel_name -> kernel_name -> precedence

type prec_def = result * kernel_name list

val add_prec_list : kernel_name -> precedence -> prec_def -> precedence
