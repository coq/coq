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
open Term
open Reduction
open Inductive
open Evd
open Environ
open Proof_trees
open Clenv
open Pattern
open Coqlib

(* I implemented the following functions which test whether a term t
   is an inductive but non-recursive type, a general conjuction, a
   general disjunction, or a type with no constructors.

   They are more general than matching with or_term, and_term, etc, 
   since they do not depend on the name of the type. Hence, they 
   also work on ad-hoc disjunctions introduced by the user.
  
  -- Eduardo (6/8/97). *)

type 'a matching_function = constr -> 'a option

type testing_function  = constr -> bool

let op2bool = function Some _ -> true | None -> false

let match_with_non_recursive_type t = 
  match kind_of_term t with 
    | IsApp _ -> 
        let (hdapp,args) = decomp_app t in
        (match kind_of_term hdapp with
           | IsMutInd ind -> 
               if not (Global.mind_is_recursive ind) then 
		 Some (hdapp,args) 
	       else 
		 None 
           | _ -> None)
    | _ -> None

let is_non_recursive_type t = op2bool (match_with_non_recursive_type t)

(* A general conjunction type is a non-recursive inductive type with
   only one constructor. *)

let match_with_conjunction t =
  let (hdapp,args) = decomp_app t in 
  match kind_of_term hdapp with
    | IsMutInd ind -> 
	let mispec = Global.lookup_mind_specif ind in
	if (mis_nconstr mispec = 1)
	  && (not (mis_is_recursive mispec)) && (mis_nrealargs mispec = 0)
        then 
	  Some (hdapp,args)
        else 
	  None
    | _ -> None

let is_conjunction t = op2bool (match_with_conjunction t)
    
(* A general disjunction type is a non-recursive inductive type all
   whose constructors have a single argument. *)

let match_with_disjunction t =
  let (hdapp,args) = decomp_app t in 
  match kind_of_term hdapp with
    | IsMutInd ind  ->
	let mispec = Global.lookup_mind_specif ind in
        let constr_types = mis_nf_lc mispec in
        let only_one_arg c =
	  ((nb_prod c) - (mis_nparams mispec)) = 1 in 
	if (array_for_all only_one_arg constr_types) &&
          (not (mis_is_recursive mispec))
        then 
	  Some (hdapp,args)
        else 
	  None
    | _ -> None

let is_disjunction t = op2bool (match_with_disjunction t)

let match_with_empty_type t =
  let (hdapp,args) = decomp_app t in
  match (kind_of_term hdapp) with
    | IsMutInd ind -> 
        let nconstr = Global.mind_nconstr ind in  
	if nconstr = 0 then Some hdapp else None
    | _ ->  None
	  
let is_empty_type t = op2bool (match_with_empty_type t)

let match_with_unit_type t =
  let (hdapp,args) = decomp_app t in
  match (kind_of_term hdapp) with
    | IsMutInd ind  -> 
        let constr_types = Global.mind_nf_lc ind in 
        let nconstr = Global.mind_nconstr ind in
        let zero_args c =  nb_prod c = Global.mind_nparams ind in  
	if nconstr = 1 && array_for_all zero_args constr_types then 
	  Some hdapp
        else 
	  None
    | _ -> None

let is_unit_type t = op2bool (match_with_unit_type t)


(* Checks if a given term is an application of an
   inductive binary relation R, so that R has only one constructor
   establishing its reflexivity.  *)

let match_with_equation t =
  let (hdapp,args) = decomp_app t in
  match (kind_of_term hdapp) with
    | IsMutInd ind -> 
        let constr_types = Global.mind_nf_lc ind in 
        let nconstr = Global.mind_nconstr ind in
	if nconstr = 1 &&
           (is_matching (build_coq_refl_rel1_pattern ()) constr_types.(0) ||
            is_matching (build_coq_refl_rel1_pattern ()) constr_types.(0)) 
        then 
	  Some (hdapp,args)
        else 
	  None
    | _ -> None

let is_equation t = op2bool (match_with_equation  t)

let match_with_nottype t =
  try
    match matches (build_coq_arrow_pattern ()) t with
      |	[(1,arg);(2,mind)] ->
	  if is_empty_type mind then Some (mind,arg) else None
      | _ -> anomaly "Incorrect pattern matching" 
  with PatternMatchingFailure -> None  

let is_nottype t = op2bool (match_with_nottype t)
		     
let is_imp_term c = match kind_of_term c with
  | IsProd (_,_,b) -> not (dependent (mkRel 1) b)
  | _              -> false



