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
open Reductionops
open Inductiveops
open Evd
open Environ
open Proof_trees
open Clenv
open Pattern
open Coqlib
open Declarations

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
    | App _ -> 
        let (hdapp,args) = decompose_app t in
        (match kind_of_term hdapp with
           | Ind ind -> 
               if not (Global.lookup_mind (fst ind)).mind_finite then 
		 Some (hdapp,args) 
	       else 
		 None 
           | _ -> None)
    | _ -> None

let is_non_recursive_type t = op2bool (match_with_non_recursive_type t)

(* A general conjunction type is a non-recursive inductive type with
   only one constructor. *)

let match_with_conjunction t =
  let (hdapp,args) = decompose_app t in 
  match kind_of_term hdapp with
    | Ind ind -> 
	let (mib,mip) = Global.lookup_inductive ind in
	if (Array.length mip.mind_consnames = 1)
	  && (not (mis_is_recursive (ind,mib,mip)))
          && (mip.mind_nrealargs = 0)
        then 
	  Some (hdapp,args)
        else 
	  None
    | _ -> None

let is_conjunction t = op2bool (match_with_conjunction t)
    
(* A general disjunction type is a non-recursive inductive type all
   whose constructors have a single argument. *)

let match_with_disjunction t =
  let (hdapp,args) = decompose_app t in 
  match kind_of_term hdapp with
    | Ind ind  ->
        let car = mis_constr_nargs ind in
	if array_for_all (fun ar -> ar = 1) car &&
	   (let (mib,mip) = Global.lookup_inductive ind in
            not (mis_is_recursive (ind,mib,mip)))
        then 
	  Some (hdapp,args)
        else 
	  None
    | _ -> None

let is_disjunction t = op2bool (match_with_disjunction t)

let match_with_empty_type t =
  let (hdapp,args) = decompose_app t in
  match (kind_of_term hdapp) with
    | Ind ind -> 
        let (mib,mip) = Global.lookup_inductive ind in
        let nconstr = Array.length mip.mind_consnames in  
	if nconstr = 0 then Some hdapp else None
    | _ ->  None
	  
let is_empty_type t = op2bool (match_with_empty_type t)

let match_with_unit_type t =
  let (hdapp,args) = decompose_app t in
  match (kind_of_term hdapp) with
    | Ind ind  -> 
        let (mib,mip) = Global.lookup_inductive ind in
        let constr_types = mip.mind_nf_lc in 
        let nconstr = Array.length mip.mind_consnames in
        let zero_args c =
          nb_prod c = mip.mind_nparams in  
	if nconstr = 1 && array_for_all zero_args constr_types then 
	  Some hdapp
        else 
	  None
    | _ -> None

let is_unit_type t = op2bool (match_with_unit_type t)

(* Checks if a given term is an application of an
   inductive binary relation R, so that R has only one constructor
   establishing its reflexivity.  *)

(* ["(A : ?)(x:A)(? A x x)"] and ["(x : ?)(? x x)"] *)
let x = Name (id_of_string "x")
let y = Name (id_of_string "y")
let name_A = Name (id_of_string "A")
let coq_refl_rel1_pattern =
  PProd
    (name_A, PMeta None,
    PProd (x, PRel 1, PApp (PMeta None, [|PRel 2; PRel 1; PRel 1|])))
let coq_refl_rel2_pattern =
  PProd (x, PMeta None, PApp (PMeta None, [|PRel 1; PRel 1|]))

let match_with_equation t =
  let (hdapp,args) = decompose_app t in
  match (kind_of_term hdapp) with
    | Ind ind -> 
        let (mib,mip) = Global.lookup_inductive ind in
        let constr_types = mip.mind_nf_lc in 
        let nconstr = Array.length mip.mind_consnames in
	if nconstr = 1 &&
           (is_matching coq_refl_rel1_pattern constr_types.(0) ||
            is_matching coq_refl_rel1_pattern constr_types.(0)) 
        then 
	  Some (hdapp,args)
        else 
	  None
    | _ -> None

let is_equation t = op2bool (match_with_equation  t)

(* ["(?1 -> ?2)"] *)
let imp a b = PProd (Anonymous, a, b)
let coq_arrow_pattern = imp (PMeta (Some 1)) (PMeta (Some 2))

let match_with_nottype t =
  try
    match matches coq_arrow_pattern t with
      |	[(1,arg);(2,mind)] ->
	  if is_empty_type mind then Some (mind,arg) else None
      | _ -> anomaly "Incorrect pattern matching" 
  with PatternMatchingFailure -> None  

let is_nottype t = op2bool (match_with_nottype t)
		     
let is_imp_term c = 
  match kind_of_term c with
    | Prod (_,_,b) -> not (dependent (mkRel 1) b)
    | _              -> false

let rec has_nodep_prod_after n c =
  match kind_of_term c with
    | Prod (_,_,b) -> 
	( n>0 || not (dependent (mkRel 1) b)) 
	&& (has_nodep_prod_after (n-1) b)
    | _            -> true
	  
let has_nodep_prod = has_nodep_prod_after 0
	
let match_with_nodep_ind t =
  let (hdapp,args) = decompose_app t in
  match (kind_of_term hdapp) with
    | Ind ind  -> 
        let (mib,mip) = Global.lookup_inductive ind in
        let constr_types = mip.mind_nf_lc in 
	let nodep_constr = has_nodep_prod_after mip.mind_nparams in	
	if array_for_all nodep_constr constr_types then 
	  Some (hdapp,args)
        else 
	  None
    | _ -> None
	  
let is_nodep_ind t=op2bool (match_with_nodep_ind t)


