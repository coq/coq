(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Hugo Herbelin from contents related to inductive schemes
   initially developed by Christine Paulin (induction schemes), Vincent
   Siles (decidable equality and boolean equality) and Matthieu Sozeau
   (combined scheme) in file command.ml, Sep 2009 *)

(* This file builds schemes related to case analysis and recursion schemes *)

open Term
open Indrec
open Declarations
open Typeops
open Termops
open Ind_tables

(* Induction/recursion schemes *)

let optimize_non_type_induction_scheme kind dep sort ind =
  if check_scheme kind ind then
    (* in case the inductive has a type elimination, generates only one
       induction scheme, the other ones share the same code with the
       apropriate type *)
    let cte = find_scheme kind ind in
    let c = mkConst cte in
    let t = type_of_constant (Global.env()) cte in
    let (mib,mip) = Global.lookup_inductive ind in
    let npars =
      (* if a constructor of [ind] contains a recursive call, the scheme
	 is generalized only wrt recursively uniform parameters *)
      if (Inductiveops.mis_is_recursive_subset [snd ind] mip.mind_recargs)
      then
	mib.mind_nparams_rec
      else
	mib.mind_nparams in
    snd (weaken_sort_scheme (new_sort_in_family sort) npars c t)
  else
    build_induction_scheme (Global.env()) Evd.empty ind dep sort

let build_induction_scheme_in_type dep sort ind =
  build_induction_scheme (Global.env()) Evd.empty ind dep sort

let rect_scheme_kind_from_prop =
  declare_individual_scheme_object "_rect" ~aux:"_rect_from_prop"
    (build_induction_scheme_in_type false InType)

let rect_dep_scheme_kind_from_type =
  declare_individual_scheme_object "_rect" ~aux:"_rect_from_type"
    (build_induction_scheme_in_type true InType)

let ind_scheme_kind_from_prop =
  declare_individual_scheme_object "_ind" ~aux:"_ind_from_prop"
  (optimize_non_type_induction_scheme rect_scheme_kind_from_prop false InProp)

let ind_dep_scheme_kind_from_type =
  declare_individual_scheme_object "_ind" ~aux:"_ind_from_type"
  (optimize_non_type_induction_scheme rect_dep_scheme_kind_from_type true InProp)

let rec_scheme_kind_from_prop =
  declare_individual_scheme_object "_rec" ~aux:"_rec_from_prop"
  (optimize_non_type_induction_scheme rect_scheme_kind_from_prop false InSet)

let rec_dep_scheme_kind_from_type =
  declare_individual_scheme_object "_rec" ~aux:"_rec_from_type"
  (optimize_non_type_induction_scheme rect_dep_scheme_kind_from_type true InSet)

(* Case analysis *)

let build_case_analysis_scheme_in_type dep sort ind =
  build_case_analysis_scheme (Global.env()) Evd.empty ind dep sort

let case_scheme_kind_from_type =
  declare_individual_scheme_object "_case_nodep"
  (build_case_analysis_scheme_in_type false InType)

let case_scheme_kind_from_prop =
  declare_individual_scheme_object "_case" ~aux:"_case_from_prop"
  (build_case_analysis_scheme_in_type false InType)

let case_dep_scheme_kind_from_type =
  declare_individual_scheme_object "_case" ~aux:"_case_from_type"
  (build_case_analysis_scheme_in_type true InType)

let case_dep_scheme_kind_from_type_in_prop =
  declare_individual_scheme_object "_casep_dep"
  (build_case_analysis_scheme_in_type true InProp)

let case_dep_scheme_kind_from_prop =
  declare_individual_scheme_object "_case_dep"
  (build_case_analysis_scheme_in_type true InType)

let case_dep_scheme_kind_from_prop_in_prop =
  declare_individual_scheme_object "_casep"
  (build_case_analysis_scheme_in_type true InProp)
