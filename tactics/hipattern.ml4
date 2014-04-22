(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma grammar/q_constr.cmo" i*)

open Pp
open Errors
open Util
open Names
open Term
open Termops
open Inductiveops
open ConstrMatching
open Coqlib
open Declarations
open Tacmach.New

(* I implemented the following functions which test whether a term t
   is an inductive but non-recursive type, a general conjuction, a
   general disjunction, or a type with no constructors.

   They are more general than matching with or_term, and_term, etc,
   since they do not depend on the name of the type. Hence, they
   also work on ad-hoc disjunctions introduced by the user.

  -- Eduardo (6/8/97). *)

type 'a matching_function = constr -> 'a option

type testing_function  = constr -> bool

let mkmeta n = Nameops.make_ident "X" (Some n)
let meta1 = mkmeta 1
let meta2 = mkmeta 2
let meta3 = mkmeta 3
let meta4 = mkmeta 4

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

(* Test dependencies *)

(* NB: we consider also the let-in case in the following function,
   since they may appear in types of inductive constructors (see #2629) *)

let rec has_nodep_prod_after n c =
  match kind_of_term c with
    | Prod (_,_,b) | LetIn (_,_,_,b) ->
	( n>0 || not (dependent (mkRel 1) b))
	&& (has_nodep_prod_after (n-1) b)
    | _            -> true

let has_nodep_prod = has_nodep_prod_after 0

(* A general conjunctive type is a non-recursive with-no-indices inductive
   type with only one constructor and no dependencies between argument;
   it is strict if it has the form
   "Inductive I A1 ... An := C (_:A1) ... (_:An)" *)

(* style: None = record; Some false = conjunction; Some true = strict conj *)

let is_strict_conjunction = function
| Some true -> true
| _ -> false

let is_lax_conjunction = function
| Some false -> true
| _ -> false

let match_with_one_constructor style onlybinary allow_rec t =
  let (hdapp,args) = decompose_app t in
  let res = match kind_of_term hdapp with
  | Ind ind ->
      let (mib,mip) = Global.lookup_inductive ind in
      if Int.equal (Array.length mip.mind_consnames) 1
	&& (allow_rec || not (mis_is_recursive (ind,mib,mip)))
        && (Int.equal mip.mind_nrealargs 0)
      then
	if is_strict_conjunction style (* strict conjunction *) then
	  let ctx =
	    (prod_assum (snd
	      (decompose_prod_n_assum mib.mind_nparams mip.mind_nf_lc.(0)))) in
	  if
	    List.for_all
	      (fun (_,b,c) -> Option.is_empty b && isRel c && Int.equal (destRel c) mib.mind_nparams) ctx
	  then
	    Some (hdapp,args)
	  else None
	else
	  let ctyp = prod_applist mip.mind_nf_lc.(0) args in
	  let cargs = List.map pi3 ((prod_assum ctyp)) in
	  if not (is_lax_conjunction style) || has_nodep_prod ctyp then
	    (* Record or non strict conjunction *)
	    Some (hdapp,List.rev cargs)
	  else
	      None
      else
	None
  | _ -> None in
  match res with
  | Some (hdapp, args) when not onlybinary -> res
  | Some (hdapp, [_; _]) -> res
  | _ -> None

let match_with_conjunction ?(strict=false) ?(onlybinary=false) t =
  match_with_one_constructor (Some strict) onlybinary false t

let match_with_record t =
  match_with_one_constructor None false false t

let is_conjunction ?(strict=false) ?(onlybinary=false) t =
  op2bool (match_with_conjunction ~strict ~onlybinary t)

let is_record t =
  op2bool (match_with_record t)

let match_with_tuple t =
  let t = match_with_one_constructor None false true t in
  Option.map (fun (hd,l) ->
    let ind = destInd hd in
    let (mib,mip) = Global.lookup_inductive ind in
    let isrec = mis_is_recursive (ind,mib,mip) in
    (hd,l,isrec)) t

let is_tuple t =
  op2bool (match_with_tuple t)

(* A general disjunction type is a non-recursive with-no-indices inductive
   type with of which all constructors have a single argument;
   it is strict if it has the form
   "Inductive I A1 ... An := C1 (_:A1) | ... | Cn : (_:An)" *)

let test_strict_disjunction n lc =
  Array.for_all_i (fun i c ->
    match (prod_assum (snd (decompose_prod_n_assum n c))) with
    | [_,None,c] -> isRel c && Int.equal (destRel c) (n - i)
    | _ -> false) 0 lc

let match_with_disjunction ?(strict=false) ?(onlybinary=false) t =
  let (hdapp,args) = decompose_app t in
  let res = match kind_of_term hdapp with
  | Ind ind  ->
      let car = mis_constr_nargs ind in
      let (mib,mip) = Global.lookup_inductive ind in
      if Array.for_all (fun ar -> Int.equal ar 1) car
	&& not (mis_is_recursive (ind,mib,mip))
        && (Int.equal mip.mind_nrealargs 0)
      then
	if strict then
	  if test_strict_disjunction mib.mind_nparams mip.mind_nf_lc then
	    Some (hdapp,args)
	  else
	    None
	else
	  let cargs =
	    Array.map (fun ar -> pi2 (destProd (prod_applist ar args)))
	      mip.mind_nf_lc in
	  Some (hdapp,Array.to_list cargs)
      else
	None
  | _ -> None in
  match res with
  | Some (hdapp,args) when not onlybinary -> res
  | Some (hdapp,[_; _]) -> res
  | _ -> None

let is_disjunction ?(strict=false) ?(onlybinary=false) t =
  op2bool (match_with_disjunction ~strict ~onlybinary t)

(* An empty type is an inductive type, possible with indices, that has no
   constructors *)

let match_with_empty_type t =
  let (hdapp,args) = decompose_app t in
  match (kind_of_term hdapp) with
    | Ind ind ->
        let (mib,mip) = Global.lookup_inductive ind in
        let nconstr = Array.length mip.mind_consnames in
	if Int.equal nconstr 0 then Some hdapp else None
    | _ ->  None

let is_empty_type t = op2bool (match_with_empty_type t)

(* This filters inductive types with one constructor with no arguments;
   Parameters and indices are allowed *)

let match_with_unit_or_eq_type t =
  let (hdapp,args) = decompose_app t in
  match (kind_of_term hdapp) with
    | Ind ind  ->
        let (mib,mip) = Global.lookup_inductive ind in
        let constr_types = mip.mind_nf_lc in
        let nconstr = Array.length mip.mind_consnames in
        let zero_args c = Int.equal (nb_prod c) mib.mind_nparams in
	if Int.equal nconstr 1 && zero_args constr_types.(0) then
	  Some hdapp
	else
	  None
    | _ -> None

let is_unit_or_eq_type t = op2bool (match_with_unit_or_eq_type t)

(* A unit type is an inductive type with no indices but possibly
   (useless) parameters, and that has no arguments in its unique
   constructor *)

let is_unit_type t =
  match match_with_conjunction t with
  | Some (_,[]) -> true
  | _ -> false

(* Checks if a given term is an application of an
   inductive binary relation R, so that R has only one constructor
   establishing its reflexivity.  *)

type equation_kind =
  | MonomorphicLeibnizEq of constr * constr
  | PolymorphicLeibnizEq of constr * constr * constr
  | HeterogenousEq of constr * constr * constr * constr

exception NoEquationFound

let coq_refl_leibniz1_pattern = PATTERN [ forall x:_, _ x x ]
let coq_refl_leibniz2_pattern = PATTERN [ forall A:_, forall x:A, _ A x x ]
let coq_refl_jm_pattern       = PATTERN [ forall A:_, forall x:A, _ A x A x ]

open Globnames

let match_with_equation t =
  if not (isApp t) then raise NoEquationFound;
  let (hdapp,args) = destApp t in
  match kind_of_term hdapp with
  | Ind ind ->
      if eq_gr (IndRef ind) glob_eq then
	Some (build_coq_eq_data()),hdapp,
	PolymorphicLeibnizEq(args.(0),args.(1),args.(2))
      else if eq_gr (IndRef ind) glob_identity then
	Some (build_coq_identity_data()),hdapp,
	PolymorphicLeibnizEq(args.(0),args.(1),args.(2))
      else if eq_gr (IndRef ind) glob_jmeq then
	Some (build_coq_jmeq_data()),hdapp,
	HeterogenousEq(args.(0),args.(1),args.(2),args.(3))
      else
        let (mib,mip) = Global.lookup_inductive ind in
        let constr_types = mip.mind_nf_lc in
        let nconstr = Array.length mip.mind_consnames in
	if Int.equal nconstr 1 then
          if is_matching coq_refl_leibniz1_pattern constr_types.(0) then
	    None, hdapp, MonomorphicLeibnizEq(args.(0),args.(1))
	  else if is_matching coq_refl_leibniz2_pattern constr_types.(0) then
	    None, hdapp, PolymorphicLeibnizEq(args.(0),args.(1),args.(2))
	  else if is_matching coq_refl_jm_pattern constr_types.(0) then
	    None, hdapp, HeterogenousEq(args.(0),args.(1),args.(2),args.(3))
	  else raise NoEquationFound
        else raise NoEquationFound
    | _ -> raise NoEquationFound

let is_inductive_equality ind =
  let (mib,mip) = Global.lookup_inductive ind in
  let nconstr = Array.length mip.mind_consnames in
  Int.equal nconstr 1 && Int.equal (constructor_nrealargs (Global.env()) (ind,1)) 0

let match_with_equality_type t =
  let (hdapp,args) = decompose_app t in
  match (kind_of_term hdapp) with
  | Ind ind when is_inductive_equality ind -> Some (hdapp,args)
  | _ -> None

let is_equality_type t = op2bool (match_with_equality_type t)

let coq_arrow_pattern = PATTERN [ ?X1 -> ?X2 ]

let match_arrow_pattern t =
  let result = matches coq_arrow_pattern t in
  match Id.Map.bindings result with
    | [(m1,arg);(m2,mind)] ->
      assert (Id.equal m1 meta1 && Id.equal m2 meta2); (arg, mind)
    | _ -> anomaly (Pp.str "Incorrect pattern matching")

let match_with_nottype t =
  try
    let (arg,mind) = match_arrow_pattern t in
    if is_empty_type mind then Some (mind,arg) else None
  with PatternMatchingFailure -> None

let is_nottype t = op2bool (match_with_nottype t)

let match_with_forall_term c=
  match kind_of_term c with
    | Prod (nam,a,b) -> Some (nam,a,b)
    | _            -> None

let is_forall_term c = op2bool (match_with_forall_term c)

let match_with_imp_term c=
  match kind_of_term c with
    | Prod (_,a,b) when not (dependent (mkRel 1) b) ->Some (a,b)
    | _              -> None

let is_imp_term c = op2bool (match_with_imp_term c)

let match_with_nodep_ind t =
  let (hdapp,args) = decompose_app t in
    match (kind_of_term hdapp) with
      | Ind ind  ->
          let (mib,mip) = Global.lookup_inductive ind in
	    if Array.length (mib.mind_packets)>1 then None else
	      let nodep_constr = has_nodep_prod_after mib.mind_nparams in
		if Array.for_all nodep_constr mip.mind_nf_lc then
		  let params=
		    if Int.equal mip.mind_nrealargs 0 then args else
		      fst (List.chop mib.mind_nparams args) in
		    Some (hdapp,params,mip.mind_nrealargs)
		else
		  None
      | _ -> None

let is_nodep_ind t=op2bool (match_with_nodep_ind t)

let match_with_sigma_type t=
  let (hdapp,args) = decompose_app t in
  match (kind_of_term hdapp) with
    | Ind ind  ->
        let (mib,mip) = Global.lookup_inductive ind in
          if Int.equal (Array.length (mib.mind_packets)) 1 &&
	    (Int.equal mip.mind_nrealargs 0) &&
	    (Int.equal (Array.length mip.mind_consnames)1) &&
	    has_nodep_prod_after (mib.mind_nparams+1) mip.mind_nf_lc.(0) then
	      (*allowing only 1 existential*)
	      Some (hdapp,args)
	  else
	    None
    | _ -> None

let is_sigma_type t=op2bool (match_with_sigma_type t)

(***** Destructing patterns bound to some theory *)

let rec first_match matcher = function
  | [] -> raise PatternMatchingFailure
  | (pat,check,build_set)::l when check () ->
      (try (build_set (),matcher pat)
       with PatternMatchingFailure -> first_match matcher l)
  | _::l -> first_match matcher l

(*** Equality *)

(* Patterns "(eq ?1 ?2 ?3)" and "(identity ?1 ?2 ?3)" *)
let coq_eq_pattern_gen eq = lazy PATTERN [ %eq ?X1 ?X2 ?X3 ]
let coq_eq_pattern = coq_eq_pattern_gen coq_eq_ref
let coq_identity_pattern = coq_eq_pattern_gen coq_identity_ref
let coq_jmeq_pattern = lazy PATTERN [ %coq_jmeq_ref ?X1 ?X2 ?X3 ?X4 ]

let match_eq eqn eq_pat =
  let pat =
    try Lazy.force eq_pat
    with e when Errors.noncritical e -> raise PatternMatchingFailure
  in
  match Id.Map.bindings (matches pat eqn) with
    | [(m1,t);(m2,x);(m3,y)] ->
	assert (Id.equal m1 meta1 && Id.equal m2 meta2 && Id.equal m3 meta3);
	PolymorphicLeibnizEq (t,x,y)
    | [(m1,t);(m2,x);(m3,t');(m4,x')] ->
        assert (Id.equal m1 meta1 && Id.equal m2 meta2 && Id.equal m3 meta3 && Id.equal m4 meta4);
	HeterogenousEq (t,x,t',x')
    | _ -> anomaly ~label:"match_eq" (Pp.str "an eq pattern should match 3 or 4 terms")

let no_check () = true
let check_jmeq_loaded () = Library.library_is_loaded Coqlib.jmeq_module

let equalities =
  [coq_eq_pattern, no_check, build_coq_eq_data;
   coq_jmeq_pattern, check_jmeq_loaded, build_coq_jmeq_data;
   coq_identity_pattern, no_check, build_coq_identity_data]

let find_eq_data eqn = (* fails with PatternMatchingFailure *)
  first_match (match_eq eqn) equalities

let extract_eq_args gl = function
  | MonomorphicLeibnizEq (e1,e2) ->
      let t = pf_type_of gl e1 in (t,e1,e2)
  | PolymorphicLeibnizEq (t,e1,e2) -> (t,e1,e2)
  | HeterogenousEq (t1,e1,t2,e2) ->
      if pf_conv_x gl t1 t2 then (t1,e1,e2)
      else raise PatternMatchingFailure

let find_eq_data_decompose gl eqn =
  let (lbeq,eq_args) = find_eq_data eqn in
  (lbeq,extract_eq_args gl eq_args)

let find_this_eq_data_decompose gl eqn =
  let (lbeq,eq_args) =
    try (*first_match (match_eq eqn) inversible_equalities*)
      find_eq_data eqn
    with PatternMatchingFailure ->
      errorlabstrm "" (str "No primitive equality found.") in
  let eq_args =
    try extract_eq_args gl eq_args
    with PatternMatchingFailure ->
      error "Don't know what to do with JMeq on arguments not of same type." in
  (lbeq,eq_args)

let match_eq_nf gls eqn eq_pat =
  match Id.Map.bindings (pf_matches gls (Lazy.force eq_pat) eqn) with
    | [(m1,t);(m2,x);(m3,y)] ->
        assert (Id.equal m1 meta1 && Id.equal m2 meta2 && Id.equal m3 meta3);
	(t,pf_whd_betadeltaiota gls x,pf_whd_betadeltaiota gls y)
    | _ -> anomaly ~label:"match_eq" (Pp.str "an eq pattern should match 3 terms")

let dest_nf_eq gls eqn =
  try
    snd (first_match (match_eq_nf gls eqn) equalities)
  with PatternMatchingFailure ->
    error "Not an equality."

(*** Sigma-types *)

(* Patterns "(existS ?1 ?2 ?3 ?4)" and "(existT ?1 ?2 ?3 ?4)" *)
let coq_ex_pattern_gen ex = lazy PATTERN [ %ex ?X1 ?X2 ?X3 ?X4 ]
let coq_existT_pattern = coq_ex_pattern_gen coq_existT_ref
let coq_exist_pattern = coq_ex_pattern_gen coq_exist_ref

let match_sigma ex ex_pat =
  match Id.Map.bindings (matches (Lazy.force ex_pat) ex) with
    | [(m1,a);(m2,p);(m3,car);(m4,cdr)] ->
        assert (Id.equal m1 meta1 && Id.equal m2 meta2 && Id.equal m3 meta3 && Id.equal m4 meta4);
	(a,p,car,cdr)
    | _ ->
	anomaly ~label:"match_sigma" (Pp.str "a successful sigma pattern should match 4 terms")

let find_sigma_data_decompose ex = (* fails with PatternMatchingFailure *)
  first_match (match_sigma ex)
    [coq_existT_pattern, no_check, build_sigma_type;
     coq_exist_pattern, no_check, build_sigma]

(* Pattern "(sig ?1 ?2)" *)
let coq_sig_pattern = lazy PATTERN [ %coq_sig_ref ?X1 ?X2 ]

let match_sigma t =
  match Id.Map.bindings (matches (Lazy.force coq_sig_pattern) t) with
    | [(_,a); (_,p)] -> (a,p)
    | _ -> anomaly (Pp.str "Unexpected pattern")

let is_matching_sigma t = is_matching (Lazy.force coq_sig_pattern) t

(*** Decidable equalities *)

(* The expected form of the goal for the tactic Decide Equality *)

(* Pattern "{<?1>x=y}+{~(<?1>x=y)}" *)
(* i.e. "(sumbool (eq ?1 x y) ~(eq ?1 x y))" *)

let coq_eqdec_inf_pattern =
 lazy PATTERN [ { ?X2 = ?X3 :> ?X1 } + { ~ ?X2 = ?X3 :> ?X1 } ]

let coq_eqdec_inf_rev_pattern =
 lazy PATTERN [ { ~ ?X2 = ?X3 :> ?X1 } + { ?X2 = ?X3 :> ?X1 } ]

let coq_eqdec_pattern =
 lazy PATTERN [ %coq_or_ref (?X2 = ?X3 :> ?X1) (~ ?X2 = ?X3 :> ?X1) ]

let coq_eqdec_rev_pattern =
 lazy PATTERN [ %coq_or_ref (~ ?X2 = ?X3 :> ?X1) (?X2 = ?X3 :> ?X1) ]

let op_or = coq_or_ref
let op_sum = coq_sumbool_ref

let match_eqdec t =
  let eqonleft,op,subst =
    try true,op_sum,matches (Lazy.force coq_eqdec_inf_pattern) t
    with PatternMatchingFailure ->
    try false,op_sum,matches (Lazy.force coq_eqdec_inf_rev_pattern) t
    with PatternMatchingFailure ->
    try true,op_or,matches (Lazy.force coq_eqdec_pattern) t
    with PatternMatchingFailure ->
        false,op_or,matches (Lazy.force coq_eqdec_rev_pattern) t in
  match Id.Map.bindings subst with
  | [(_,typ);(_,c1);(_,c2)] ->
      eqonleft, Globnames.constr_of_global (Lazy.force op), c1, c2, typ
  | _ -> anomaly (Pp.str "Unexpected pattern")

(* Patterns "~ ?" and "? -> False" *)
let coq_not_pattern = lazy PATTERN [ ~ _ ]
let coq_imp_False_pattern = lazy PATTERN [ _ -> %coq_False_ref ]

let is_matching_not t = is_matching (Lazy.force coq_not_pattern) t
let is_matching_imp_False t = is_matching (Lazy.force coq_imp_False_pattern) t

(* Remark: patterns that have references to the standard library must
   be evaluated lazily (i.e. at the time they are used, not a the time
   coqtop starts) *)
