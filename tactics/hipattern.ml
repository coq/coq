
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Term
open Reduction
open Evd
open Environ
open Proof_trees
open Stock
open Clenv
open Pattern

(* The pattern table for tactics. *)

(* Description: see the interface. *)

(* First part : introduction of term patterns *)

type module_mark = Stock.module_mark

let parse_constr s =
  try 
    Pcoq.parse_string Pcoq.Constr.constr_eoi s 
  with Stdpp.Exc_located (_ , (Stream.Failure | Stream.Error _)) ->
    error "Syntax error : not a construction" 

(* Patterns *)
let parse_pattern s =
  Astterm.interp_constrpattern Evd.empty (Global.env()) (parse_constr s)
    
type marked_pattern = (int list * constr_pattern) Stock.stocked

let (pattern_stock : (int list * constr_pattern) Stock.stock) =
  Stock.make_stock { name = "PATTERN"; proc = parse_pattern }

let put_pat = Stock.stock pattern_stock
let get_pat tm = snd (Stock.retrieve pattern_stock tm)

let make_module_marker = Stock.make_module_marker

(* Squeletons *)
let parse_squeleton s =
  let c = Astterm.interp_constr Evd.empty (Global.env()) (parse_constr s) in
  (collect_metas c, c)

type marked_term = (int list * constr) Stock.stocked

let (squeleton_stock : (int list * constr) Stock.stock) =
  Stock.make_stock { name = "SQUELETON"; proc = parse_squeleton }

let put_squel = Stock.stock squeleton_stock
let get_squel_core = Stock.retrieve squeleton_stock

(*
let dest_somatch n pat =
  let _,m = get_pat pat in
  matches m n

let somatches n pat =
  let _,m = get_pat pat in
  is_matching m n

let dest_somatch_conv env sigma n pat =
  let _,m = get_pat pat in
  matches_conv env sigma m n

let somatches_conv env sigma n pat =
  let _,m = get_pat pat in
  is_matching_conv env sigma m n
*)
let soinstance squel arglist =
  let mvs,c = get_squel_core squel in
  let mvb = List.combine mvs arglist in 
  Sosub.soexecute (Reduction.strong (fun _ _ -> Reduction.whd_meta mvb) 
		     empty_env Evd.empty c)

let get_squel m =
  let mvs, c = get_squel_core m in
  if mvs = [] then c
  else errorlabstrm "get_squel"
    [< Printer.prterm c;
       'sPC; 'sTR "is not a closed squeleton, use 'soinstance'" >]

(* I implemented the following functions which test whether a term t
   is an inductive but non-recursive type, a general conjuction, a
   general disjunction, or a type with no constructors.

   They are more general than matching with or_term, and_term, etc, 
   since they do not depend on the name of the type. Hence, they 
   also work on ad-hoc disjunctions introduced by the user.
  
  -- Eduardo (6/8/97). *)

let mmk = make_module_marker ["Prelude"]

type 'a matching_function = constr -> 'a option

type testing_function  = constr -> bool

let op2bool = function Some _ -> true | None -> false

let match_with_non_recursive_type t = 
  match kind_of_term t with 
    | IsAppL _ -> 
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
        let nconstr = Global.mind_nconstr ind in  
	if (nconstr = 1) && 
          (not (Global.mind_is_recursive ind)) &&
          (nb_prod (Global.mind_arity ind)) = (Global.mind_nparams ind)
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
        let constr_types = 
	  Global.mind_lc_without_abstractions ind in
        let only_one_arg c = 
	  ((nb_prod c) - (Global.mind_nparams ind)) = 1 in 
	if (array_for_all only_one_arg constr_types) &&
          (not (Global.mind_is_recursive ind))
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
        let constr_types = 
	  Global.mind_lc_without_abstractions ind in 
        let nconstr = Global.mind_nconstr ind in
        let zero_args c = ((nb_prod c) - (Global.mind_nparams ind)) = 0 in  
	if nconstr = 1 && (array_for_all zero_args constr_types) then 
	  Some hdapp
        else 
	  None
    | _ -> None

let is_unit_type t = op2bool (match_with_unit_type t)


(* Checks if a given term is an application of an
   inductive binary relation R, so that R has only one constructor
   stablishing its reflexivity.  *)

let refl_rel_pat1 = put_pat mmk "(A : ?)(x:A)(? A x x)"
let refl_rel_pat2 = put_pat mmk "(x : ?)(? x x)"

let match_with_equation  t =
  let (hdapp,args) = decomp_app t in
  match (kind_of_term hdapp) with
    | IsMutInd ind -> 
        let constr_types = Global.mind_lc_without_abstractions ind in 
        let nconstr = Global.mind_nconstr ind in
	if nconstr = 1 &&
           (is_matching (get_pat refl_rel_pat1) constr_types.(0) ||
            is_matching (get_pat refl_rel_pat2) constr_types.(0)) 
        then 
	  Some (hdapp,args)
        else 
	  None
    | _ -> None

let is_equation t = op2bool (match_with_equation  t)

let arrow_pat = put_pat mmk "(?1 -> ?2)"

let match_with_nottype t =
  try
    match matches (get_pat arrow_pat) t with
      |	[(1,arg);(2,mind)] ->
	  if is_empty_type mind then Some (mind,arg) else None
      | _ -> anomaly "Incorrect pattern matching" 
  with PatternMatchingFailure -> None  

let is_nottype t = op2bool (match_with_nottype t)
		     
let is_imp_term = function
  | DOP2(Prod,_,DLAM(_,b)) -> not (dependent (Rel 1) b)
  | _                      -> false



