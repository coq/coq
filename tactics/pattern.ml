
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
open Rawterm

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
let get_pat = Stock.retrieve pattern_stock

let make_module_marker = Stock.make_module_marker

(* Squeletons *)
let parse_squeleton s =
  Astterm.interp_constr Evd.empty (Global.env()) (parse_constr s)

type marked_term = constr Stock.stocked

let (squeleton_stock : constr Stock.stock) =
  Stock.make_stock { name = "SQUELETON"; proc = parse_squeleton }

let put_squel = Stock.stock squeleton_stock
let get_squel = Stock.retrieve squeleton_stock

(* Second part : Given a term with second-order variables in it,
   represented by Meta's, and possibly applied using XTRA[$SOAPP] to
   terms, this function will perform second-order, binding-preserving,
   matching, in the case where the pattern is a pattern in the sense
   of Dale Miller.

   ALGORITHM:

   Given a pattern, we decompose it, flattening Cast's and apply's,
   recursing on all operators, and pushing the name of the binder each
   time we descend a binder.

   When we reach a first-order variable, we ask that the corresponding
   term's free-rels all be higher than the depth of the current stack.

   When we reach a second-order application, we ask that the
   intersection of the free-rels of the term and the current stack be
   contained in the arguments of the application, and in that case, we
   construct a DLAM with the names on the stack.

 *)

let dest_soapp_operator = function
  | DOPN(XTRA("$SOAPP"),v) ->
      (match Array.to_list v with
	 | (DOP0(Meta n))::l ->
             let l' = 
	       List.map (function (Rel i) -> i | _ -> error "somatch") l in
             Some (n, list_uniquize l')
	 | _ -> error "somatch")
  | (DOP2(XTRA("$SOAPP"),DOP0(Meta n),Rel p)) ->
      Some (n,list_uniquize [p])
  | _ -> None

let constrain ((n : int),(m : constr)) sigma =
  if List.mem_assoc n sigma then
    if eq_constr m (List.assoc n sigma) then sigma else error "somatch"
  else 
    (n,m)::sigma
    
let build_dlam toabstract stk (m : constr) = 
  let rec buildrec m p_0 p_1 = match p_0,p_1 with 
    | (_, []) -> m
    | (n, (na::tl)) -> 
	if List.mem n toabstract then
          buildrec (DLAM(na,m)) (n+1) tl
        else 
	  buildrec (pop m) (n+1) tl
  in 
  buildrec m 1 stk

let memb_metavars m n =
  match (m,n) with
    | (None, _)     -> true
    | (Some mvs, n) -> List.mem n mvs

exception PatternMatchingFailure

let somatch metavars = 
  let rec sorec stk sigma p t =
    let cT = whd_castapp t in
    match p,kind_of_term cT with
      | PSoApp (n,relargs),m ->
          assert (memb_metavars metavars n);
	  let frels = Intset.elements (free_rels cT) in
	  if list_subset frels relargs then
	    constrain (n,build_dlam relargs stk cT) sigma
	  else
	    raise PatternMatchingFailure

      | PMeta n, m ->
	  if not (memb_metavars metavars n) then
	  (*Ce cas est bizarre : comment les numéros pourraient-ils coincider*)
	    match m with
	      | IsMeta m0 when n=m0 -> sigma
	      | _ -> raise PatternMatchingFailure
	  else
	    let depth = List.length stk in
	    let frels = Intset.elements (free_rels cT) in
            if List.for_all (fun i -> i > depth) frels then
	      constrain (n,lift (-depth) cT) sigma
            else 
	      raise PatternMatchingFailure

      | PRef (RVar v1), IsVar v2 when v1 = v2 -> sigma

      | PRef (RConst (sp1,ctxt1)), IsConst (sp2,ctxt2) 
	  when sp1 = sp2 && Array.length ctxt1 = Array.length ctxt2 ->
	  array_fold_left2 (sorec stk) sigma ctxt1 ctxt2

      | PRef (RInd (sp1,ctxt1)), IsMutInd (sp2,ctxt2) 
	  when sp1 = sp2 && Array.length ctxt1 = Array.length ctxt2 ->
	  array_fold_left2 (sorec stk) sigma ctxt1 ctxt2

      | PRef (RConstruct (sp1,ctxt1)), IsMutConstruct (sp2,ctxt2) 
	  when sp1 = sp2 && Array.length ctxt1 = Array.length ctxt2 ->
	  array_fold_left2 (sorec stk) sigma ctxt1 ctxt2

      | PRel n1, IsRel n2 when n1 = n2 -> sigma

      | PSort (RProp c1), IsSort (Prop c2) when c1 = c2 -> sigma

      | PSort RType, IsSort (Type _) -> sigma

      | PApp (c1,arg1), IsAppL (c2,arg2) ->
	  array_fold_left2 (sorec stk) (sorec stk sigma c1 c2)
	    arg1 (Array.of_list arg2)

      | PBinder(BProd,na1,c1,d1), IsProd(na2,c2,d2) ->
	  sorec (na2::stk) (sorec stk sigma c1 c2) d1 d2

      | PBinder(BLambda,na1,c1,d1), IsLambda(na2,c2,d2) ->
	  sorec (na2::stk) (sorec stk sigma c1 c2) d1 d2

      | _, (IsFix _ | IsMutCase _ | IsCoFix _) ->
	  error "somatch: not implemented"

      | _ -> raise PatternMatchingFailure

    in 
    sorec [] []
(*
let somatch metavars = 
  let rec sorec stk sigma p t =
    let cP = whd_castapp p 
    and cT = whd_castapp t in
    match dest_soapp_operator cP with
      | Some (n,ok_args) ->
          if not (memb_metavars metavars n) then error "somatch";
	  let frels = Intset.elements (free_rels cT) in
	  if list_subset frels ok_args then 
	    constrain (n,build_dlam ok_args stk cT) sigma
	  else 
	    error "somatch"

      | None ->
	  match (cP,cT) with
       	    | (DOP0(Meta n),m) ->
		if not (memb_metavars metavars n) then
		  match m with
		    | DOP0(Meta m_0) -> 
			if n=m_0 then sigma else error "somatch"
		    | _ -> error "somatch"
		else
		  let depth = List.length stk in
		  let frels = Intset.elements (free_rels m) in
        	  if List.for_all (fun i -> i > depth) frels then
		    constrain (n,lift (-depth) m) sigma
        	  else 
		    error "somatch"

  	    | (VAR v1,VAR v2) ->
		if v1 = v2 then sigma else error "somatch"
		  
  	    | (Rel n1,Rel n2) ->
		if n1 = n2 then sigma else error "somatch"

  	    | (DOP0 op1,DOP0 op2) ->
		if op1 = op2 then sigma else error "somatch"

  	    | (DOP1(op1,c1), DOP1(op2,c2)) ->
		if op1 = op2 then sorec stk sigma c1 c2	else error "somatch"
	       
  	    | (DOP2(op1,c1,d1), DOP2(op2,c2,d2)) ->
		if op1 = op2 then
		  sorec stk (sorec stk sigma c1 c2) d1 d2
		else 
		  error "somatch"
	       
  	    | (DOPN(op1,cl1), DOPN(op2,cl2)) ->
		if op1 = op2 & Array.length cl1 = Array.length cl2 then
		  array_fold_left2 (sorec stk) sigma cl1 cl2
		else 
		  error "somatch"

  	    | (DOPL(op1,cl1), DOPL(op2,cl2)) ->
		if op1 = op2 & List.length cl1 = List.length cl2 then
		  List.fold_left2 (sorec stk) sigma cl1 cl2
		else 
		  error "somatch"

  	    | (DLAM(_,c1), DLAM(na,c2)) -> 
		sorec (na::stk) sigma c1 c2
		  
  	    | (DLAMV(_,cl1), DLAMV(na,cl2)) ->
		if Array.length cl1 = Array.length cl2 then
		  array_fold_left2 (sorec (na::stk)) sigma cl1 cl2
		else 
		  error "somatch"
		    
  	    | _ -> error "somatch"
    in 
    sorec [] []
*)
let somatches n pat =
  let (_,m) = get_pat pat in 
  try 
    let _ = somatch None m n in true 
  with e when Logic.catchable_exception e -> 
    false

let dest_somatch n pat =
  let mvs,m = get_pat pat in
  let mvb = somatch (Some (list_uniquize mvs)) m n in
  List.map (fun b -> List.assoc b mvb) mvs

let newsomatch n pat = let _,m = get_pat pat in somatch None m n

let soinstance squel arglist =
  let c = get_squel squel in
  let mvs = collect_metas c in
  let mvb = List.combine mvs arglist in 
  Sosub.soexecute (Reduction.strong (fun _ _ -> Reduction.whd_meta mvb) 
		     empty_env Evd.empty c)

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
           (somatches constr_types.(0) refl_rel_pat1 ||
            somatches constr_types.(0) refl_rel_pat2) 
        then 
	  Some (hdapp,args)
        else 
	  None
    | _ -> None

let is_equation t = op2bool (match_with_equation  t)

let match_with_nottype t =
  let notpat = put_pat mmk "(?1 -> ?2)" in 
  try 
    (match dest_somatch t notpat with
       | [arg;mind] when is_empty_type mind -> Some (mind,arg)
       | [arg;mind] -> None
       | _ -> anomaly "match_with_nottype")
  with UserError ("somatches",_) -> 
    None  

let is_nottype t = op2bool (match_with_nottype t)
		     
let is_imp_term = function
  | DOP2(Prod,_,DLAM(_,b)) -> not (dependent (Rel 1) b)
  | _                      -> false

let rec pattern_of_constr t =
  match kind_of_term t with
    | IsRel n  -> PRel n
    | IsMeta n -> PMeta n
    | IsVar id -> PRef (RVar id)
    | IsSort (Prop c) -> PSort (RProp c)
    | IsSort (Type _) -> PSort RType
    | IsCast (c,t)      -> pattern_of_constr c
    | IsProd (na,c,b)   ->
	PBinder (BProd,na,pattern_of_constr c,pattern_of_constr b)
    | IsLambda (na,c,b) ->
	PBinder (BLambda,na,pattern_of_constr c,pattern_of_constr b)
    | IsAppL (f,args)   ->
	PApp (pattern_of_constr f,
	      Array.of_list (List.map pattern_of_constr args))
    | IsConst (cst_sp,ctxt)         ->
	PRef (RConst (cst_sp,Array.map pattern_of_constr ctxt))
    | IsMutInd (ind_sp,ctxt)        ->
	PRef (RInd (ind_sp,Array.map pattern_of_constr ctxt))
    | IsMutConstruct (cstr_sp,ctxt) ->
	PRef (RConstruct (cstr_sp,Array.map pattern_of_constr ctxt))
    | IsMutCase _ | IsFix _ | IsCoFix _ ->
	error "pattern_of_constr: destructors currently not supported"
    | IsEvar _ -> error "pattern_of_constr: an existential variable remains"
    | IsAbst _ | IsXtra _   -> anomaly "No longer supported"


