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
open Univ
open Term
open Inductive
open Environ
open Reduction
open Instantiate
open Typeops
open Typing
open Retyping
open Tacmach
open Proof_type
open Logic
open Wcclausenv
open Pattern
open Hipattern
open Tacticals
open Tactics
open Tacinterp
open Tacred
open Vernacinterp
open Coqlib

(* Rewriting tactics *)

(* Warning : rewriting from left to right only works
   if there exists in the context a theorem named <eqname>_<suffsort>_r
   with type (A:<sort>)(x:A)(P:A->Prop)(P x)->(y:A)(eqname A y x)->(P y).
   If another equality myeq is introduced, then corresponding theorems
   myeq_ind_r, myeq_rec_r and myeq_rect_r have to be proven. See below.
   -- Eduardo (19/8/97
*)

let general_rewrite_bindings lft2rgt (c,l) gl =
  let ctype = pf_type_of gl c in 
  let env = pf_env gl in
  let sigma = project gl in 
  let _,t = splay_prod env sigma ctype in
  match match_with_equation t with
    | None -> error "The term provided does not end with an equation" 
    | Some (hdcncl,_) -> 
        let hdcncls = string_head hdcncl in 
	let suffix = Declare.elimination_suffix (sort_of_goal gl) in
        let elim =
	  if lft2rgt then
            pf_global gl (id_of_string (hdcncls^suffix^"_r"))
          else
	    pf_global gl (id_of_string (hdcncls^suffix))
        in 
	tclNOTSAMEGOAL (general_elim (c,l) (elim,[])) gl
   (* was tclWEAK_PROGRESS which only fails for tactics generating one subgoal 
      and did not fail for useless conditional rewritings generating an
      extra condition *)

let general_rewrite lft2rgt c = general_rewrite_bindings lft2rgt (c,[])

let rewriteLR_bindings = general_rewrite_bindings true
let rewriteRL_bindings = general_rewrite_bindings false

let rewriteLR = general_rewrite true
let rewriteRL = general_rewrite false

let dyn_rewriteLR = function
  | [Command com; Bindings binds] -> 
      tactic_com_bind_list rewriteLR_bindings (com,binds)
  | [Constr c; Cbindings binds] -> 
      rewriteLR_bindings (c,binds)
  | _ -> assert false

let dyn_rewriteRL = function
  | [Command com; Bindings binds] -> 
      tactic_com_bind_list rewriteRL_bindings (com,binds)
  | [Constr c; Cbindings binds] -> 
      rewriteRL_bindings (c,binds)
  | _ -> assert false

(* Replacing tactics *)

(* eq,symeq : equality on Set and its symmetry theorem
   eqt,sym_eqt : equality on Type and its symmetry theorem
   c2 c1 : c1 is to be replaced by c2
   unsafe : If true, do not check that c1 and c2 are convertible
   gl : goal *)

let abstract_replace (eq,sym_eq) (eqt,sym_eqt) c2 c1 unsafe gl =
  let t1 = pf_type_of gl c1 
  and t2 = pf_type_of gl c2 in
  if unsafe or (pf_conv_x gl t1 t2) then
    let (e,sym) = 
      match kind_of_term (hnf_type_of gl t1) with 
        | IsSort (Prop(Pos)) -> (eq,sym_eq)
        | IsSort (Type(_))   -> (eqt,sym_eqt)
        | _                  -> error "replace"
    in 
    (tclTHENL (elim_type (applist (e, [t1;c1;c2])))
       (tclORELSE assumption 
          (tclTRY (tclTHEN (apply sym) assumption)))) gl
  else
    error "terms does not have convertible types"

(* Only for internal use *)
let unsafe_replace c2 c1 gl = 
  let eq        = (pf_parse_const gl "eq")     in
  let eqt       = (pf_parse_const gl "eqT")    in 
  let sym_eq    = (pf_parse_const gl "sym_eq") in
  let sym_eqt   = (pf_parse_const gl "sym_eqT") in
  abstract_replace (eq,sym_eq) (eqt,sym_eqt) c2 c1 true gl

let replace c2 c1 gl = 
  let eq        = (pf_parse_const gl "eq")     in
  let eqt       = (pf_parse_const gl "eqT")    in 
  let sym_eq    = (pf_parse_const gl "sym_eq") in
  let sym_eqt   = (pf_parse_const gl "sym_eqT") in
  abstract_replace (eq,sym_eq) (eqt,sym_eqt) c2 c1 false gl
    
let dyn_replace args gl = 
  match args with 
    | [(Command c1);(Command c2)] -> 
       	replace (pf_interp_constr gl c1) (pf_interp_constr gl c2) gl
    | [(Constr c1);(Constr c2)] -> 
       	replace c1 c2 gl
    | _ -> assert false
                 
let v_rewriteLR = hide_tactic "RewriteLR" dyn_rewriteLR
let h_rewriteLR_bindings (c,bl) = v_rewriteLR [(Constr c);(Cbindings bl)] 
let h_rewriteLR c = h_rewriteLR_bindings (c,[])

let v_rewriteRL = hide_tactic "RewriteRL" dyn_rewriteRL
let h_rewriteRL_bindings (c,bl) = v_rewriteRL [(Constr c);(Cbindings bl)] 
let h_rewriteRL c = h_rewriteRL_bindings (c,[])

let v_replace = hide_tactic "Replace" dyn_replace
let h_replace c1 c2 = v_replace [(Constr c1);(Constr c2)]

(* Conditional rewriting, the success of a rewriting is related 
   to the resolution of the conditions by a given tactic *)

let conditional_rewrite lft2rgt tac (c,bl) = 
  tclTHEN_i (general_rewrite_bindings lft2rgt (c,bl))
    (fun i -> if i=1 then tclIDTAC else tclCOMPLETE tac)

let dyn_conditional_rewrite lft2rgt = function
  | [(Tacexp tac); (Command com);(Bindings binds)] -> 
      tactic_com_bind_list 
	(conditional_rewrite lft2rgt (Tacinterp.interp tac)) 
	(com,binds)
  | [(Tacexp tac); (Constr c);(Cbindings binds)] -> 
      conditional_rewrite lft2rgt (Tacinterp.interp tac) (c,binds)
  | _ -> assert false
	
let v_conditional_rewriteLR = 
  hide_tactic "CondRewriteLR" (dyn_conditional_rewrite true)

let v_conditional_rewriteRL = 
  hide_tactic "CondRewriteRL" (dyn_conditional_rewrite false)

(* End of Eduardo's code. The rest of this file could be improved
   using the functions match_with_equation, etc that I defined
   in Pattern.ml.
   -- Eduardo (19/8/97)
*)

(* Tactics for equality reasoning with the "eq"  or "eqT"
   relation This code  will work with any equivalence relation which 
   is substitutive *)

let find_constructor env sigma c =
  let hd,stack = whd_betadeltaiota_stack env sigma c in
  match kind_of_term hd with
    | IsMutConstruct _ -> (hd,stack)
    | _ -> error "find_constructor"

(* Patterns *)

let build_coq_eq eq = eq.eq ()
let build_ind eq = eq.ind ()
let build_rect eq = 
  match eq.rect with
    | None -> assert false
    | Some c -> c ()
	  
(* List of constructions depending of the initial state *)

(* Destructuring patterns *)
let match_eq eqn eq_pat =
  match matches eqn eq_pat with
    | [(1,t);(2,x);(3,y)] -> (t,x,y)
    | _ -> anomaly "match_eq: an eq pattern should match 3 terms"

type elimination_types =
  | Set_Type
  | Type_Type
  | Set_SetorProp
  | Type_SetorProp 

let necessary_elimination sort_arity sort =
  let sort_arity = mkSort sort_arity in
  if (isType sort) then
    if is_Set sort_arity then
      Set_Type
    else 
      if is_Type sort_arity then
	Type_Type
      else  
	errorlabstrm "necessary_elimination" 
	  [< 'sTR "no primitive equality on proofs" >]  
  else
    if is_Set sort_arity then
      Set_SetorProp
    else
      if is_Type sort_arity then
	Type_SetorProp
      else  errorlabstrm "necessary_elimination" 
        [< 'sTR "no primitive equality on proofs" >]

let find_eq_pattern aritysort sort = 
  match necessary_elimination aritysort sort with
    | Set_Type       ->  build_coq_eq_data.eq ()
    | Type_Type      ->  build_coq_idT_data.eq ()
    | Set_SetorProp  ->  build_coq_eq_data.eq ()
    | Type_SetorProp ->  build_coq_eqT_data.eq ()

(* [find_positions t1 t2]

   will find the positions in the two terms which are suitable for
   discrimination, or for injection.  Obviously, if there is a
   position which is suitable for discrimination, then we want to
   exploit it, and not bother with injection.  So when we find a
   position which is suitable for discrimination, we will just raise
   an exception with that position.

   So the algorithm goes like this:

   if [t1] and [t2] start with the same constructor, then we can
   continue to try to find positions in the arguments of [t1] and
   [t2].

   if [t1] and [t2] do not start with the same constructor, then we
   have found a discrimination position

   if one [t1] or [t2] do not start with a constructor and the two
   terms are not already convertible, then we have found an injection
   position.

   A discriminating position consists of a constructor-path and a pair
   of operators.  The constructor-path tells us how to get down to the
   place where the two operators, which must differ, can be found.

   An injecting position has two terms instead of the two operators,
   since these terms are different, but not manifestly so.

   A constructor-path is a list of pairs of (operator * int), where
   the int (based at 0) tells us which argument of the operator we
   descended into.

 *)

exception DiscrFound of
  (constructor_path * int) list * constructor_path * constructor_path

let find_positions env sigma t1 t2 =
  let rec findrec posn t1 t2 =
    let hd1,args1 = whd_betadeltaiota_stack env sigma t1 in
    let hd2,args2 = whd_betadeltaiota_stack env sigma t2 in
    match (kind_of_term hd1, kind_of_term hd2) with
  	
      | IsMutConstruct (sp1,_), IsMutConstruct (sp2,_) ->
        (* both sides are constructors, so either we descend, or we can
           discriminate here. *)
	  if sp1 = sp2 then
            List.flatten
	      (list_map2_i
		 (fun i arg1 arg2 ->
		    findrec ((sp1,i)::posn) arg1 arg2)
		 0 args1 args2)
	  else
	    raise (DiscrFound(List.rev posn,sp1,sp2))

      | _ ->
	  let t1_0 = applist (hd1,args1) 
          and t2_0 = applist (hd2,args2) in
          if is_conv env sigma t1_0 t2_0 then 
	    []
          else
	    let ty1_0 = get_type_of env sigma t1_0 in
	    (match get_sort_of env sigma ty1_0 with
	       | Prop Pos -> [(List.rev posn,t1_0,t2_0)] (* Set *)
	       | Type _ -> [(List.rev posn,t1_0,t2_0)] (* Type *)
	       | _ -> [])
	  in 
	  (try 
	     Inr(findrec [] t1 t2)
	   with DiscrFound (path,c1,c2) -> 
	     Inl (path,c1,c2))

let discriminable env sigma t1 t2 =
  match find_positions env sigma t1 t2 with
    | Inl _ -> true
    | _ -> false

(* Once we have found a position, we need to project down to it.  If
   we are discriminating, then we need to produce False on one of the
   branches of the discriminator, and True on the other one.  So the
   result type of the case-expressions is always Prop.

   If we are injecting, then we need to discover the result-type.
   This can be difficult, since the type of the two terms at the
   injection-position can be different, and we need to find a
   dependent sigma-type which generalizes them both.

   We can get an approximation to the right type to choose by:

   (0) Before beginning, we reserve a metavariable for the default
   value of the match, to be used in all the bogus branches.

   (1) perform the case-splits, down to the site of the injection.  At
   each step, we have a term which is the "head" of the next
   case-split.  At the point when we actually reach the end of our
   path, the "head" is the term to return.  We compute its type, and
   then, backwards, make a sigma-type with every free debruijn
   reference in that type.  We can be finer, and first do a S(TRONG)NF
   on the type, so that we get the fewest number of references
   possible.

   (2) This gives us a closed type for the head, which we use for the
   types of all the case-splits.

   (3) Now, we can compute the type of one of T1, T2, and then unify
   it with the type of the last component of the result-type, and this
   will give us the bindings for the other arguments of the tuple.

 *)

(* The algorithm, then is to perform successive case-splits.  We have
   the result-type of the case-split, and also the type of that
   result-type.  We have a "direction" we want to follow, i.e. a
   constructor-number, and in all other "directions", we want to juse
   use the default-value.

   After doing the case-split, we call the afterfun, with the updated
   environment, to produce the term for the desired "direction".

   The assumption is made here that the result-type is not manifestly
   functional, so we can just use the length of the branch-type to
   know how many lambda's to stick in.

 *)

(* [descend_then sigma env head dirn]

   returns the number of products introduced, and the environment
   which is active, in the body of the case-branch given by [dirn],
   along with a continuation, which expects to be fed:

    (1) the value of the body of the branch given by [dirn]
    (2) the default-value

    (3) the type of the default-value, which must also be the type of
        the body of the [dirn] branch

   the continuation then constructs the case-split.
 *)
let push_rel_type sigma (na,c,t) env =
  push_rel (na,c,t) env

let push_rels vars env =
  List.fold_right (fun nvar env -> push_rel_type Evd.empty nvar env) vars env

let descend_then sigma env head dirn =
  let IndType (indf,_) as indt =
    try find_rectype env sigma (get_type_of env sigma head)
    with Not_found -> assert false in
  let mispec,_ = dest_ind_family indf in
  let cstr = get_constructors indf in
  let dirn_nlams = cstr.(dirn-1).cs_nargs in
  let dirn_env = push_rels cstr.(dirn-1).cs_args env in
  (dirn_nlams,
   dirn_env,
   (fun dirnval (dfltval,resty) ->
      let arign,_ = get_arity indf in
      let p = it_mkLambda_or_LetIn (lift (mis_nrealargs mispec) resty) arign in
      let build_branch i =
	let result = if i = dirn then dirnval else dfltval in
	it_mkLambda_or_LetIn_name env result cstr.(i-1).cs_args
      in
      mkMutCaseL (make_default_case_info mispec, p, head,
		 List.map build_branch (interval 1 (mis_nconstr mispec)))))
  
(* Now we need to construct the discriminator, given a discriminable
   position.  This boils down to:

   (1) If the position is directly beneath us, then we need to do a
   case-split, with result-type Prop, and stick True and False into
   the branches, as is convenient.

   (2) If the position is not directly beneath us, then we need to
   call descend_then, to descend one step, and then recursively
   construct the discriminator.

 *)

(* [construct_discriminator env dirn headval]
   constructs a case-split on [headval], with the [dirn]-th branch
   giving [True], and all the rest giving False. *)

let construct_discriminator sigma env dirn c sort =
  let (IndType(IndFamily (mispec,_) as indf,_) as indt) =
    try find_rectype env sigma (type_of env sigma c)
    with Not_found ->
       (* one can find Rel(k) in case of dependent constructors 
          like T := c : (A:Set)A->T and a discrimination 
          on (c bool true) = (c bool false)
          CP : changed assert false in a more informative error
       *)
      errorlabstrm "Equality.construct_discriminator"
	[< 'sTR "Cannot discriminate on inductive constructors with 
		 dependent types" >] in
  let arsign,arsort = get_arity indf in
  let (true_0,false_0,sort_0) = 
    match necessary_elimination arsort (destSort sort) with
      | Type_Type -> build_coq_UnitT (), build_coq_EmptyT (), (Type dummy_univ)
      | _         -> build_coq_True (),  build_coq_False (),  (Prop Null)
  in
  let p = it_mkLambda_or_LetIn (mkSort sort_0) arsign in
  let cstrs = get_constructors indf in
  let build_branch i =
    let endpt = if i = dirn then true_0 else false_0 in
    it_mkLambda_or_LetIn endpt cstrs.(i-1).cs_args 
  in
  let build_match =
    mkMutCaseL (make_default_case_info mispec, p, c,
	       List.map build_branch (interval 1 (mis_nconstr mispec)))
  in
  build_match
    
let rec build_discriminator sigma env dirn c sort = function
  | [] -> construct_discriminator sigma env dirn c sort
  | ((sp,cnum),argnum)::l ->
      let cty = type_of env sigma c in
      let IndType (indf,_) =
	try find_rectype env sigma cty with Not_found -> assert false in
      let _,arsort = get_arity indf in
      let nparams = mis_nparams (fst (dest_ind_family indf)) in
      let (cnum_nlams,cnum_env,kont) = descend_then sigma env c cnum in
      let newc = mkRel(cnum_nlams-(argnum-nparams)) in
      let subval = build_discriminator sigma cnum_env dirn newc sort l  in
      (match necessary_elimination arsort (destSort sort) with
         | Type_Type ->
	     kont subval (build_coq_EmptyT (),mkSort (Type(dummy_univ)))
	 | _ -> kont subval (build_coq_False (),mkSort (Prop Null)))

let find_eq_data_decompose eqn =
  if (is_matching (build_coq_eq_pattern ()) eqn) then
    (build_coq_eq_data, match_eq (build_coq_eq_pattern ()) eqn)
  else if (is_matching (build_coq_eqT_pattern ()) eqn) then
    (build_coq_eqT_data, match_eq (build_coq_eqT_pattern ()) eqn)
  else if (is_matching (build_coq_idT_pattern ()) eqn) then
    (build_coq_idT_data, match_eq (build_coq_idT_pattern ()) eqn)
  else
    errorlabstrm  "find_eq_data_decompose" [< >]

let gen_absurdity id gl =
(*
  if   (pf_is_matching gl (pat_False ()) (clause_type (Some id) gl)) 
    or (pf_is_matching gl (pat_EmptyT ()) (clause_type  (Some id) gl))
*)
  if is_empty_type (clause_type (Some id) gl)
  then
    simplest_elim (mkVar id) gl
  else
    errorlabstrm "Equality.gen_absurdity" 
      [< 'sTR "Not the negation of an equality" >]

(* Precondition: eq is leibniz equality
 
  returns ((eq_elim t t1 P i t2), absurd_term)
  where  P=[e:t][h:(t1=e)]discrimator 
          absurd_term=EmptyT    if the necessary elimination is Type_Tyoe 

   and   P=[e:t][h[e:t]discriminator 
         absurd_term=Fale       if the necessary eliination is Type_ProporSet
                                   or Set_ProporSet
*)

let discrimination_pf e (t,t1,t2) discriminator lbeq gls =
  let env = pf_env gls in
  let (indt,_) = find_mrectype env (project gls) t in 
  let aritysort = mis_sort (Global.lookup_mind_specif indt) in
  let sort = pf_type_of gls (pf_concl gls) in
  match necessary_elimination aritysort (destSort sort) with
    | Type_Type  ->
 	let eq_elim     = build_rect lbeq in
	let eq_term     = build_coq_eq lbeq in
	let i           = build_coq_IT () in
	let absurd_term = build_coq_EmptyT () in
        let h = pf_get_new_id (id_of_string "HH")gls in
        let pred= mkNamedLambda e t 
                    (mkNamedLambda h (applist (eq_term, [t;t1;(mkRel 1)])) 
		       discriminator)
        in (applist(eq_elim, [t;t1;pred;i;t2]), absurd_term)
	     
    | _ ->
	let i           = build_coq_I () in
	let absurd_term = build_coq_False ()

 in
	let eq_elim     = build_ind lbeq in
        (applist (eq_elim, [t;t1;mkNamedLambda e t discriminator;i;t2]),
 	 absurd_term)

exception NotDiscriminable

let discr id gls =
  let eqn = (pf_whd_betadeltaiota gls (clause_type (Some id) gls)) in
  let sort = pf_type_of gls (pf_concl gls) in 
  let (lbeq,(t,t1,t2)) =
    try find_eq_data_decompose eqn
    with e when catchable_exception e -> raise NotDiscriminable
  in
  let tj = pf_execute gls t in
  let sigma = project gls in
  let env = pf_env gls in
  (match find_positions env sigma t1 t2 with
     | Inr _ -> raise NotDiscriminable
     | Inl (cpath, (_,dirn), _) ->
	 let e = pf_get_new_id (id_of_string "ee") gls in
	 let e_env =
	   push_named_assum (e,assumption_of_judgment env sigma tj) env
	 in
	 let discriminator =
	   build_discriminator sigma e_env dirn (mkVar e) sort cpath in
	 let (indt,_) = find_mrectype env sigma t in 
	 let (pf, absurd_term) =
	   discrimination_pf e (t,t1,t2) discriminator lbeq gls 
	 in
	 tclCOMPLETE((tclTHENS (cut_intro absurd_term)
			([onLastHyp (compose gen_absurdity out_some);
			  refine (mkApp (pf, [| mkVar id |]))]))) gls)


let not_found_message id =
  [<'sTR "the variable"; 'sPC ; 'sTR (string_of_id id) ; 'sPC;
    'sTR" was not found in the current environment" >]

let insatisfied_prec_message cls =
  match cls with
    | None -> [< 'sTR"goal does not satify the expected preconditions">] 
    |  Some id -> [< 'sTR(string_of_id id); 'sPC;
		     'sTR"does not satify the expected preconditions" >]

let discrOnLastHyp gls =
  try onLastHyp (compose discr out_some) gls
  with NotDiscriminable ->
    errorlabstrm "DiscrConcl" [< 'sTR" Not a discriminable equality" >]

let discrClause cls gls =
  match cls with
    | None ->
    	if is_matching (build_coq_not_pattern ()) (pf_concl gls) then
          (tclTHEN (tclTHEN hnf_in_concl intro) discrOnLastHyp) gls
    	else if is_matching (build_coq_imp_False_pattern ()) (pf_concl gls)then
	  (tclTHEN intro discrOnLastHyp) gls
	else 
	  errorlabstrm "DiscrClause" (insatisfied_prec_message cls)
    | Some id ->
	try (discr id gls)
      	with
	  | Not_found -> errorlabstrm "DiscrClause" (not_found_message id)
	  | NotDiscriminable ->
	      errorlabstrm "DiscrHyp"
		[< 'sTR(string_of_id id);'sTR" Not a discriminable equality" >]

let discrEverywhere = 
  tclORELSE
    (Tacticals.tryAllClauses discrClause)
    (fun gls -> 
       errorlabstrm "DiscrEverywhere" [< 'sTR" No discriminable equalities" >])

let discrConcl gls  = discrClause None gls
let discrHyp id gls = discrClause (Some id) gls

(**)
let h_discr      = hide_atomic_tactic "Discr"      discrEverywhere
let h_discrConcl = hide_atomic_tactic "DiscrConcl" discrConcl
let h_discrHyp   = hide_ident_tactic  "DiscrHyp"   discrHyp
(**)

(* returns the sigma type (sigS, sigT) with the respective
    constructor depending on the sort *)

let find_sigma_data s =
  match s with  
    | Prop Pos  -> build_sigma_set ()                    (* Set *) 
    | Type _    -> build_sigma_type ()                   (* Type *)
    | Prop Null -> error "find_sigma_data"

(* [make_tuple env sigma (lift,rterm,rty) lind] assumes [lind-lift] is
   bound in [rty] but no lesser index is bound in [rty]

   Then we will build the term

     (existS A==[type_of(mkRel lind)] P==(Lambda(na:type_of(mkRel lind),
                                        [rty{1/lind}]))
              [(mkRel lind)] [rterm])

   which should have type (sigS A P) - we can verify it by
   typechecking at the end.
 *)

let make_tuple env sigma (prev_lind,rterm,rty) lind =
  assert (dependent (mkRel lind) rty);
  let {intro = exist_term; typ = sig_term} =
    find_sigma_data (get_sort_of env sigma rty) in
  let a = type_of env sigma (mkRel lind) in
  let na = fst (lookup_rel_type lind env) in
  (* If [lind] is not [prev_lind+1] then we lift down rty *)
  let rty = lift (- lind + prev_lind + 1) rty in
  (* Now [lind] is [mkRel 1] and we abstract on (na:a) *)
  let p = mkLambda (na, a, rty) in
  (lind,
   applist(exist_term,[a;p;(mkRel lind);rterm]),
   applist(sig_term,[a;p]))

(* check that the free-references of the type of [c] are contained in
   the free-references of the normal-form of that type.  If the normal
   form of the type contains fewer references, we want to return that
   instead. *)

let minimal_free_rels env sigma (c,cty) =
  let cty_rels = free_rels cty in
  let nf_cty = nf_betadeltaiota env sigma cty in
  let nf_rels = free_rels nf_cty in
  if Intset.subset cty_rels nf_rels then
    (cty,cty_rels)
  else
    (nf_cty,nf_rels)

(* [sig_clausale_forme siglen ty]
    
   Will explode [siglen] [sigS,sigT ]'s on [ty] (depending on the 
   type of ty), and return:

   (1) a pattern, with meta-variables in it for various arguments,
       which, when the metavariables are replaced with appropriate
       terms, will have type [ty]

   (2) an integer, which is the last argument - the one which we just
       returned.

   (3) a pattern, for the type of that last meta

   (4) a typing for each metavariable

   WARNING: No checking is done to make sure that the 
            sigS(or sigT)'s are actually there.
          - Only homogenious pairs are built i.e. pairs where all the 
   dependencies are of the same sort
 *)

let sig_clausale_forme env sigma sort_of_ty siglen ty (dFLT,dFLTty) =
  let { intro = exist_term } = find_sigma_data sort_of_ty in 
  let rec sigrec_clausale_forme siglen ty =
    if siglen = 0 then
      (* We obtain the components dependent in dFLT by matching *)
      let headpat = nf_betadeltaiota env sigma ty in
      let nf_ty = nf_betadeltaiota env sigma dFLTty in
      let bindings =
	list_try_find
	  (fun ty -> 
             try 
            (* Test inutile car somatch ne prend pas en compte les univers *) 
	       if is_Type headpat & is_Type ty then
		 []
	       else
		 matches (pattern_of_constr headpat) ty 
             with PatternMatchingFailure -> failwith "caught")
	  [dFLTty; nf_ty]
      in
      (bindings,dFLT)
    else
      let (a,p) = match whd_beta_stack ty with
	| (_,[a;p]) -> (a,p)
 	| _ -> anomaly "sig_clausale_forme: should be a sigma type" in
      let mv = new_meta() in
      let rty = applist(p,[mkMeta mv]) in
      let (bindings,tuple_tail) = sigrec_clausale_forme (siglen-1) rty in
      let w =
	try List.assoc mv bindings
	with Not_found ->
	  anomaly "Not enough components to build the dependent tuple" in
      (bindings,applist(exist_term,[a;p;w;tuple_tail]))
  in
  snd (sigrec_clausale_forme siglen ty)

(* [make_iterated_tuple sigma env DFLT c]

   Will find the free (DB) references of the S(TRONG)NF of [c]'s type,
   gather them together in left-to-right order (i.e. highest-numbered
   is farthest-left), and construct a big iterated pair out of it.
   This only works when the references are all themselves to members
   of [Set]s, because we use [sigS] to construct the tuple.

   Suppose now that our constructed tuple is of length [tuplen].

   Then, we need to construct the default value for the other
   branches.  The default value is constructed by taking the
   tuple-type, exploding the first [tuplen] [sigS]'s, and replacing at
   each step the binder in the right-hand-type by a fresh
   metavariable.

   In addition, on the way back out, we will construct the pattern for
   the tuple which uses these meta-vars.

   This gives us a pattern, which we use to match against the type of
   DFLT; if that fails, then against the S(TRONG)NF of that type.  If
   both fail, then we just cannot construct our tuple.  If one of
   those succeed, then we can construct our value easily - we just use
   the tuple-pattern.

 *)

let make_iterated_tuple env sigma (dFLT,dFLTty) (c,cty) =
  let (cty,rels) = minimal_free_rels env sigma (c,cty) in
  let sort_of_cty = get_sort_of env sigma cty in
  let sorted_rels = Sort.list (>=) (Intset.elements rels) in
  let (_,tuple,tuplety) =
    List.fold_left (make_tuple env sigma) (0,c,cty) sorted_rels 
  in
  assert (closed0 tuplety);
  let dfltval = 
    sig_clausale_forme env sigma sort_of_cty (List.length sorted_rels) 
      tuplety (dFLT,dFLTty)
  in
  (tuple,tuplety,dfltval)

let rec build_injrec sigma env (t1,t2) c = function
  | [] ->
      make_iterated_tuple env sigma (t1,type_of env sigma t1)
        (c,type_of env sigma c)
  | ((sp,cnum),argnum)::l ->
      let cty = type_of env sigma c in
      let (ity,_) = find_mrectype env sigma cty in
      let nparams = Global.mind_nparams ity in
      let (cnum_nlams,cnum_env,kont) = descend_then sigma env c cnum in
      let newc = mkRel(cnum_nlams-(argnum-nparams)) in
      let (subval,tuplety,dfltval) =
      	build_injrec sigma cnum_env (t1,t2) newc l
      in
      (kont subval (dfltval,tuplety),
       tuplety,dfltval)

let build_injector sigma env (t1,t2) c cpath =
  let (injcode,resty,_) = build_injrec sigma env (t1,t2) c cpath in
  (injcode,resty)

let try_delta_expand env sigma t =
  let whdt = whd_betadeltaiota env sigma t  in 
  let rec hd_rec c  =
    match kind_of_term c with
      | IsMutConstruct _ -> whdt
      | IsApp (f,_)  -> hd_rec f
      | IsCast (c,_) -> hd_rec c
      | _  -> t
  in 
  hd_rec whdt 

(* Given t1=t2 Inj calculates the whd normal forms of t1 and t2 and it 
   expands then only when the whdnf has a constructor of an inductive type
   in hd position, otherwise delta expansion is not done *)

let inj id gls =
  let eqn = (pf_whd_betadeltaiota gls (clause_type (Some id) gls)) in
  let (eq,(t,t1,t2))= 
    try 
      find_eq_data_decompose eqn
    with e when catchable_exception e -> 
      errorlabstrm "Inj"  [<'sTR(string_of_id id); 
			    'sTR" Not a primitive  equality here " >] 
  in
  let tj = pf_execute gls t in
  let sigma = project gls in
  let env = pf_env gls in
  match find_positions env sigma t1 t2 with
    | Inl _ ->
	errorlabstrm "Inj" [<'sTR (string_of_id id);
			     'sTR" is not a projectable equality" >]
    | Inr posns ->
	let e = pf_get_new_id (id_of_string "e") gls in
	let e_env =
	  push_named_assum (e,assumption_of_judgment env sigma tj) env
	in
	let injectors =
	  map_succeed
	    (fun (cpath,t1_0,t2_0) ->
	       let (injbody,resty) =
		 build_injector sigma e_env (t1_0,t2_0) (mkVar e) cpath in
	       let injfun = mkNamedLambda e t injbody in
	       try 
		 let _ = type_of env sigma injfun in (injfun,resty)
	       with e when catchable_exception e -> failwith "caught")
            posns 
	in
	if injectors = [] then
	  errorlabstrm "Equality.inj" 
	    [<'sTR "Failed to decompose the equality">];
	tclMAP 
	  (fun (injfun,resty) ->
	     let pf = applist(eq.congr (),
			      [t;resty;injfun;
			       try_delta_expand env sigma t1;
			       try_delta_expand env sigma t2;
			       mkVar id]) 
	     in
	     let ty = pf_type_of gls pf in
	     ((tclTHENS  (cut  ty) ([tclIDTAC;refine pf]))))
	  injectors
	  gls
	    
let injClause cls gls =
  match cls with
    | None ->
    	if is_matching (build_coq_not_pattern ()) (pf_concl gls) then
          (tclTHEN (tclTHEN hnf_in_concl intro)
             (onLastHyp (compose inj out_some))) gls
    	else
	  errorlabstrm "InjClause" (insatisfied_prec_message  cls)
    | Some id ->
	try 
	  inj id gls
        with
          | UserError("refiner__fail",_) -> 
              errorlabstrm "InjClause" 
		[< 'sTR (string_of_id id); 'sTR" Not a projectable equality" >]

let injConcl gls  = injClause None gls
let injHyp id gls = injClause (Some id) gls

(**)
let h_injConcl = hide_atomic_tactic "Inj" injConcl
let h_injHyp   = hide_ident_tactic "InjHyp" injHyp
(**)

let decompEqThen ntac id gls =
  let eqn = (pf_whd_betadeltaiota gls (clause_type (Some id) gls)) in
  let (lbeq,(t,t1,t2))= find_eq_data_decompose  eqn in
  let sort = pf_type_of gls (pf_concl gls) in 
  let tj = pf_execute gls t in
  let sigma = project gls in
  let env = pf_env gls in 
  (match find_positions env sigma t1 t2 with
     | Inl (cpath, (_,dirn), _) ->
	 let e = pf_get_new_id (id_of_string "e") gls in
	 let e_env =
	   push_named_assum (e,assumption_of_judgment env sigma tj) env in
	 let discriminator =
	   build_discriminator sigma e_env dirn (mkVar e) sort cpath in
	 let (pf, absurd_term) =
	   discrimination_pf e (t,t1,t2) discriminator lbeq gls in
	 tclCOMPLETE
	   ((tclTHENS (cut_intro absurd_term)
	       ([onLastHyp (compose gen_absurdity out_some);
		 refine (mkApp (pf, [| mkVar id |]))]))) gls
     | Inr posns ->
	 (let e = pf_get_new_id (id_of_string "e") gls in
	  let e_env =
	    push_named_assum (e,assumption_of_judgment env sigma tj) env in
	  let injectors =
	    map_succeed
	      (fun (cpath,t1_0,t2_0) ->
		 let (injbody,resty) =
		   build_injector sigma e_env (t1_0,t2_0) (mkVar e) cpath in
		 let injfun = mkNamedLambda e t injbody in
		 try 
		   let _ = type_of env sigma injfun in (injfun,resty)
		 with e when catchable_exception e -> failwith "caught")
	      posns 
	  in
	  if injectors = [] then
	    errorlabstrm "Equality.decompEqThen" 
              [<'sTR "Discriminate failed to decompose the equality">];
	  ((tclTHEN
	      (tclMAP (fun (injfun,resty) ->
			 let pf = applist(lbeq.congr (),
					  [t;resty;injfun;t1;t2;
					   mkVar id]) in
			 let ty = pf_type_of gls pf in
			 ((tclTHENS (cut ty) 
			     ([tclIDTAC;refine pf]))))
		 (List.rev injectors))
	      (ntac (List.length injectors))))
	  gls))

let decompEq = decompEqThen (fun x -> tclIDTAC)

let dEqThen ntac cls gls =
  match cls with
    | None ->
    	if is_matching (build_coq_not_pattern ()) (pf_concl gls) then
	  (tclTHEN hnf_in_concl
	     (tclTHEN intro
         	(onLastHyp (compose (decompEqThen ntac) out_some)))) gls
    	else
	  errorlabstrm "DEqThen" (insatisfied_prec_message  cls)
    | Some id ->
	try 
	  decompEqThen ntac id gls
      	with 
	  | Not_found -> 
	      errorlabstrm "DEqThen" (not_found_message id)
          | e when catchable_exception e ->
	       errorlabstrm "DEqThen" (insatisfied_prec_message cls)

let dEq = dEqThen (fun x -> tclIDTAC)

let dEqConcl gls = dEq None gls
let dEqHyp id gls = dEq (Some id) gls

(**)
let dEqConcl_tac = hide_atomic_tactic "DEqConcl" dEqConcl
let dEqHyp_tac = hide_ident_tactic "DEqHyp" dEqHyp
(**)

let rewrite_msg = function 
  | None ->  
      [<'sTR "passed term is not a primitive equality">] 
  | Some id ->
      [<'sTR (string_of_id id); 'sTR "does not satisfy preconditions ">]

let swap_equands gls eqn =
  let (lbeq,(t,e1,e2)) =
    try 
      find_eq_data_decompose eqn
    with _ -> errorlabstrm "swap_equamds" (rewrite_msg None)
  in 
  applist(lbeq.eq (),[t;e2;e1])

let swapEquandsInConcl gls =
  let (lbeq,(t,e1,e2)) =
    try 
      find_eq_data_decompose (pf_concl gls)
    with _-> errorlabstrm "SwapEquandsInConcl" (rewrite_msg None) 
  in
  let sym_equal = lbeq.sym () in
  refine (applist(sym_equal,[t;e2;e1;mkMeta (new_meta())])) gls

let swapEquandsInHyp id gls =
  ((tclTHENS (cut_replacing id (swap_equands gls (clause_type (Some id) gls)))
      ([tclIDTAC;
      	(tclTHEN (swapEquandsInConcl) (exact_no_check (mkVar id)))]))) gls

(* find_elim determines which elimination principle is necessary to
   eliminate lbeq on sort_of_gl. It yields the boolean true wether
   it is a dependent elimination principle (as idT.rect) and false
   otherwise *)

let find_elim  sort_of_gl  lbeq =
  match kind_of_term sort_of_gl  with
    | IsSort(Prop Null)  (* Prop *)  ->  (lbeq.ind (), false)  
    | IsSort(Prop Pos)   (* Set *)   ->  
	(match lbeq.rrec with
           | Some eq_rec -> (eq_rec (), false) 
	   | None -> errorlabstrm "find_elim"
		 [< 'sTR "this type of elimination is not allowed">])
    | _ (* Type *) -> 
        (match lbeq.rect with
           | Some eq_rect -> (eq_rect (), true) 
           | None -> errorlabstrm "find_elim"
		 [< 'sTR "this type of elimination is not allowed">])

(* builds a predicate [e:t][H:(lbeq t e t1)](body e)
   to be used as an argument for equality dependent elimination principle:
   Preconditon: dependent body (mkRel 1) *)

let build_dependent_rewrite_predicate (t,t1,t2) body lbeq gls =
  let e = pf_get_new_id  (id_of_string "e") gls in 
  let h = pf_get_new_id  (id_of_string "HH") gls in 
  let eq_term = lbeq.eq () in
  (mkNamedLambda e t 
     (mkNamedLambda h (applist (eq_term, [t;t1;(mkRel 1)])) 
        (lift 1 body))) 

(* builds a predicate [e:t](body e) ???
   to be used as an argument for equality non-dependent elimination principle:
   Preconditon: dependent body (mkRel 1) *)

let build_non_dependent_rewrite_predicate (t,t1,t2) body gls =
  lambda_create (pf_env gls) (t,body)

let bareRevSubstInConcl lbeq body (t,e1,e2) gls =
  let (eq_elim,dep) =
    try 
      find_elim (pf_type_of gls (pf_concl gls)) lbeq  
    with e when catchable_exception e -> 
      errorlabstrm "RevSubstIncConcl"
        [< 'sTR "this type of substitution is not allowed">]  
  in 
  let p =
    if dep then
      (build_dependent_rewrite_predicate (t,e1,e2)  body lbeq gls)
    else
      (build_non_dependent_rewrite_predicate (t,e1,e2)  body  gls)
  in
  refine (applist(eq_elim,[t;e1;p;mkMeta(new_meta());
                           e2;mkMeta(new_meta())])) gls

(* [subst_tuple_term dep_pair B]

   Given that dep_pair looks like:

   (existS e1 (existS e2 ... (existS en en+1) ... ))

   and B might contain instances of the ei, we will return the term:

   ([x1:ty(e1)]...[xn:ty(en)]B
    (projS1 (mkRel 1))
    (projS1 (projS2 (mkRel 1)))
    ... etc ...)

   That is, we will abstract out the terms e1...en+1 as usual, but
   will then produce a term in which the abstraction is on a single
   term - the debruijn index [mkRel 1], which will be of the same type
   as dep_pair.

   ALGORITHM for abstraction:

   We have a list of terms, [e1]...[en+1], which we want to abstract
   out of [B].  For each term [ei], going backwards from [n+1], we
   just do a [subst_term], and then do a lambda-abstraction to the
   type of the [ei].

 *)

let match_sigma ex ex_pat =
  match matches ex_pat ex with
    | [(1,a);(2,p);(3,car);(4,cdr)] -> (a,p,car,cdr)
    | _ ->
	anomaly "match_sigma: a successful sigma pattern should match 4 terms"

let find_sigma_data_decompose ex =
  try
    let subst = match_sigma ex (build_coq_existS_pattern ()) in
    (build_sigma_set (),subst)
  with PatternMatchingFailure ->
    (try 
       let subst = match_sigma ex (build_coq_existT_pattern ()) in
       (build_sigma_type (),subst)
     with PatternMatchingFailure -> 
       errorlabstrm "find_sigma_data_decompose" [< >])

let decomp_tuple_term env c t = 
  let rec decomprec inner_code ex exty =
    try
      let {proj1 = p1; proj2 = p2 },(a,p,car,cdr) =
	find_sigma_data_decompose ex in
      let car_code = applist (p1,[a;p;inner_code])
      and cdr_code = applist (p2,[a;p;inner_code]) in
      let cdrtyp = beta_applist (p,[car]) in
      ((car,a),car_code)::(decomprec cdr_code cdr cdrtyp)
    with e when catchable_exception e ->
      [((ex,exty),inner_code)]
  in
  List.split (decomprec (mkRel 1) c t)

let subst_tuple_term env sigma dep_pair b =
  let typ = get_type_of env sigma dep_pair in
  let e_list,proj_list = decomp_tuple_term env dep_pair typ in
  let abst_B =
    List.fold_right
      (fun (e,t) body -> lambda_create env (t,subst_term e body)) e_list b in
  let app_B = applist(abst_B,proj_list) in app_B
    
(* |- (P e2)
     BY RevSubstInConcl (eq T e1 e2)
     |- (P e1)
     |- (eq T e1 e2)
 *)
let revSubstInConcl eqn gls =
  let (lbeq,(t,e1,e2)) = find_eq_data_decompose eqn in
  let body = subst_tuple_term (pf_env gls) (project gls) e2 (pf_concl gls) in
  assert (dependent (mkRel 1) body);
  bareRevSubstInConcl lbeq body (t,e1,e2) gls

(* |- (P e1)
     BY SubstInConcl (eq T e1 e2)
     |- (P e2)
     |- (eq T e1 e2)
 *)
let substInConcl eqn gls =
  (tclTHENS (revSubstInConcl (swap_equands gls eqn))
     ([tclIDTAC;
       swapEquandsInConcl])) gls

let substInHyp eqn id gls =
  let (lbeq,(t,e1,e2)) = (find_eq_data_decompose eqn) in 
  let body = subst_term e1 (clause_type (Some id) gls) in
  if not (dependent (mkRel 1) body) then errorlabstrm  "SubstInHyp" [<>];
  (tclTHENS (cut_replacing id (subst1 e2 body))
     ([tclIDTAC;
       (tclTHENS (bareRevSubstInConcl lbeq body (t,e1,e2))
          ([exact_no_check (mkVar id);tclIDTAC]))])) gls

let revSubstInHyp eqn id gls =
  (tclTHENS (substInHyp (swap_equands gls eqn) id)
     ([tclIDTAC;
       swapEquandsInConcl])) gls

let try_rewrite tac gls =
  try 
    tac gls
  with 
    | UserError ("find_eq_data_decompose",_) -> errorlabstrm 
	  "try_rewrite" [< 'sTR "Not a primitive equality here">]
    | UserError ("swap_equamds",_) -> errorlabstrm 
          "try_rewrite" [< 'sTR "Not a primitive equality here">]
    | UserError("find_eq_elim",s) -> errorlabstrm "try_rew" 
          [<'sTR "This type of elimination is not allowed ">]  
    | e when catchable_exception e -> 
	errorlabstrm "try_rewrite"
          [< 'sTR "Cannot find a well type generalisation of the goal that";
             'sTR " makes progress the proof.">]

(* list_int n 0 [] gives the list [1;2;...;n] *)
let rec list_int n cmr l =
  if cmr = n then
    l @ [n]
  else
    list_int n (cmr+1) (l @ [cmr])

(* Tells if two constrs are equal modulo unification *)

(* Alpha-conversion *)
let bind_eq = function
  | (Anonymous,Anonymous) -> true
  | (Name _,Name _) -> true
  | _ -> false

let eqop_mod_names = function
  | OpLambda n0, OpLambda n1 -> bind_eq (n0,n1)
  | OpProd n0, OpProd n1 -> bind_eq (n0,n1)
  | OpLetIn n0, OpLetIn n1 -> bind_eq (n0,n1)
  | op0, op1 -> op0 = op1

exception NotEqModRel

let rec eq_mod_rel l_meta t0 t1 =
  match splay_constr_with_binders t1 with
    | OpMeta n, [], [||] ->
	if not (List.mem_assoc n l_meta) then
	  [(n,t0)]@l_meta
	else if (List.assoc n l_meta) = t0 then
	  l_meta
	else
	  raise NotEqModRel
    | op1, bd1, v1 ->
	match splay_constr_with_binders t0 with
	  | op0, bd0, v0
	      when (eqop_mod_names (op0, op1)
		    & (List.length bd0 = List.length bd1)
		    & (Array.length v0 = Array.length v1)) ->
	      array_fold_left2 eq_mod_rel
		(List.fold_left2 eq_mod_rel_binders l_meta bd0 bd1)
		v0 v1
	    | _ -> raise NotEqModRel

  and eq_mod_rel_binders l_meta t0 t1 = match (t0,t1) with
    | (na0,Some b0,t0), (na1,Some b1,t1) when bind_eq (na0,na1) ->
	eq_mod_rel (eq_mod_rel l_meta b0 b1) t0 t1
    | (na0,None,t0), (na1,None,t1) when bind_eq (na0,na1) ->
	eq_mod_rel l_meta t0 t1
    | _ -> raise NotEqModRel

(* Verifies if the constr has an head constant *)

let is_hd_const c = match kind_of_term c with
  | IsApp (f,args) ->
      (match kind_of_term f with
         | IsConst (c,_) -> Some (c, args)
         |_ -> None)
  | _ -> None

(* Gives the occurrences number of a t in u
   Rem: t is assumed closed then there is no need to lift it
*)

let nb_occ_term t u =
  let rec nbrec nocc u =
    if t = u then   (* Pourquoi pas eq_constr ?? *)
      nocc + 1
    else
      Array.fold_left nbrec nocc (snd (splay_constr u))
  in nbrec 0 u
    

(* Gives Some(first instance of ceq in cref,occurence number for this
   instance) or None if no instance of ceq can be found in cref
   Rem: t_eq is assumed closed then there is no need to lift it
*)
let sub_term_with_unif cref ceq =
  let rec find_match l_meta nb_occ hdsp t_args u = match splay_constr u with
    | OpApp, cl -> begin
	let f, args = destApplication u in
	match kind_of_term f with
          | IsConst (sp,_) when sp = hdsp -> begin
	      try (array_fold_left2 eq_mod_rel l_meta args t_args, nb_occ+1)
	      with NotEqModRel ->
		Array.fold_left
                  (fun (l_meta,nb_occ) x -> find_match l_meta nb_occ
                       hdsp t_args x) (l_meta,nb_occ) args
	    end

          | IsConst _ | IsVar _ | IsMutInd _ | IsMutConstruct _
	  | IsFix _ | IsCoFix _ ->
               Array.fold_left 
		 (fun (l_meta,nb_occ) x -> find_match l_meta
		      nb_occ hdsp t_args x) (l_meta,nb_occ) cl

	   (* Pourquoi ne récurre-t-on pas dans f ? *)
           | _ -> (l_meta,nb_occ)
      end

(* Le code original ne récurrait pas sous les Cast 
    | OpCast, _ -> (l_meta,nb_occ)
*)
    | _, t -> 
	Array.fold_left 
	  (fun (l_meta,nb_occ) x -> find_match l_meta nb_occ hdsp t_args x)
	  (l_meta,nb_occ) t

  in
  match (is_hd_const ceq) with
    | None ->
        if (occur_meta ceq) then
          None
        else
          let nb_occ = nb_occ_term ceq cref in
          if nb_occ = 0 then
            None
          else
            Some (ceq,nb_occ)
    |Some (head,t_args) ->
        let (l,nb)=find_match [] 0 head t_args cref in
        if nb = 0 then
          None
        else
          Some ((plain_instance l ceq),nb)
	    
(*The Rewrite in tactic*)
let general_rewrite_in lft2rgt id (c,lb) gls =
  let typ_id =
    (try
       let (_,ty) = lookup_named id (pf_env gls) in ty
     with Not_found -> 
       errorlabstrm "general_rewrite_in" 
	 [< 'sTR"No such hypothesis : "; pr_id id >])
  in
  let (wc,_) = startWalk gls
  and (_,_,t) = reduce_to_ind (pf_env gls) (project gls) (pf_type_of gls c) in
  let ctype = type_clenv_binding wc (c,t) lb in
  match (match_with_equation ctype) with
    | None -> error "The term provided does not end with an equation" 
    | Some (hdcncl,l) ->
        let mbr_eq =
          if lft2rgt then
            List.hd (List.tl (List.rev l))
          else
            List.hd (List.rev l)
        in
        (match (sub_term_with_unif 
		  (collapse_appl (strip_outer_cast typ_id))
		  (collapse_appl mbr_eq)) with
           | None ->
               errorlabstrm "general_rewrite_in" 
		 [<'sTR "Nothing to rewrite in: "; pr_id id>]
           | Some (l2,nb_occ) ->
               (tclTHENSI
		  (tclTHEN
		     (tclTHEN (generalize [(pf_global gls id)])
			(reduce (Pattern [(list_int nb_occ 1 [],l2,
					   pf_type_of gls l2)]) []))
		     (general_rewrite_bindings lft2rgt (c,lb))) 
		  [(tclTHEN (clear_one id) (introduction id))]) gls)

let dyn_rewrite_in lft2rgt = function
  | [Identifier id;(Command com);(Bindings binds)] -> 
      tactic_com_bind_list (general_rewrite_in lft2rgt id) (com,binds)
  | [Identifier id;(Constr c);(Cbindings binds)] -> 
      general_rewrite_in lft2rgt id (c,binds)
  | _ -> assert false

let rewriteLR_in_tac =  hide_tactic "RewriteLRin" (dyn_rewrite_in true)
let rewriteRL_in_tac = hide_tactic "RewriteRLin" (dyn_rewrite_in false)
			 
let conditional_rewrite_in lft2rgt id tac (c,bl) = 
  tclTHEN_i (general_rewrite_in lft2rgt id (c,bl))
    (fun i -> if i=1 then tclIDTAC else tclCOMPLETE tac)
    
let dyn_conditional_rewrite_in lft2rgt = function
  | [(Tacexp tac); Identifier id; (Command com);(Bindings binds)] -> 
      tactic_com_bind_list 
	(conditional_rewrite_in lft2rgt id (Tacinterp.interp tac)) 
	(com,binds)
  | [(Tacexp tac); Identifier id; (Constr c);(Cbindings binds)] -> 
      conditional_rewrite_in lft2rgt id (Tacinterp.interp tac) (c,binds)
  | _ -> assert false

let v_conditional_rewriteLR_in = 
  hide_tactic "CondRewriteLRin" (dyn_conditional_rewrite_in true) 

let v_conditional_rewriteRL_in = 
  hide_tactic "CondRewriteRLin" (dyn_conditional_rewrite_in false)

(* Rewrite c in id. Rewrite -> c in id. Rewrite <- c in id. 
   Does not work when c is a conditional equation *)

let rewrite_in lR com id gls =
  (try 
     let _ = lookup_named id (pf_env gls) in () 
   with Not_found -> 
     errorlabstrm "rewrite_in" [< 'sTR"No such hypothesis : " ;pr_id id >]);
  let c = pf_interp_constr gls com in
  let eqn = pf_type_of gls c in
  try
    let _ = find_eq_data_decompose eqn in
    (try 
       (tclTHENS 
          ((if lR then substInHyp else revSubstInHyp) eqn id) 
          ([tclIDTAC ; exact_no_check c])) gls
     with UserError("SubstInHyp",_) -> tclIDTAC gls)
  with UserError ("find_eq_data_decompose",_)->  
    errorlabstrm "rewrite_in" [< 'sTR"No equality here" >] 
      
let subst eqn cls gls =
  match cls with
    | None ->    substInConcl eqn gls
    | Some id -> substInHyp eqn id gls

(* |- (P a)
 * Subst_Concl a=b 
 *  |- (P b)
 *  |- a=b
 *)

let substConcl_LR eqn gls = try_rewrite (subst eqn None) gls
let substConcl_LR_tac = 
  let gentac = 
    hide_tactic "SubstConcl_LR"
      (function 
	 | [Command eqn] -> 
	     (fun gls ->  substConcl_LR (pf_interp_constr gls eqn)  gls)
	 | _ -> assert false)
  in 
  fun eqn  -> gentac [Command eqn] 

(* id:(P a) |- G
 * SubstHyp a=b id
 *  id:(P b) |- G
 *  id:(P a) |-a=b
*)

let hypSubst id cls gls =
  match cls with
    | None -> 
	(tclTHENS (substInConcl (clause_type (Some id) gls))
	   ([tclIDTAC; exact_no_check (mkVar id)])) gls
    | Some hypid -> 
	(tclTHENS (substInHyp (clause_type (Some id) gls) hypid)
	   ([tclIDTAC;exact_no_check (mkVar id)])) gls

(* id:a=b |- (P a)
 * HypSubst id.
 *  id:a=b |- (P b)
 *)
let substHypInConcl_LR id gls = try_rewrite (hypSubst id None) gls
let substHypInConcl_LR_tac =
  let gentac = 
    hide_tactic "SubstHypInConcl_LR" 
      (function 
	 | [Identifier id] -> substHypInConcl_LR id
	 | _ -> assert false)
  in 
  fun id -> gentac [Identifier id]

(* id:a=b H:(P a) |- G
   SubstHypInHyp id H.
    id:a=b H:(P b) |- G
*)
let revSubst eqn cls gls =
  match cls with
    | None -> revSubstInConcl eqn gls
    | Some id -> revSubstInHyp eqn id gls

(* |- (P b)
   SubstConcl_RL a=b
     |- (P a)
     |- a=b
*)
let substConcl_RL eqn gls = try_rewrite (revSubst eqn None) gls
let substConcl_RL_tac = 
  let gentac = 
    hide_tactic "SubstConcl_RL"
      (function 
	 | [Command eqn] -> 
	     (fun gls ->  substConcl_RL (pf_interp_constr gls eqn)  gls)
	 | _ -> assert false)
  in 
  fun eqn  -> gentac [Command eqn] 

(* id:(P b) |-G
   SubstHyp_RL a=b id 
      id:(P a) |- G
      |- a=b  
*)
let substHyp_RL  eqn id gls = try_rewrite (revSubst eqn (Some id)) gls

let revHypSubst id cls gls =
  match cls with
    | None -> 
	(tclTHENS (revSubstInConcl (clause_type (Some id) gls))
	   ([tclIDTAC; exact_no_check (mkVar id)])) gls
    | Some hypid -> 
	(tclTHENS (revSubstInHyp (clause_type (Some id) gls) hypid)
	   ([tclIDTAC;exact_no_check (mkVar id)])) gls

(* id:a=b |- (P b)
 * HypSubst id.
 * id:a=b |- (P a)
 *)
let substHypInConcl_RL id gls = try_rewrite (revHypSubst id None) gls
let substHypInConcl_RL_tac =
  let gentac = 
    hide_tactic "SubstHypInConcl_RL" 
      (function 
	 | [Identifier id] -> substHypInConcl_RL id
         | _ -> assert false)
  in 
  fun id -> gentac [Identifier id]

(* id:a=b H:(P b) |- G
   SubstHypInHyp id H.
    id:a=b H:(P a) |- G
*)

(**********************************************************************)
(*                    AutoRewrite                                     *)
(**********************************************************************)

(****Dealing with the rewriting rules****)

(* A rewriting is typically an equational constr with an orientation (true=LR
   and false=RL) *)
type rewriting_rule = constr * bool

(* The table of rewriting rules. The key is the name of the rule base.  
   the value is a list of [rewriting_rule] *)
let rew_tab = ref Gmapl.empty

(*Functions necessary to the summary*)
let init () = rew_tab := Gmapl.empty
let freeze () = !rew_tab
let unfreeze ft = rew_tab := ft

(*Declaration of the summary*)
(*let _ = 
  Summary.declare_summary "autorewrite"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_section = false }*)

(*Adds a list of rules to the rule table*)
let add_list_rules rbase lrl = 
  List.iter (fun r -> rew_tab := Gmapl.add rbase r !rew_tab) lrl

(*Gives the list of rules for the base named rbase*)
let rules_of_base rbase = List.rev (Gmapl.find rbase !rew_tab)

(*Functions necessary to the library object declaration*)
let load_autorewrite_rule _ = ()
let cache_autorewrite_rule (_,(rbase,lrl)) = add_list_rules rbase lrl
let export_autorewrite_rule x = Some x

(*Declaration of the AUTOREWRITE_RULE library object*)
let (in_autorewrite_rule,out_autorewrite_rule)=
  Libobject.declare_object
    ("AUTOREWRITE_RULE",
     { Libobject.load_function = load_autorewrite_rule;
       Libobject.open_function = cache_autorewrite_rule;
       Libobject.cache_function = cache_autorewrite_rule;
       Libobject.export_function = export_autorewrite_rule })

(* Semantic of the HintRewrite vernacular command *)
let _ = 
  vinterp_add "HintRewrite"
  (let rec lrules_arg lrl = function
     | [] -> lrl
     | (VARG_VARGLIST [VARG_CONSTR rule; VARG_STRING ort])::a 
	 when ort="LR" or ort="RL" ->
           lrules_arg (lrl@[(Astterm.interp_constr Evd.empty
			      (Global.env()) rule,ort="LR")]) a
     | _ -> bad_vernac_args "HintRewrite"
   and lbases_arg lbs = function
     | [] -> lbs
     | (VARG_VARGLIST ((VARG_IDENTIFIER rbase)::b))::a ->
      	 lbases_arg (lbs@[(rbase,lrules_arg [] b)]) a
     | _ -> bad_vernac_args "HintRewrite"
   in
   fun largs () ->
     List.iter (fun c -> Lib.add_anonymous_leaf
		    (in_autorewrite_rule c)) (lbases_arg [] largs))

(****The tactic****)

(*To build the validation function. Length=number of unproven goals, Valid=a
  validation which solves*)
type valid_elem =
  | Length of int
  | Valid of validation

(* Ce truc devrait aller dans Std -- papageno *)
(*Gives the sub_list characterized by the indexes i_s and i_e with respect to
  lref*)
let sub_list lref i_s i_e =
  let rec sub_list_rec l i =
    if i = i_e then
      l @ [List.nth lref i]
    else if (i>=i_s) & (i<i_e) then
      sub_list_rec (l@[List.nth lref i]) (i+1)
    else
      anomalylabstrm "Equality.sub_list" [<'sTR "Out of range">]
  in
  sub_list_rec [] i_s

(*Cuts the list l2becut in lists which lengths are given by llth*)
let cut_list l2becut lval =
  let rec cut4_1goal cmr l1g = function
    | [] -> (cmr,l1g)
    | a::b ->
	(match a with
           | Length lth ->
               if lth = 0 then
		 cut4_1goal cmr l1g b
               else
		 cut4_1goal (cmr+lth) 
		   (l1g@(sub_list l2becut cmr (cmr+lth-1))) b
           | Valid p ->
               cut4_1goal cmr (l1g@[p []]) b)	
  and cut_list_rec cmr l2b=function
    | [] -> l2b
    | a::b ->
	let (cmr,l1g)=cut4_1goal cmr [] a in
        cut_list_rec cmr (l2b@[l1g]) b
  in
  cut_list_rec 0 [] lval

(*Builds the validation function with lvalid and with respect to l*)
let validation_gen lvalid l =
  let (lval,larg_velem) = List.split lvalid in
  let larg=cut_list l larg_velem in
  List.fold_left2 (fun a p l -> p ([a]@l)) (List.hd lval (List.hd larg))
    (List.tl lval) (List.tl larg)

(*Adds the main argument for the last validation function*)
let mod_hdlist l =
  match (List.hd l) with
    | (p,[Length 0]) -> l
    | (p,larg) -> (p,[Length 1]@larg)::(List.tl l)

(*For the Step options*)
type option_step=
  | Solve
  | Use
  | All

(* the user can give a base either by a name of by its full definition
  The definition is an Ast that will find its meaning only in the context
  of a given goal *)
type hint_base = 
  | By_name of identifier
  | Explicit of (Coqast.t * bool) list

let explicit_hint_base gl = function 
  | By_name id -> 
      begin match rules_of_base id with
	| [] -> errorlabstrm "autorewrite" [<'sTR ("Base "^(string_of_id id)^
						   " does not exist")>]
	| lbs -> lbs
      end 
  | Explicit lbs -> 
      List.map (fun (ast,b) -> (pf_interp_constr gl ast, b)) lbs 

(*AutoRewrite cannot be expressed with a combination of tacticals (due to the
  options). So, we make it in a primitive way*)
let autorewrite lbases ltacstp opt_step ltacrest opt_rest depth_step gls =
  let lst = List.flatten (List.map (explicit_hint_base gls) lbases)
  and unproven_goals = ref []
  and fails = ref 0
  and (sigr,g) = unpackage gls in
  let put_rewrite lrw = List.map (fun (x,y) -> general_rewrite y x) lrw
  and nbr_rules = List.length lst in
  let lst_rew = put_rewrite lst in
  let rec try2solve_main_goal mgl = function
    | [] -> None
    | a::b ->
        try
          let (gl_solve,p_solve)=apply_sig_tac sigr a mgl in
          if gl_solve=[] then
            Some (gl_solve,p_solve)
          else
            try2solve_main_goal mgl b
        with e when catchable_exception e -> 
	  try2solve_main_goal mgl b
  and try_tacs4main_goal mgl = function
    | [] -> None
    | a::b ->
        try
          Some (apply_sig_tac sigr a mgl)
        with e when catchable_exception e -> 
	  try_tacs4main_goal mgl b
  and try2solve1gen_goal gl = function
    | [] -> ([gl],Length 1)
    | a::b ->
        try
          let (gl_solve,p_solve)=apply_sig_tac sigr a gl in
          if gl_solve=[] then
            ([],Valid p_solve)
          else
            try2solve1gen_goal gl b
        with e when catchable_exception e -> 
	  try2solve1gen_goal gl b
  and try2solve_gen_goals (lgls,valg) ltac = function
    | [] -> (lgls,valg)
    | a::b ->
        let (g,elem)=try2solve1gen_goal a ltac in
        try2solve_gen_goals (lgls@g,valg@[elem]) ltac b
  and iterative_rew cmr fails (cglob,cmod,warn) unp_goals lvalid =
    let cmd = ref cmod
    and wrn = ref warn in
    if !cmd=depth_step then begin
      wARNING [<'sTR ((string_of_int cglob)^" rewriting(s) carried out") >];
      cmd := 0;
      wrn := true
    end;
    if fails = nbr_rules then
      (unp_goals,lvalid,!wrn)
    else if cmr = nbr_rules then
      iterative_rew 0 0 (cglob,!cmd,!wrn) unp_goals lvalid
    else 
      try
	let (gl,p) = 
	  apply_sig_tac sigr (List.nth lst_rew cmr) (List.hd unp_goals) 
	in
	let (lgl_gen,lval_gen) =
	  match ltacrest with
            | None ->
		if (List.length gl)=1 then
		  ([],[])
		else
		  (List.tl gl,[Length ((List.length gl)-1)])
            | Some ltac ->
		try2solve_gen_goals ([],[]) ltac (List.tl gl)
	in
	if opt_rest & (not(lgl_gen=[])) then
          iterative_rew (cmr+1) (fails+1) (cglob,!cmd,!wrn) unp_goals lvalid
	else
          (match ltacstp with
             | None ->
                 iterative_rew (cmr+1) fails
                   (cglob+1,!cmd+1,!wrn) 
		   ((List.hd gl)::(lgl_gen@(List.tl unp_goals)))
                   ((p,lval_gen)::lvalid)
             | Some ltac ->
                 (match opt_step with
                    | Solve ->
			(match (try2solve_main_goal (List.hd gl) ltac) with
                           | None ->
                               iterative_rew (cmr+1) fails
                                 (cglob+1,!cmd+1,!wrn) 
				 ((List.hd gl)::(lgl_gen@(List.tl unp_goals)))
                                 ((p,lval_gen)::lvalid)
                           | Some (gl_solve,p_solve) ->
                               (lgl_gen@(List.tl unp_goals),
				(p_solve,[Length 0])::(p,lval_gen)
				::lvalid,!wrn))
                    | Use ->	
			(match (try_tacs4main_goal (List.hd gl) ltac) with
                           | None ->
                               iterative_rew (cmr+1) fails
                                 (cglob+1,!cmd+1,!wrn) 
				 ((List.hd gl)::(lgl_gen@(List.tl unp_goals)))
                                 ((p,lval_gen)::lvalid)
                           | Some(gl_trans,p_trans) ->
                               let lth=List.length gl_trans in
                               if lth=0 then
                                 (lgl_gen@(List.tl unp_goals),
				  (p_trans,[Length 0])::(p,lval_gen)::lvalid,
				  !wrn)
                               else if lth=1 then
                                 iterative_rew (cmr+1) fails
                                   (cglob+1,!cmd+1,!wrn)
                                   (gl_trans@(lgl_gen@(List.tl
							 unp_goals)))
                                   ((p_trans,[])::(p,lval_gen)::
                                    lvalid)
                               else
                                 iterative_rew (cmr+1) fails
                                   (cglob+1,!cmd+1,!wrn)
                                   (gl_trans@(lgl_gen@(List.tl unp_goals))) 
				   ((p_trans,
				     [Length ((List.length gl_trans)-1)])::
				    (p,lval_gen):: lvalid))
                    | All ->
			(match (try2solve_main_goal (List.hd gl) ltac) with
                           | None ->
                               (match (try_tacs4main_goal 
					 (List.hd gl) ltac) with
                                  | None ->
                                      iterative_rew (cmr+1) fails
					(cglob+1,!cmd+1,!wrn)
					((List.hd
                                            gl)::(lgl_gen@(List.tl
							     unp_goals)))
					((p,lval_gen)::lvalid)
                                  | Some(gl_trans,p_trans) ->
                                      let lth = List.length gl_trans in
                                      if lth = 0 then
                                        (lgl_gen@(List.tl unp_goals),
					 (p_trans,[Length 0])::
					 (p,lval_gen)::lvalid, !wrn)
                                      else if lth = 1 then
                                        iterative_rew (cmr+1) fails
                                          (cglob+1,!cmd+1,!wrn)
                                          (gl_trans@
					   (lgl_gen@
					    (List.tl unp_goals)))
                                          ((p_trans,[])::
					   (p,lval_gen)::lvalid)
                                      else
                                        iterative_rew (cmr+1) fails
                                          (cglob+1,!cmd+1,!wrn)
                                          (gl_trans@
					   (lgl_gen@
					    (List.tl unp_goals)))
                                          ((p_trans,
					    [Length 
					       ((List.length gl_trans)-1)])::
					   (p, lval_gen)::lvalid))
                           | Some (gl_solve,p_solve) ->
                               (lgl_gen@(List.tl unp_goals),
				(p_solve,[Length 0])::
				(p,lval_gen)::lvalid,!wrn))))
      with e when catchable_exception e ->
	iterative_rew (cmr+1) (fails+1) (cglob,!cmd,!wrn) unp_goals lvalid
    in
    let (gl,lvalid)=
      let (gl_res,lvalid_res,warn)=iterative_rew 0 0 (0,0,false) [g] [] in
      if warn then mSGNL [<>];
      (gl_res,lvalid_res)
    in
    let validation_fun=
      if lvalid = [] then
        (fun l -> List.hd l)
      else
        let nlvalid=mod_hdlist lvalid in
        (fun l -> validation_gen nlvalid l)
    in
    (repackage sigr gl,validation_fun)

(*Collects the arguments of AutoRewrite ast node*)
(*let dyn_autorewrite largs=
  let rec explicit_base largs =
    let tacargs = List.map cvt_arg largs in 
    List.map 
      (function
	 | Redexp ("LR", [Coqast.Node(_,"Command", [ast])]) -> ast, true
	 | Redexp ("RL", [Coqast.Node(_,"Command", [ast])]) -> ast, false
	 | _ -> anomaly "Equality.explicit_base") 
      tacargs
  and list_bases largs =
    let tacargs = List.map cvt_arg largs in 
    List.map 
      (function 
	 | Redexp ("ByName", [Coqast.Nvar(_,s)]) -> 
	     By_name (id_of_string s)
	 | Redexp ("Explicit", l) ->
	     Explicit (explicit_base l)
	 | _ -> anomaly "Equality.list_bases") 
      tacargs
  and int_arg=function
    | [(Integer n)] -> n
    | _ -> anomalylabstrm "dyn_autorewrite" 
	  [<'sTR "Bad call of int_arg (not an INTEGER)">]
  and list_args_rest (lstep,evstep) (ostep,evostep) (lrest,evrest)
    (orest,evorest) (depth,evdepth) = function
      | [] -> (lstep,ostep,lrest,orest,depth)
      | (Redexp (s,l))::tail ->
	  if s="Step" & not evstep then
            list_args_rest ((List.map Tacinterp.interp l),true) (ostep,evostep)
              (lrest,evrest) (orest,evorest) (depth,evdepth) tail
	  else if s="SolveStep" & not evostep then
            list_args_rest (lstep,evstep) (Solve,true) (lrest,evrest)
              (orest,evorest) (depth,evdepth) tail
	  else if s="Use" & not evostep then
            list_args_rest (lstep,evstep) (Use,true) (lrest,evrest) 
	      (orest,evorest) (depth,evdepth) tail
	  else if s="All" & not evostep then
            list_args_rest (lstep,evstep) (All,true) (lrest,evrest) 
	      (orest,evorest) (depth,evdepth) tail
	  else if s="Rest" & not evrest then
            list_args_rest (lstep,evstep) (ostep,evostep) 
	      ((List.map Tacinterp.interp l),true) (orest,evorest) 
	      (depth,evdepth) tail
	  else if s="SolveRest" & not evorest then
            list_args_rest (lstep,evstep) (ostep,evostep) (lrest,evrest)
              (false,true) (depth,evdepth) tail
	  else if s="Cond" & not evorest then
            list_args_rest (lstep,evstep) (ostep,evostep) (lrest,evrest)
              (true,true) (depth,evdepth) tail
	  else if s="Depth" & not evdepth then
            (let dth = int_arg (List.map cvt_arg l) in
             if dth > 0 then
               list_args_rest (lstep,evstep) (ostep,evostep) (lrest,evrest)
		 (orest,evorest) (dth,true) tail
             else
               errorlabstrm "dyn_autorewrite" 
		 [<'sTR "Depth value lower or equal to 0">])
	  else
            anomalylabstrm "dyn_autorewrite" 
	      [<'sTR "Bad call of list_args_rest">]
      | _ -> 
	  anomalylabstrm "dyn_autorewrite" 
	    [<'sTR "Bad call of list_args_rest">]
  and list_args = function
    | (Redexp (s,lbases))::tail ->
	if s = "BaseList" then
          (let (lstep,ostep,lrest,orest,depth) = 
	     list_args_rest ([],false) (Solve,false) ([],false) (false,false) 
	       (100,false) tail
           in
           autorewrite (list_bases lbases) 
	     (if lstep = [] then None else Some lstep) 
	     ostep (if lrest=[] then None else Some lrest) orest depth)
	else
          anomalylabstrm "dyn_autorewrite" 
	    [<'sTR "Bad call of list_args (not a BaseList tagged REDEXP)">]
    | _ ->
	anomalylabstrm "dyn_autorewrite" 
	  [<'sTR "Bad call of list_args (not a REDEXP)">]
  in
  list_args largs*)

(*Adds and hides the AutoRewrite tactic*)
(*let h_autorewrite = hide_tactic "AutoRewrite" dyn_autorewrite*)
