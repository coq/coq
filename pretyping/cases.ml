(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Names
open Nameops
open Term
open Termops
open Declarations
open Inductiveops
open Environ
open Sign
open Reductionops
open Typeops
open Type_errors

open Rawterm
open Retyping
open Pretype_errors
open Evarutil
open Evarconv

(* Pattern-matching errors *)

type pattern_matching_error =
  | BadPattern of constructor * constr
  | BadConstructor of constructor * inductive
  | WrongNumargConstructor of constructor * int
  | WrongPredicateArity of constr * constr * constr
  | NeedsInversion of constr * constr
  | UnusedClause of cases_pattern list
  | NonExhaustive of cases_pattern list
  | CannotInferPredicate of (constr * types) array

exception PatternMatchingError of env * pattern_matching_error

let raise_pattern_matching_error (loc,ctx,te) =
  Stdpp.raise_with_loc loc (PatternMatchingError(ctx,te))

let error_bad_pattern_loc loc cstr ind =
  raise_pattern_matching_error (loc, Global.env(), BadPattern (cstr,ind))

let error_bad_constructor_loc loc cstr ind =
  raise_pattern_matching_error (loc, Global.env(), BadConstructor (cstr,ind))

let error_wrong_numarg_constructor_loc loc c n =
  raise_pattern_matching_error (loc, Global.env(), WrongNumargConstructor (c,n))

let error_wrong_predicate_arity_loc loc env c n1 n2 =
  raise_pattern_matching_error (loc, env, WrongPredicateArity (c,n1,n2))

let error_needs_inversion env x t =
  raise (PatternMatchingError (env, NeedsInversion (x,t)))

(*********************************************************************)
(* A) Typing old cases                                               *)
(* This was previously in Indrec but creates existential holes       *)

let mkExistential isevars env loc = new_isevar isevars env loc (new_Type ())

let norec_branch_scheme env isevars cstr =
  let rec crec env = function
    | d::rea -> mkProd_or_LetIn d (crec (push_rel d env) rea)
    | [] -> mkExistential isevars env (dummy_loc, InternalHole) in 
  crec env (List.rev cstr.cs_args)

let rec_branch_scheme env isevars (sp,j) recargs cstr =
  let rec crec env (args,recargs) = 
    match args, recargs with 
      | (name,None,c as d)::rea,(ra::reca) -> 
	  let d =
 	    match dest_recarg ra with 
	      | Mrec k when k=j ->
		  let t = mkExistential isevars env (dummy_loc, InternalHole)
		  in
		  mkArrow t
		    (crec (push_rel (Anonymous,None,t) env)
		       (List.rev (lift_rel_context 1 (List.rev rea)),reca))
              | _ -> crec (push_rel d env) (rea,reca) in
          mkProd (name,  c, d)

      | (name,Some b,c as d)::rea, reca -> 
	  mkLetIn (name,b, c,crec (push_rel d env) (rea,reca))
      | [],[] -> mkExistential isevars env (dummy_loc, InternalHole)
      | _ -> anomaly "rec_branch_scheme"
  in 
  crec env (List.rev cstr.cs_args,recargs) 
    
let branch_scheme env isevars isrec indf =
  let (ind,params) = dest_ind_family indf in
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let cstrs = get_constructors env indf in 
  if isrec then
    array_map2
      (rec_branch_scheme env isevars ind)
      (dest_subterms mip.mind_recargs) cstrs
  else 
    Array.map (norec_branch_scheme env isevars) cstrs

(******************************************************)
(* B) Building ML like case expressions without types *)

let concl_n env sigma = 
  let rec decrec m c = if m = 0 then (nf_evar sigma c) else 
    match kind_of_term (whd_betadeltaiota env sigma c) with
      | Prod (n,_,c_0) -> decrec (m-1) c_0
      | _                -> failwith "Typing.concl_n"
  in 
  decrec

let count_rec_arg j = 
  let rec crec i = function 
    | [] -> i 
    | ra::l ->
        (match dest_recarg ra with
            Mrec k -> crec (if k=j then (i+1) else i) l
          | _ -> crec i l)
  in 
  crec 0

(* if arity of mispec is (p_bar:P_bar)(a_bar:A_bar)s where p_bar are the
 * K parameters. Then then build_notdep builds the predicate
 * [a_bar:A'_bar](lift k pred) 
 * where A'_bar = A_bar[p_bar <- globargs] *)

let build_dep_pred env sigma indf pred =
  let arsign,_ = get_arity env indf in
  let psign = (Anonymous,None,build_dependent_inductive env indf)::arsign in
  let nar = List.length psign in
  it_mkLambda_or_LetIn_name env (lift nar pred) psign

type ml_case_error =
  | MlCaseAbsurd
  | MlCaseDependent

exception NotInferable of ml_case_error


let pred_case_ml env sigma isrec (IndType (indf,realargs)) (i,ft) =
  let pred =
    let (ind,params) = dest_ind_family indf in
    let (mib,mip) = Inductive.lookup_mind_specif env ind in
    let recargs = dest_subterms mip.mind_recargs in
    if Array.length recargs = 0 then raise (NotInferable MlCaseAbsurd);
    let recargi = recargs.(i) in
    let j = snd ind in (* index of inductive *)
    let nbrec = if isrec then count_rec_arg j recargi else 0 in
    let nb_arg = List.length (recargs.(i)) + nbrec in
    let pred = Evarutil.refresh_universes (concl_n env sigma nb_arg ft) in
    if noccur_between 1 nb_arg pred then 
      lift (-nb_arg) pred
    else 
      raise (NotInferable MlCaseDependent)
  in
  build_dep_pred env sigma indf pred  

(************************************************************************)
(*            Pattern-matching compilation (Cases)                      *)
(************************************************************************)

(************************************************************************)
(* Configuration, errors and warnings *)

open Pp

let mssg_may_need_inversion () =
  str "This pattern-matching is not exhaustive."

let mssg_this_case_cannot_occur () =
  "This pattern-matching is not exhaustive."

(* Utils *)
let make_anonymous_patvars =
  list_tabulate (fun _ -> PatVar (dummy_loc,Anonymous)) 

(* Environment management *)
let push_rels vars env = List.fold_right push_rel vars env

let push_rel_defs =
  List.fold_right (fun (x,d,t) e -> push_rel (x,Some d,t) e)

(* We have x1:t1...xn:tn,xi':ti,y1..yk |- c and re-generalize
   over xi:ti to get x1:t1...xn:tn,xi':ti,y1..yk |- c[xi:=xi'] *)

let regeneralize_rel i k j = if j = i+k then k else if j < i+k then j else j

let rec regeneralize_index i k t = match kind_of_term t with
  | Rel j when j = i+k -> mkRel (k+1)
  | Rel j when j < i+k -> t
  | Rel j when j > i+k -> t
  | _ -> map_constr_with_binders succ (regeneralize_index i) k t

type alias_constr =
  | DepAlias
  | NonDepAlias

let mkSpecialLetInJudge j (na,(deppat,nondeppat,d,t)) =
  { uj_val =
      (match d with
	| DepAlias -> mkLetIn (na,deppat,t,j.uj_val)
	| NonDepAlias ->
	    if (not (dependent (mkRel 1) j.uj_type))
	      or (* A leaf: *) isRel deppat
	    then 
	      (* The body of pat is not needed to type j - see *)
	      (* insert_aliases - and both deppat and nondeppat have the *)
	      (* same type, then one can freely substitute one by the other *)
	      subst1 nondeppat j.uj_val
	    else
	      (* The body of pat is not needed to type j but its value *)
	      (* is dependent in the type of j; our choice is to *)
	      (* enforce this dependency *)
	      mkLetIn (na,deppat,t,j.uj_val));
    uj_type = subst1 deppat j.uj_type }

(**********************************************************************)
(* Structures used in compiling pattern-matching *)
type 'a lifted = int * 'a

let insert_lifted a = (0,a);;

(* The pattern variables for [it] are in [user_ids] and the variables
   to avoid are in [other_ids]. 
*)

type rhs =
    { rhs_env    : env;
      other_ids  : identifier list;
      user_ids   : identifier list;
      rhs_lift   : int;
      it         : rawconstr }

type equation =
    { dependencies : constr lifted list;
      patterns     : cases_pattern list; 
      rhs          : rhs;
      alias_stack  : name list;
      eqn_loc      : loc;
      used         : bool ref;
      tag          : pattern_source }

type matrix = equation list

(* 1st argument of IsInd is the original ind before extracting the summary *)
type tomatch_type =
  | IsInd of types * inductive_type
  | NotInd of constr option * types

type tomatch_status =
  | Pushed of ((constr * tomatch_type) * int list)
  | Alias of (constr * constr * alias_constr * constr)
  | Abstract of rel_declaration

type tomatch_stack = tomatch_status list

(* The type [predicate_signature] types the terms to match and the rhs:

   - [PrLetIn (n,dep,pred)] types a pushed term ([Pushed]), if dep is true,
     the term is dependent, if n<>0 then the type of the pushed term is
     necessarily inductive with n real arguments. Otherwise, it may be
     non inductive, or inductive without real arguments, or inductive
     originating from a subterm in which case real args are not dependent;
     it accounts for n+1 binders if dep or n binders if not dep
   - [PrProd] types abstracted term ([Abstract]); it accounts for one binder
   - [PrCcl] types the right-hand-side
   - Aliases [Alias] have no trace in [predicate_signature]
*)

type predicate_signature =
  | PrLetIn of (int * bool) * predicate_signature
  | PrProd of predicate_signature
  | PrCcl of constr

(* We keep a constr for aliases and a cases_pattern for error message *)

type alias_builder =
  | AliasLeaf
  | AliasConstructor of constructor

type pattern_history =
  | Top
  | MakeAlias of alias_builder * pattern_continuation

and pattern_continuation =
  | Continuation of int * cases_pattern list * pattern_history
  | Result of cases_pattern list

let start_history n = Continuation (n, [], Top)

let initial_history = function Continuation (_,[],Top) -> true | _ -> false

let feed_history arg = function
  | Continuation (n, l, h) when n>=1 ->
      Continuation (n-1, arg :: l, h)
  | Continuation (n, _, _) ->
      anomaly ("Bad number of expected remaining patterns: "^(string_of_int n))
  | Result _ -> 
      anomaly "Exhausted pattern history"

(* This is for non exhaustive error message *)

let rec rawpattern_of_partial_history args2 = function
  | Continuation (n, args1, h) ->
      let args3 = make_anonymous_patvars (n - (List.length args2)) in
      build_rawpattern (List.rev_append args1 (args2@args3)) h
  | Result pl -> pl

and build_rawpattern args = function
  | Top -> args
  | MakeAlias (AliasLeaf, rh) ->
      assert (args = []);
      rawpattern_of_partial_history [PatVar (dummy_loc, Anonymous)] rh
  | MakeAlias (AliasConstructor pci, rh) ->
      rawpattern_of_partial_history
	[PatCstr (dummy_loc, pci, args, Anonymous)] rh

let complete_history = rawpattern_of_partial_history []

(* This is to build glued pattern-matching history and alias bodies *)

let rec simplify_history = function
  | Continuation (0, l, Top) -> Result (List.rev l)
  | Continuation (0, l, MakeAlias (f, rh)) ->
      let pargs = List.rev l in
      let pat = match f with
	| AliasConstructor pci ->
	    PatCstr (dummy_loc,pci,pargs,Anonymous)
	| AliasLeaf -> 
	    assert (l = []);
	    PatVar (dummy_loc, Anonymous) in
      feed_history pat rh
  | h -> h

(* Builds a continuation expecting [n] arguments and building [ci] applied
   to this [n] arguments *)

let push_history_pattern n current cont =
  Continuation (n, [], MakeAlias (current, cont))

(* A pattern-matching problem has the following form:

   env, isevars |- <pred> Cases tomatch of mat end

  where tomatch is some sequence of "instructions" (t1  ... tn)

  and mat is some matrix 
   (p11 ... p1n -> rhs1)
   (    ...            )
   (pm1 ... pmn -> rhsm)

  Terms to match: there are 3 kinds of instructions

  - "Pushed" terms to match are typed in [env]; these are usually just
    Rel(n) except for the initial terms given by user and typed in [env]
  - "Abstract" instructions means an abstraction has to be inserted in the
    current branch to build (this means a pattern has been detected dependent
    in another one and generalisation is necessary to ensure well-typing)
  - "Alias" instructions means an alias has to be inserted (this alias
    is usually removed at the end, except when its type is not the
    same as the type of the matched term from which it comes -
    typically because the inductive types are "real" parameters)

  Right-hand-sides:

  They consist of a raw term to type in an environment specific to the
  clause they belong to: the names of declarations are those of the
  variables present in the patterns. Therefore, they come with their
  own [rhs_env] (actually it is the same as [env] except for the names
  of variables).

*)
type pattern_matching_problem =
    { env      : env;
      isevars  : evar_defs;
      pred     : predicate_signature option;
      tomatch  : tomatch_stack;
      history  : pattern_continuation;
      mat      : matrix;
      caseloc  : loc;
      typing_function: type_constraint -> env -> rawconstr -> unsafe_judgment }

(*--------------------------------------------------------------------------*
 * A few functions to infer the inductive type from the patterns instead of *
 * checking that the patterns correspond to the ind. type of the            *
 * destructurated object. Allows type inference of examples like            *
 *  [n]Cases n of O => true | _ => false end                                *
 *--------------------------------------------------------------------------*)

(* Computing the inductive type from the matrix of patterns *)

let rec find_row_ind = function
    [] -> None
  | PatVar _ :: l -> find_row_ind l
  | PatCstr(loc,c,_,_) :: _ -> Some (loc,c)

exception NotCoercible

let inh_coerce_to_ind isevars env tmloc ty tyi =
  let (mib,mip) = Inductive.lookup_mind_specif env tyi in
  let (ntys,_) = splay_prod env (evars_of isevars) mip.mind_nf_arity in
  let hole_source = match tmloc with 
    | Some loc -> fun i -> (loc, TomatchTypeParameter (tyi,i))
    | None -> fun _ -> (dummy_loc, InternalHole) in
   let (_,evarl,_) =
    List.fold_right
      (fun (na,ty) (env,evl,n) ->
	 (push_rel (na,None,ty) env,
	    (new_isevar isevars env (hole_source n) ty)::evl,n+1))
      ntys (env,[],1) in
  let expected_typ = applist (mkInd tyi,evarl) in
     (* devrait être indifférent d'exiger leq ou pas puisque pour 
        un inductif cela doit être égal *)
  if the_conv_x_leq env isevars expected_typ ty then ty
  else raise NotCoercible

(* We do the unification for all the rows that contain
 * constructor patterns. This is what we do at the higher level of patterns.
 * For nested patterns, we do this unif when we ``expand'' the matrix, and we
 * use the function above.
 *)

let unify_tomatch_with_patterns isevars env tmloc typ = function
  | Some (cloc,(cstr,_ as c)) ->
      (let tyi = inductive_of_constructor c in
       try 
	 let indtyp = inh_coerce_to_ind isevars env tmloc typ tyi in
	 IsInd (typ,find_rectype env (evars_of isevars) typ)
       with NotCoercible ->
	 (* 2 cases : Not the right inductive or not an inductive at all *)
	 try
	   IsInd (typ,find_rectype env (evars_of isevars) typ)
             (* will try to coerce later in check_and_adjust_constructor.. *)
	 with Not_found ->
	   NotInd (None,typ))
	     (* error will be detected in check_all_variables *)
  | None -> 
      try IsInd (typ,find_rectype env (evars_of isevars) typ)
      with Not_found -> NotInd (None,typ)

let coerce_row typing_fun isevars env cstropt tomatch =
  let j = typing_fun empty_tycon env tomatch in
  let typ = body_of_type j.uj_type in
  let loc = loc_of_rawconstr tomatch in
  let t = unify_tomatch_with_patterns isevars env (Some loc) typ cstropt in
  (j.uj_val,t)

let coerce_to_indtype typing_fun isevars env matx tomatchl =
  let pats = List.map (fun r ->  r.patterns) matx in
  let matx' = match matrix_transpose pats with
    | [] -> List.map (fun _ -> None) tomatchl (* no patterns at all *)
    | m -> List.map find_row_ind m in
  List.map2 (coerce_row typing_fun isevars env) matx' tomatchl

(************************************************************************)
(* Utils *)

   (* extract some ind from [t], possibly coercing from constructors in [tm] *)
let to_mutind env isevars tm c t =
  match c with
    | Some body -> NotInd (c,t)
    | None -> unify_tomatch_with_patterns isevars env None t (find_row_ind tm)

let type_of_tomatch = function
  | IsInd (t,_) -> t
  | NotInd (_,t) -> t

let mkDeclTomatch na = function
  | IsInd (t,_) -> (na,None,t)
  | NotInd (c,t) -> (na,c,t)

let map_tomatch_type f = function
  | IsInd (t,ind) -> IsInd (f t,map_inductive_type f ind)
  | NotInd (c,t) -> NotInd (option_app f c, f t)

let liftn_tomatch_type n depth = map_tomatch_type (liftn n depth)
let lift_tomatch_type n = liftn_tomatch_type n 1

let lift_tomatch n ((current,typ),info) =
  ((lift n current,lift_tomatch_type n typ),info)

(**********************************************************************)
(* Utilities on patterns *)

let current_pattern eqn =
  match eqn.patterns with
    | pat::_ -> pat
    | [] -> anomaly "Empty list of patterns"

let alias_of_pat = function
  | PatVar (_,name) -> name
  | PatCstr(_,_,_,name) -> name

let unalias_pat = function
  | PatVar (c,name) as p ->
      if name = Anonymous then p else PatVar (c,Anonymous)
  | PatCstr(a,b,c,name) as p ->
      if name = Anonymous then p else PatCstr (a,b,c,Anonymous)

let remove_current_pattern eqn =
  match eqn.patterns with
    | pat::pats ->
	{ eqn with
	    patterns = pats;
	    alias_stack = alias_of_pat pat :: eqn.alias_stack }
    | [] -> anomaly "Empty list of patterns"

let prepend_pattern tms eqn = {eqn with patterns = tms@eqn.patterns }

(**********************************************************************)
(* Dealing with regular and default patterns *)
let is_regular eqn = eqn.tag = RegularPat

let lower_pattern_status = function
  | RegularPat -> DefaultPat 0
  | DefaultPat n -> DefaultPat (n+1)

let pattern_status pats =
  if array_exists ((=) RegularPat) pats then RegularPat
  else 
    let min =
      Array.fold_right
	(fun pat n -> match pat with
	   | DefaultPat i when i<n -> i
	   | _ -> n)
	pats 0 in
    DefaultPat min

(**********************************************************************)
(* Well-formedness tests *)
(* Partial check on patterns *)

exception NotAdjustable

let rec adjust_local_defs loc = function
  | (pat :: pats, (_,None,_) :: decls) ->
      pat :: adjust_local_defs loc (pats,decls)
  | (pats, (_,Some _,_) :: decls) ->
      PatVar (loc, Anonymous) :: adjust_local_defs loc (pats,decls)
  | [], [] -> []
  | _ -> raise NotAdjustable

let check_and_adjust_constructor ind cstrs = function 
  | PatVar _ as pat -> pat
  | PatCstr (loc,((_,i) as cstr),args,alias) as pat ->
      (* Check it is constructor of the right type *)
      let ind' = inductive_of_constructor cstr in
      if ind' = ind then
	(* Check the constructor has the right number of args *)
	let ci = cstrs.(i-1) in
	let nb_args_constr = ci.cs_nargs in
	if List.length args = nb_args_constr then pat
	else
	  try 
	    let args' = adjust_local_defs loc (args, List.rev ci.cs_args)
	    in PatCstr (loc, cstr, args', alias)
	  with NotAdjustable ->
	    error_wrong_numarg_constructor_loc loc cstr nb_args_constr
      else
	(* Try to insert a coercion *)
	try
	  Coercion.inh_pattern_coerce_to loc pat ind' ind
	with Not_found -> 
	  error_bad_constructor_loc loc cstr ind

let check_all_variables typ mat =
  List.iter
    (fun eqn -> match current_pattern eqn with
       | PatVar (_,id) -> ()
       | PatCstr (loc,cstr_sp,_,_) ->
	   error_bad_pattern_loc loc cstr_sp typ)
    mat

let check_unused_pattern env eqn =
  if not !(eqn.used) then 
    raise_pattern_matching_error
      (eqn.eqn_loc, env, UnusedClause eqn.patterns)

let set_used_pattern eqn = eqn.used := true

let extract_rhs pb =
  match pb.mat with 
    | [] -> errorlabstrm "build_leaf" (mssg_may_need_inversion())
    | eqn::_ ->
	set_used_pattern eqn;
	eqn.tag, eqn.rhs

(**********************************************************************)
(* Functions to deal with matrix factorization *)

let occur_in_rhs na rhs =
  match na with
    | Anonymous -> false
    | Name id -> occur_rawconstr id rhs.it

let is_dep_patt eqn = function
  | PatVar (_,name) -> occur_in_rhs name eqn.rhs
  | PatCstr _ -> true

let dependencies_in_rhs nargs eqns =
  if eqns = [] then list_tabulate (fun _ -> false) nargs (* Only "_" patts *)
  else
  let deps = List.map (fun (tms,eqn) -> List.map (is_dep_patt eqn) tms) eqns in
  let columns = matrix_transpose deps in
  List.map (List.exists ((=) true)) columns

let dependent_decl a = function
  | (na,None,t) -> dependent a t
  | (na,Some c,t) -> dependent a t || dependent a c

(* Computing the matrix of dependencies *)

(* We are in context d1...dn |- and [find_dependencies k 1 nextlist]
   computes for declaration [k+1] in which of declarations in
   [nextlist] (which corresponds to d(k+2)...dn) it depends;
   declarations are expressed by index, e.g. in dependency list
   [n-2;1], [1] points to [dn] and [n-2] to [d3] *)

let rec find_dependency_list k n = function
  | [] -> []
  | (used,tdeps,d)::rest -> 
      let deps = find_dependency_list k (n+1) rest in
      if used && dependent_decl (mkRel n) d
      then list_add_set (List.length rest + 1) (list_union deps tdeps)
      else deps

let find_dependencies is_dep_or_cstr_in_rhs d (k,nextlist) =
  let deps = find_dependency_list k 1 nextlist in
  if is_dep_or_cstr_in_rhs || deps <> []
  then (k-1,(true ,deps,d)::nextlist)
  else (k-1,(false,[]  ,d)::nextlist)

let find_dependencies_signature deps_in_rhs typs =
  let k = List.length deps_in_rhs in
  let _,l = List.fold_right2 find_dependencies deps_in_rhs typs (k,[]) in
  List.map (fun (_,deps,_) -> deps) l

(******)

(* A Pushed term to match has just been substituted by some
   constructor t = (ci x1...xn) and the terms x1 ... xn have been added to
   match 

   - all terms to match and to push (dependent on t by definition)
     must have (Rel depth) substituted by t and Rel's>depth lifted by n
   - all pushed terms to match (non dependent on t by definition) must
     be lifted by n

  We start with depth=1
*)

let regeneralize_index_tomatch n =
  let rec genrec depth = function
  | [] -> []
  | Pushed ((c,tm),l)::rest ->
      let c = regeneralize_index n depth c in
      let tm = map_tomatch_type (regeneralize_index n depth) tm in
      let l = List.map (regeneralize_rel n depth) l in
      Pushed ((c,tm),l)::(genrec depth rest)
  | Alias (c1,c2,d,t)::rest ->
      Alias (regeneralize_index n depth c1,c2,d,t)::(genrec depth rest)
  | Abstract d::rest ->
      Abstract (map_rel_declaration (regeneralize_index n depth) d)
      ::(genrec (depth+1) rest) in
  genrec 0

let rec replace_term n c k t = 
  if t = mkRel (n+k) then lift k c
  else map_constr_with_binders succ (replace_term n c) k t

let replace_tomatch n c =
  let rec replrec depth = function
  | [] -> []
  | Pushed ((b,tm),l)::rest ->
      let b = replace_term n c depth b in
      let tm = map_tomatch_type (replace_term n c depth) tm in
      List.iter (fun i -> if i=n+depth then anomaly "replace_tomatch") l;
      Pushed ((b,tm),l)::(replrec depth rest)
  | Alias (c1,c2,d,t)::rest ->
      Alias (replace_term n c depth c1,c2,d,t)::(replrec depth rest)
  | Abstract d::rest ->
      Abstract (map_rel_declaration (replace_term n c depth) d)
      ::(replrec (depth+1) rest) in
  replrec 0

let liftn_rel_declaration n k = map_rel_declaration (liftn n k)
let substnl_rel_declaration sigma k = map_rel_declaration (substnl sigma k)

let rec liftn_tomatch_stack n depth = function
  | [] -> []
  | Pushed ((c,tm),l)::rest ->
      let c = liftn n depth c in
      let tm = liftn_tomatch_type n depth tm in
      let l = List.map (fun i -> if i<depth then i else i+n) l in
      Pushed ((c,tm),l)::(liftn_tomatch_stack n depth rest)
  | Alias (c1,c2,d,t)::rest ->
      Alias (liftn n depth c1,liftn n depth c2,d,liftn n depth t)
      ::(liftn_tomatch_stack n depth rest)
  | Abstract d::rest ->
      Abstract (map_rel_declaration (liftn n depth) d)
      ::(liftn_tomatch_stack n (depth+1) rest)


let lift_tomatch_stack n = liftn_tomatch_stack n 1

(* if [current] has type [I(p1...pn u1...um)] and we consider the case
   of constructor [ci] of type [I(p1...pn u'1...u'm)], then the
   default variable [name] is expected to have which type?
   Rem: [current] is [(Rel i)] except perhaps for initial terms to match *)

(************************************************************************)
(* Some heuristics to get names for variables pushed in pb environment *)
(* Typical requirement:

   [Cases y of (S (S x)) => x | x => x end] should be compiled into
   [Cases y of O => y | (S n) => Cases n of O => y | (S x) => x end end]

   and [Cases y of (S (S n)) => n | n => n end] into 
   [Cases y of O => y | (S n0) => Cases n0 of O => y | (S n) => n end end]

  i.e. user names should be preserved and created names should not
  interfere with user names *)

let merge_name get_name obj = function
  | Anonymous -> get_name obj
  | na -> na

let merge_names get_name = List.map2 (merge_name get_name)

let get_names env sign eqns =
  let names1 = list_tabulate (fun _ -> Anonymous) (List.length sign) in
  (* If any, we prefer names used in pats, from top to bottom *)
  let names2 = 
    List.fold_right
      (fun (pats,eqn) names -> merge_names alias_of_pat pats names)
      eqns names1 in
  (* Otherwise, we take names from the parameters of the constructor but
     avoiding conflicts with user ids *)
  let allvars =
    List.fold_left (fun l (_,eqn) -> list_union l eqn.rhs.other_ids) [] eqns in
  let names4,_ =
    List.fold_left2
      (fun (l,avoid) d na ->
	 let na =
	   merge_name
	     (fun (na,_,t) -> Name (next_name_away (named_hd env t na) avoid))
	     d na 
	 in
         (na::l,(out_name na)::avoid))
      ([],allvars) (List.rev sign) names2 in
  names4

(************************************************************************)
(* Recovering names for variables pushed to the rhs' environment *)

let recover_alias_names get_name = List.map2 (fun x (_,c,t) ->(get_name x,c,t))

let push_rels_eqn sign eqn =
  {eqn with rhs = {eqn.rhs with rhs_env = push_rels sign eqn.rhs.rhs_env} }

let push_rels_eqn_with_names sign eqn =
  let pats = List.rev (list_firstn (List.length sign) eqn.patterns) in
  let sign = recover_alias_names alias_of_pat pats sign in
  push_rels_eqn sign eqn

let build_aliases_context env sigma names allpats pats =
  (* pats is the list of bodies to push as an alias *)
  (* They all are defined in env and we turn them into a sign *)
  (* cuts in sign need to be done in allpats *)
  let rec insert env sign1 sign2 n newallpats oldallpats = function
    | (deppat,_,_,_)::pats, Anonymous::names when not (isRel deppat) ->
        (* Anonymous leaves must be considered named and treated in the *)
        (* next clause because they may occur in implicit arguments *)
	insert env sign1 sign2
	  n newallpats (List.map List.tl oldallpats) (pats,names)
    | (deppat,nondeppat,d,t)::pats, na::names ->
	let nondeppat = lift n nondeppat in
	let deppat = lift n deppat in
	let newallpats =
	  List.map2 (fun l1 l2 -> List.hd l2::l1) newallpats oldallpats in
	let oldallpats = List.map List.tl oldallpats in
	let u = Retyping.get_type_of env sigma deppat in
	let decl = (na,Some deppat,t) in
	let a = (deppat,nondeppat,d,t) in
	insert (push_rel decl env) (decl::sign1) ((na,a)::sign2) (n+1) 
	  newallpats oldallpats (pats,names)
    | [], [] -> newallpats, sign1, sign2, env
    | _ -> anomaly "Inconsistent alias and name lists" in
  let allpats = List.map (fun x -> [x]) allpats
  in insert env [] [] 0 (List.map (fun _ -> []) allpats) allpats (pats, names)

let insert_aliases_eqn sign eqnnames alias_rest eqn =
  let thissign = List.map2 (fun na (_,c,t) -> (na,c,t)) eqnnames sign in
  { eqn with
      alias_stack = alias_rest;
      rhs = {eqn.rhs with rhs_env = push_rels thissign eqn.rhs.rhs_env } }

let insert_aliases env sigma alias eqns =
  (* Là, y a une faiblesse, si un alias est utilisé dans un cas par *)
  (* défaut présent mais inutile, ce qui est le cas général, l'alias *)
  (* est introduit même s'il n'est pas utilisé dans les cas réguliers *)
  let eqnsnames = List.map (fun eqn -> List.hd eqn.alias_stack) eqns in
  let alias_rests = List.map (fun eqn -> List.tl eqn.alias_stack) eqns in
  (* names2 takes the meet of all needed aliases *)
  let names2 = 
    List.fold_right (merge_name (fun x -> x)) eqnsnames Anonymous in
  (* Only needed aliases are kept by build_aliases_context *)
  let eqnsnames, sign1, sign2, env =
    build_aliases_context env sigma [names2] eqnsnames [alias] in
  let eqns = list_map3 (insert_aliases_eqn sign1) eqnsnames alias_rests eqns in
  sign2, env, eqns

(**********************************************************************)
(* Functions to deal with elimination predicate *)

exception Occur
let noccur_between_without_evar n m term = 
  let rec occur_rec n c = match kind_of_term c with
    | Rel p       -> if n<=p && p<n+m then raise Occur
    | Evar (_,cl) -> ()
    | _             -> iter_constr_with_binders succ occur_rec n c
  in 
  try occur_rec n term; true with Occur -> false

(* Infering the predicate *)
let prepare_unif_pb typ cs =
  let n = List.length (assums_of_rel_context cs.cs_args) in

  (* We may need to invert ci if its parameters occur in typ *)
  let typ' =
    if noccur_between_without_evar 1 n typ then lift (-n) typ
    else (* TODO4-1 *)
      error "Inference of annotation not yet implemented in this case" in
  let args = extended_rel_list (-n) cs.cs_args in
  let ci = applist (mkConstruct cs.cs_cstr, cs.cs_params@args) in

  (* This is the problem: finding P s.t. cs_args |- (P realargs ci) = typ' *)
  (Array.map (lift (-n)) cs.cs_concl_realargs, ci, typ')


(* Infering the predicate *)
(*
The problem to solve is the following:

We match Gamma |- t : I(u01..u0q) against the following constructors:

  Gamma, x11...x1p1 |- C1(x11..x1p1) : I(u11..u1q)
   ...
  Gamma, xn1...xnpn |- Cn(xn1..xnp1) : I(un1..unq)

Assume the types in the branches are the following

  Gamma, x11...x1p1 |- branch1 : T1
   ...
  Gamma, xn1...xnpn |- branchn : Tn

Assume the type of the global case expression is Gamma |- T

The predicate has the form phi = [y1..yq][z:I(y1..yq)]? and must satisfy
the following n+1 equations:

  Gamma, x11...x1p1 |- (phi u11..u1q (C1 x11..x1p1))  =  T1
   ...
  Gamma, xn1...xnpn |- (phi un1..unq (Cn xn1..xnpn))  =  Tn
  Gamma             |- (phi u01..u0q t)               =  T

Some hints:

- Clearly, if xij occurs in Ti, then, a "Cases z of (Ci xi1..xipi) => ..."
  should be inserted somewhere in Ti.

- If T is undefined, an easy solution is to insert a "Cases z of (Ci
  xi1..xipi) => ..." in front of each Ti

- Otherwise, T1..Tn and T must be step by step unified, if some of them
  diverge, then try to replace the diverging subterm by one of y1..yq or z.

- The main problem is what to do when an existential variables is encountered

let prepare_unif_pb typ cs =
  let n = cs.cs_nargs in
  let _,p = decompose_prod_n n typ in
  let ci = build_dependent_constructor cs in
  (* This is the problem: finding P s.t. cs_args |- (P realargs ci) = p *)
  (n, cs.cs_concl_realargs, ci, p)

let eq_operator_lift k (n,n') = function
  | OpRel p, OpRel p' when p > k & p' > k ->
      if p < k+n or p' < k+n' then false else p - n = p' - n'
  | op, op' -> op = op'

let rec transpose_args n =
  if n=0 then []
  else
    (Array.map (fun l -> List.hd l) lv)::
    (transpose_args (m-1) (Array.init (fun l -> List.tl l)))

let shift_operator k = function OpLambda _ | OpProd _ -> k+1 | _ -> k

let reloc_operator (k,n) = function OpRel p when p > k -> 
let rec unify_clauses k pv =
  let pv'= Array.map (fun (n,sign,_,p) -> n,splay_constr (whd_betaiotaevar (push_rels (List.rev sign) env) (evars_of isevars)) p) pv in
  let n1,op1 = let (n1,(op1,args1)) = pv'.(0) in n1,op1 in
  if Array.for_all (fun (ni,(opi,_)) -> eq_operator_lift k (n1,ni) (op1,opi)) pv'
  then
    let argvl = transpose_args (List.length args1) pv' in
    let k' = shift_operator k op1 in
    let argl = List.map (unify_clauses k') argvl in
    gather_constr (reloc_operator (k,n1) op1) argl
*)

let abstract_conclusion typ cs =
  let n = List.length (assums_of_rel_context cs.cs_args) in
  let (sign,p) = decompose_prod_n n typ in
  lam_it p sign

let infer_predicate loc env isevars typs cstrs indf =
  let (mis,_) = dest_ind_family indf in
  (* Il faudra substituer les isevars a un certain moment *)
  if Array.length cstrs = 0 then (* "TODO4-3" *)
    error "Inference of annotation for empty inductive types not implemented"
  else
    (* Empiric normalization: p may depend in a irrelevant way on args of the*)
    (* cstr as in [c:{_:Alpha & Beta}] Cases c of (existS a b)=>(a,b) end *)
    let typs =
      Array.map (local_strong (whd_betaevar empty_env (evars_of isevars))) typs
    in
    let eqns = array_map2 prepare_unif_pb typs cstrs in
    (* First strategy: no dependencies at all *)
(*    let (cclargs,_,typn) = eqns.(mis_nconstr mis -1) in*)
    let (sign,_) = get_arity env indf in
    let mtyp =
      if array_exists is_Type typs then
	(* Heuristic to avoid comparison between non-variables algebric univs*)
	new_Type ()
      else
	mkExistential isevars env (loc, CasesType)
    in
    if array_for_all (fun (_,_,typ) -> the_conv_x_leq env isevars typ mtyp) eqns
    then
      (* Non dependent case -> turn it into a (dummy) dependent one *)
      let sign = (Anonymous,None,build_dependent_inductive env indf)::sign in
      let pred = it_mkLambda_or_LetIn (lift (List.length sign) mtyp) sign in
      (true,pred) (* true = dependent -- par défaut *)
    else
(*
      let s = get_sort_of env (evars_of isevars) typs.(0) in
      let predpred = it_mkLambda_or_LetIn (mkSort s) sign in
      let caseinfo = make_default_case_info mis in
      let brs = array_map2 abstract_conclusion typs cstrs in
      let predbody = mkCase (caseinfo, (nf_betaiota predpred), mkRel 1, brs) in
      let pred = it_mkLambda_or_LetIn (lift (List.length sign) mtyp) sign in
*)
      (* "TODO4-2" *)
      (* We skip parameters *)
      let cis = 
	Array.map
	  (fun cs ->
	     applist (mkConstruct cs.cs_cstr, extended_rel_list 0 cs.cs_args))
	  cstrs in
      let ct = array_map2 (fun ci (_,_,t) -> (ci,t)) cis eqns in
      raise_pattern_matching_error (loc,env, CannotInferPredicate ct)
(*
      (true,pred)
*)

(* Propagation of user-provided predicate through compilation steps *)

let rec map_predicate f k = function
  | PrCcl ccl -> PrCcl (f k ccl)
  | PrProd pred ->
      PrProd (map_predicate f (k+1) pred)
  | PrLetIn ((nargs,dep as tm),pred) ->
      let k' = nargs + (if dep then 1 else 0) in
      PrLetIn (tm, map_predicate f (k+k') pred)

let liftn_predicate n = map_predicate (liftn n)

let lift_predicate n = liftn_predicate n 1

let regeneralize_index_predicate n = map_predicate (regeneralize_index n) 0

let substnl_predicate sigma = map_predicate (substnl sigma)

(* This is parallel bindings *)
let subst_predicate (args,copt) pred =
  let sigma = match copt with
    | None -> List.rev args
    | Some c -> c::(List.rev args) in
  substnl_predicate sigma 0 pred

let specialize_predicate_var (cur,typ) = function
  | PrProd _ | PrCcl _ ->
     anomaly "specialize_predicate_var: a pattern-variable must be pushed"
  | PrLetIn ((0,dep),pred) ->
      subst_predicate ([],if dep then Some cur else None) pred
  | PrLetIn ((_,dep),pred) ->
      (match typ with
        | IsInd (_,IndType (_,realargs)) ->
            subst_predicate (realargs,if dep then Some cur else None) pred
        | _ -> anomaly "specialize_predicate_var")

let ungeneralize_predicate = function
  | PrLetIn _ | PrCcl _ -> anomaly "ungeneralize_predicate: expects a product"
  | PrProd pred -> pred

(*****************************************************************************)
(* We have pred = [X:=realargs;x:=c]P typed in Gamma1, x:I(realargs), Gamma2 *)
(* and we want to abstract P over y:t(x) typed in the same context to get    *)
(*                                                                           *)
(*    pred' = [X:=realargs;x':=c](y':t(x'))P[y:=y']                          *)
(*                                                                           *)
(* We first need to lift t(x) s.t. it is typed in Gamma, X:=rargs, x'        *)
(* then we have to replace x by x' in t(x) and y by y' in P                  *)
(*****************************************************************************)
let generalize_predicate c ny d = function
  | PrLetIn ((nargs,dep as tm),pred) ->
      if not dep then anomaly "Undetected dependency";
      let p = nargs + 1 in
      let pred = lift_predicate 1 pred in
      let pred = regeneralize_index_predicate (ny+p+1) pred in
      PrLetIn (tm, PrProd pred)
  | PrProd _ | PrCcl _ ->
      anomaly "generalize_predicate: expects a non trivial pattern"

let rec extract_predicate l = function
  | pred, Alias (deppat,nondeppat,_,_)::tms ->
      let tms' = match kind_of_term nondeppat with
        | Rel i -> replace_tomatch i deppat tms
        | _ -> (* initial terms are not dependent *) tms in
      extract_predicate l (pred,tms')
  | PrProd pred, Abstract d'::tms ->
      let d' = map_rel_declaration (lift (List.length l)) d' in
      substl l (mkProd_or_LetIn d' (extract_predicate [] (pred,tms)))
  | PrLetIn ((0,dep),pred), Pushed ((cur,_),_)::tms ->
      extract_predicate (if dep then cur::l else l) (pred,tms)
  | PrLetIn ((_,dep),pred), Pushed ((cur,IsInd (_,(IndType(_,realargs)))),_)::tms ->
      let l = List.rev realargs@l in
      extract_predicate (if dep then cur::l else l) (pred,tms)
  | PrCcl ccl, [] ->
      substl l ccl
  | _ -> anomaly"extract_predicate: predicate inconsistent with terms to match"

let abstract_predicate env sigma indf cur tms = function
  | (PrProd _ | PrCcl _) -> anomaly "abstract_predicate: must be some LetIn"
  | PrLetIn ((nrealargs,dep),pred) ->
      let sign = make_arity_signature env true indf in
      (* n is the number of real args + 1 *)
      let n = List.length sign in
      let tms = lift_tomatch_stack n tms in
      let tms =
        match kind_of_term cur with
          | Rel i -> regeneralize_index_tomatch (i+n) tms
          | _ -> (* Initial case *) tms in
      (* Depending on whether the predicate is dependent or not, and has real
         args or not, we lift it to make room for [sign] *)
      (* Even if not intrinsically dep, we move the predicate into a dep one *)
      let k =
        if nrealargs = 0 & n <> 1 then 
          (* Real args were not considered *) if dep then n-1 else n
        else
          (* Real args are OK *) if dep then 0 else 1 in
      let pred = lift_predicate k pred in
      let pred = extract_predicate [] (pred,tms) in
      (true, it_mkLambda_or_LetIn_name env pred sign)

let rec known_dependent = function
  | None -> false
  | Some (PrLetIn ((_,dep),_)) -> dep
  | Some (PrCcl _) -> false
  | Some (PrProd _) ->
      anomaly "known_dependent: can only be used when patterns remain"

(* [expand_arg] is used by [specialize_predicate]
   it replaces gamma, x1...xn, x1...xk |- pred
   by gamma, x1...xn, x1...xk-1 |- [X=realargs,xk=xk]pred (if dep) or
   by gamma, x1...xn, x1...xk-1 |- [X=realargs]pred (if not dep) *)

let expand_arg n alreadydep (na,t) deps (k,pred) =
  (* current can occur in pred even if the original problem is not dependent *)
  let dep = deps <> [] || alreadydep in
  let pred = if dep then pred else lift_predicate (-1) pred in
  (* There is no dependency in realargs for subpattern *)
  (k-1, PrLetIn ((0,dep), pred))


(*****************************************************************************)
(* pred = [X:=realargs;x:=c]P types the following problem:                   *)
(*                                                                           *)
(*  Gamma |- Cases Pushed(c:I(realargs)) rest of...end: pred                 *)
(*                                                                           *)
(* where the branch with constructor Ci:(x1:T1)...(xn:Tn)->I(realargsi)      *)
(* is considered. Assume each Ti is some Ii(argsi).                          *)
(* We let e=Ci(x1,...,xn) and replace pred by                                *)
(*                                                                           *)
(* pred' = [X1:=rargs1,x1:=x1']...[Xn:=rargsn,xn:=xn'](P[X:=realargsi;x:=e]) *)
(*                                                                           *)
(* s.t Gamma,x1'..xn' |- Cases Pushed(x1')..Pushed(xn') rest of...end: pred' *)
(*                                                                           *)
(*****************************************************************************)
let specialize_predicate tomatchs deps cs = function
  | (PrProd _ | PrCcl _) ->
      anomaly "specialize_predicate: a matched pattern must be pushed"
  | PrLetIn ((nrealargs,isdep),pred) ->
      (* Assume some gamma st: gamma, (X,x:=realargs,copt) |- pred *)
      let k = nrealargs + (if isdep then 1 else 0) in
      (* We adjust pred st: gamma, x1..xn, (X,x:=realargs,copt) |- pred' *)
      let n = cs.cs_nargs in
      let pred' = liftn_predicate n (k+1) pred in
      let argsi = if nrealargs <> 0 then Array.to_list cs.cs_concl_realargs else [] in
      let copti = if isdep then Some (build_dependent_constructor cs) else None in
      (* The substituends argsi, copti are all defined in gamma, x1...xn *)
      (* We need _parallel_ bindings to get gamma, x1...xn |- pred'' *)
      let pred'' = subst_predicate (argsi, copti) pred' in
      (* We adjust pred st: gamma, x1..xn, x1..xn |- pred'' *)
      let pred''' = liftn_predicate n (n+1) pred'' in
      (* We finally get gamma,x1..xn |- [X1,x1:=R1,x1]..[Xn,xn:=Rn,xn]pred'''*)
      snd (List.fold_right2 (expand_arg n isdep) tomatchs deps (n,pred'''))

let find_predicate loc env isevars p typs cstrs current
  (IndType (indf,realargs)) tms =
  let (dep,pred) =
    match p with
      | Some p -> abstract_predicate env (evars_of isevars) indf current tms p
      | None -> infer_predicate loc env isevars typs cstrs indf in
  let typ = whd_beta (applist (pred, realargs)) in
  if dep then
    (pred, whd_beta (applist (typ, [current])), new_Type ())
  else
    (pred, typ, new_Type ())

(************************************************************************)
(* Sorting equations by constructor *)

type inversion_problem =
  (* the discriminating arg in some Ind and its order in Ind *)
  | Incompatible of int * (int * int)
  | Constraints of (int * constr) list

let solve_constraints constr_info indt =
  (* TODO *)
  Constraints []

let rec irrefutable env = function
  | PatVar (_,name) -> true
  | PatCstr (_,cstr,args,_) ->
      let ind = inductive_of_constructor cstr in
      let (_,mip) = Inductive.lookup_mind_specif env ind in
      let one_constr = Array.length mip.mind_user_lc = 1 in
      one_constr & List.for_all (irrefutable env) args

let first_clause_irrefutable env = function
  | eqn::mat -> List.for_all (irrefutable env) eqn.patterns
  | _ -> false

let group_equations pb mind current cstrs mat =
  let mat =
    if first_clause_irrefutable pb.env mat then [List.hd mat] else mat in
  let brs = Array.create (Array.length cstrs) [] in
  let only_default = ref true in
  let _ =
    List.fold_right (* To be sure it's from bottom to top *)
      (fun eqn () ->
	 let rest = remove_current_pattern eqn in
	 let pat = current_pattern eqn in
	 match check_and_adjust_constructor mind cstrs pat with 
	   | PatVar (_,name) -> 
	       (* This is a default clause that we expand *)
	       for i=1 to Array.length cstrs do
		 let args = make_anonymous_patvars cstrs.(i-1).cs_nargs in
		 let rest = {rest with tag = lower_pattern_status rest.tag} in
		 brs.(i-1) <- (args, rest) :: brs.(i-1)
	       done
	   | PatCstr (loc,((_,i) as cstr),args,_) as pat ->
	       (* This is a regular clause *)
	       only_default := false;
	       brs.(i-1) <- (args,rest) :: brs.(i-1)) mat () in
  (brs,!only_default)

(************************************************************************)
(* Here starts the pattern-matching compilation algorithm *)

(* Abstracting over dependent subterms to match *)
let rec generalize_problem pb current = function
  | [] -> pb
  | i::l ->
      let d = map_rel_declaration (lift i) (Environ.lookup_rel i pb.env) in
      let pb' = generalize_problem pb current l in
      let tomatch = lift_tomatch_stack 1 pb'.tomatch in
      let tomatch = regeneralize_index_tomatch (i+1) tomatch in
      { pb with
	  tomatch = Abstract d :: tomatch;
          pred = option_app (generalize_predicate current i d) pb'.pred }

(* No more patterns: typing the right-hand-side of equations *)
let build_leaf pb =
  let tag, rhs = extract_rhs pb in
  let tycon = match pb.pred with
    | None -> empty_tycon
    | Some (PrCcl typ) -> mk_tycon typ
    | Some _ -> anomaly "not all parameters of pred have been consumed" in
  tag, pb.typing_function tycon rhs.rhs_env rhs.it

(* Building the sub-problem when all patterns are variables *)
let shift_problem (current,t) pb =
  {pb with
     tomatch = Alias (current,current,NonDepAlias,type_of_tomatch t)::pb.tomatch;
     pred = option_app (specialize_predicate_var (current,t)) pb.pred;
     history = push_history_pattern 0 AliasLeaf pb.history;
     mat = List.map remove_current_pattern pb.mat }

(* Building the sub-pattern-matching problem for a given branch *)
let build_branch current deps pb eqns const_info =
  (* We remember that we descend through a constructor *)
  let alias_type =
    if Array.length const_info.cs_concl_realargs = 0
      & not (known_dependent pb.pred) & deps = []
    then
      NonDepAlias
    else 
      DepAlias
  in
  let partialci =
    applist (mkConstruct const_info.cs_cstr, const_info.cs_params) in
  let history = 
    push_history_pattern const_info.cs_nargs
      (AliasConstructor const_info.cs_cstr)
      pb.history in

  (* We find matching clauses *)
  let cs_args = (*assums_of_rel_context*) const_info.cs_args in
  let names = get_names pb.env cs_args eqns in
  let submat = List.map (fun (tms,eqn) -> prepend_pattern tms eqn) eqns in
  if submat = [] then
    raise_pattern_matching_error
      (dummy_loc, pb.env, NonExhaustive (complete_history history));
  let typs = List.map2 (fun (_,c,t) na -> (na,c,t)) cs_args names in
  let _,typs',_ =
    List.fold_right
      (fun (na,c,t as d) (env,typs,tms) ->
	 let tm1 = List.map List.hd tms in
	 let tms = List.map List.tl tms in
 	 (push_rel d env, (na,to_mutind env pb.isevars tm1 c t)::typs,tms))
      typs (pb.env,[],List.map fst eqns) in

  let dep_sign =
    find_dependencies_signature
      (dependencies_in_rhs const_info.cs_nargs eqns) (List.rev typs) in

  (* The dependent term to subst in the types of the remaining UnPushed 
     terms is relative to the current context enriched by topushs *)
  let ci = build_dependent_constructor const_info in

  (* We replace [(mkRel 1)] by its expansion [ci] *)
  (* and context "Gamma = Gamma1, current, Gamma2" by "Gamma;typs;curalias" *)
  (* This is done in two steps : first from "Gamma |- tms" *)
  (* into  "Gamma; typs; curalias |- tms" *)
  let tomatch = lift_tomatch_stack const_info.cs_nargs pb.tomatch in

  let currents =
    list_map2_i
      (fun i (na,t) deps -> Pushed ((mkRel i, lift_tomatch_type i t), deps))
      1 typs' (List.rev dep_sign) in

  let sign = List.map (fun (na,t) -> mkDeclTomatch na t) typs' in

  let ind =
    appvect (
      applist (mkInd (inductive_of_constructor const_info.cs_cstr),
      List.map (lift const_info.cs_nargs) const_info.cs_params),
      const_info.cs_concl_realargs) in

  let cur_alias = lift (List.length sign) current in
  let currents = Alias (ci,cur_alias,alias_type,ind) :: currents in

  sign,
  { pb with
      env = push_rels sign pb.env;
      tomatch = List.rev_append currents tomatch;
      pred = option_app (specialize_predicate (List.rev typs') dep_sign const_info) pb.pred;
      history = history;
      mat = List.map (push_rels_eqn_with_names sign) submat }

(**********************************************************************
 INVARIANT:

  pb = { env, subst, tomatch, mat, ...}
  tomatch = list of Pushed (c:T) or Abstract (na:T) or Alias (c:T)

  "Pushed" terms and types are relative to env
  "Abstract" types are relative to env enriched by the previous terms to match

  Concretely, each term "c" or type "T" comes with a delayed lift
  index, but it works as if the lifting were effective.

*)

(**********************************************************************)
(* Main compiling descent *)
let rec compile pb =
  match pb.tomatch with
    | (Pushed cur)::rest -> match_current { pb with tomatch = rest } cur
    | (Alias x)::rest -> compile_alias pb x rest
    | (Abstract d)::rest -> compile_generalization pb d rest
    | [] -> build_leaf pb

and match_current pb ((current,typ as ct),deps) =
  let tm1 = List.map (fun eqn -> List.hd eqn.patterns) pb.mat in
  let (_,c,t) = mkDeclTomatch Anonymous typ in
  let typ = to_mutind pb.env pb.isevars tm1 c t in
  match typ with
    | NotInd (_,typ) ->
	check_all_variables typ pb.mat;
	compile (shift_problem ct pb)
    | IsInd (_,(IndType(indf,realargs) as indt)) ->
	let mind,_ = dest_ind_family indf in
	let cstrs = get_constructors pb.env indf in
	let eqns,onlydflt = group_equations pb mind current cstrs pb.mat in
	if (cstrs <> [||] or not (initial_history pb.history)) & onlydflt then
	  compile (shift_problem ct pb)
	else
          let constraints = Array.map (solve_constraints indt) cstrs in

	  (* We generalize over terms depending on current term to match *)
	  let pb = generalize_problem pb current deps in

	  (* We compile branches *)
	  let brs = array_map2 (compile_branch current deps pb) eqns cstrs in

	  (* We build the (elementary) case analysis *)
	  let tags   = Array.map (fun (t,_,_) -> t) brs in
	  let brvals = Array.map (fun (_,v,_) -> v) brs in
	  let brtyps = Array.map (fun (_,_,t) -> t) brs in
	  let (pred,typ,s) =
	    find_predicate pb.caseloc pb.env pb.isevars 
	      pb.pred brtyps cstrs current indt pb.tomatch in
	  let ci = make_case_info pb.env mind RegularStyle tags in
	  let case = mkCase (ci,nf_betaiota pred,current,brvals) in
	  let inst = List.map mkRel deps in
	  pattern_status tags,
	  { uj_val = applist (case, inst);
	    uj_type = substl inst typ }

and compile_branch current deps pb eqn cstr =
  let sign, pb = build_branch current deps pb eqn cstr in
  let tag, j = compile pb in
  (tag, it_mkLambda_or_LetIn j.uj_val sign, j.uj_type)

and compile_generalization pb d rest =
  let pb =
    { pb with
       env = push_rel d pb.env;
       tomatch = rest;
       pred = option_app ungeneralize_predicate pb.pred;
       mat = List.map (push_rels_eqn [d]) pb.mat } in
  let patstat,j = compile pb in
  patstat, 
  { uj_val = mkLambda_or_LetIn d j.uj_val;
    uj_type = mkProd_or_LetIn d j.uj_type }

and compile_alias pb (deppat,nondeppat,d,t) rest =
  let history = simplify_history pb.history in
  let sign, newenv, mat =
    insert_aliases pb.env (evars_of pb.isevars) (deppat,nondeppat,d,t) pb.mat in
  let n = List.length sign in

  (* We had Gamma1; x:current; Gamma2 |- tomatch(x) and we rebind x to get *)
  (* Gamma1; x:current; Gamma2; typs; x':=curalias |- tomatch(x') *)
  let tomatch = lift_tomatch_stack n rest in
  let tomatch = match kind_of_term nondeppat with
    | Rel i ->
	if n = 1 then regeneralize_index_tomatch (i+n) tomatch
	else replace_tomatch i deppat tomatch
    | _ -> (* initial terms are not dependent *) tomatch in

  let pb =
    {pb with
       env = newenv;
       tomatch = tomatch;
       pred = option_app (lift_predicate n) pb.pred;
       history = history;
       mat = mat } in
  let patstat,j = compile pb in
  patstat, 
  List.fold_left mkSpecialLetInJudge j sign

(* pour les alias des initiaux, enrichir les env de ce qu'il faut et
substituer après par les initiaux *)

(**************************************************************************)
(* Preparation of the pattern-matching problem                            *)

(* Qu'est-ce qui faut pas faire pour traiter les alias ... *)

(* On ne veut pas ajouter de primitive à Environ et le problème, c'est
   donc de faire un renommage en se contraignant à parcourir l'env
   dans le sens croissant. Ici, subst renomme des variables repérées
   par leur numéro et seen_ids collecte celles dont on sait que les
   variables de subst annule le scope *)
let rename_env subst env =
  let n = ref (rel_context_length (rel_context env)) in
  let seen_ids = ref [] in
  process_rel_context
    (fun (na,c,t as d) env ->
       let d =
	 try
	   let id = List.assoc !n subst in
	   seen_ids := id :: !seen_ids;
	   (Name id,c,t)
	 with Not_found ->
	   match na with
	     | Name id when List.mem id !seen_ids -> (Anonymous,c,t)
	     | _ -> d in
       decr n;
       push_rel d env) env

let is_dependent_indtype = function
  | NotInd _ -> false
  | IsInd (_, IndType(_,realargs)) -> List.length realargs <> 0

let prepare_initial_alias_eqn isdep tomatchl eqn =
  let (subst, pats) = 
  List.fold_right2
    (fun pat (tm,tmtyp) (subst, stripped_pats) ->
       match alias_of_pat pat with
	 | Anonymous -> (subst, pat::stripped_pats)
	 | Name idpat as na ->
	     match kind_of_term tm with
	       | Rel n when not (is_dependent_indtype tmtyp) & not isdep
		   -> (n, idpat)::subst, (unalias_pat pat::stripped_pats)
	       | _ -> (subst, pat::stripped_pats))
    eqn.patterns tomatchl ([], []) in
  let env = rename_env subst eqn.rhs.rhs_env in
  { eqn with patterns = pats; rhs = { eqn.rhs with rhs_env = env } }

let prepare_initial_aliases isdep tomatchl mat = mat
(*  List.map (prepare_initial_alias_eqn isdep tomatchl) mat*)

(*
let prepare_initial_alias lpat tomatchl rhs =
  List.fold_right2
    (fun pat tm (stripped_pats, rhs) ->
       match alias_of_pat pat with
	 | Anonymous -> (pat::stripped_pats, rhs)
	 | Name _ as na ->
	     match tm with
	       | RVar _ -> 
		   (unalias_pat pat::stripped_pats, 
		    RLetIn (dummy_loc, na, tm, rhs))
	       | _ -> (pat::stripped_pats, rhs))
    lpat tomatchl ([], rhs)
*)
(* builds the matrix of equations testing that each eqn has n patterns
 * and linearizing the _ patterns.
 * Syntactic correctness has already been done in astterm *)
let matx_of_eqns env tomatchl eqns =
  let build_eqn (loc,ids,lpat,rhs) =
(*    let initial_lpat,initial_rhs = prepare_initial_alias lpat tomatchl rhs in*)
    let initial_lpat,initial_rhs = lpat,rhs in
    let initial_rhs = rhs in
    let rhs =
      { rhs_env = env;
	other_ids = ids@(ids_of_named_context (named_context env));
	user_ids = ids;
	rhs_lift = 0;
	it = initial_rhs } in
    { dependencies = [];
      patterns = initial_lpat;
      tag = RegularPat;
      alias_stack = [];
      eqn_loc = loc;
      used = ref false;
      rhs = rhs }
  in List.map build_eqn eqns

(************************************************************************)
(* preparing the elimination predicate if any                          *)

let build_expected_arity env isevars isdep tomatchl =
  let cook n = function
    | _,IsInd (_,IndType(indf,_)) ->
        let indf' = lift_inductive_family n indf in
	Some (build_dependent_inductive env indf', fst (get_arity env indf'))
    | _,NotInd _ -> None
  in
  let rec buildrec n env = function
    | [] -> new_Type ()
    | tm::ltm ->
	match cook n tm with
	  | None -> buildrec n env ltm
	  | Some (ty1,aritysign) ->
	      let rec follow n env = function
		| d::sign ->
		    mkProd_or_LetIn_name env
		      (follow (n+1) (push_rel d env) sign) d
		| [] ->
		    if isdep then
		      mkProd (Anonymous, ty1, 
			      buildrec (n+1)
				(push_rel_assum (Anonymous, ty1) env)
				ltm)
		    else buildrec n env ltm
	      in follow n env (List.rev aritysign)
  in buildrec 0 env tomatchl

let extract_predicate_conclusion isdep tomatchl pred =
  let cook = function
    | _,IsInd (_,IndType(_,args)) -> Some (List.length args)
    | _,NotInd _ -> None in
  let decomp_lam_force p =
    match kind_of_term p with
      | Lambda (_,_,c) -> c
      | _ -> (* eta-expansion *) applist (lift 1 p, [mkRel 1]) in
  let rec buildrec p = function
    | [] -> p
    | tm::ltm ->
	match cook tm with
	  | None -> 
              let p = 
                (* adjust to a sign containing the NotInd's *)
                if isdep then lift 1 p else p in
              buildrec p ltm 
	  | Some n ->
              let n = if isdep then n+1 else n in
              let p = iterate decomp_lam_force n p in
              buildrec p ltm
  in buildrec pred tomatchl

let set_arity_signature dep n arsign tomatchl pred x =
  (* avoid is not exhaustive ! *)
  let rec decomp_lam_force n avoid l p =
    if n = 0 then (List.rev l,p,avoid) else
    match p with
      | RLambda (_,(Name id as na),_,c) -> 
          decomp_lam_force (n-1) (id::avoid) (na::l) c
      | RLambda (_,(Anonymous as na),_,c) -> decomp_lam_force (n-1) avoid (na::l) c
      | _ ->
          let x = next_ident_away (id_of_string "x") avoid in
          decomp_lam_force (n-1) (x::avoid) (Name x :: l) 
          (* eta-expansion *)
            (let a = RVar (dummy_loc,x) in
             match p with
               | RApp (loc,p,l) -> RApp (loc,p,l@[a])
               | _ -> (RApp (dummy_loc,p,[a]))) in
  let rec decomp_block avoid p = function
    | ([], _) -> x := Some p
    | ((_,IsInd (_,IndType(indf,realargs)))::l),(y::l')  ->
	let (ind,params) = dest_ind_family indf in
        let (nal,p,avoid') = decomp_lam_force (List.length realargs) avoid [] p 
        in
        let na,p,avoid' = 
          if dep then decomp_lam_force 1 avoid' [] p else [Anonymous],p,avoid'
        in 
        y :=
        (List.hd na,
         if List.for_all ((=) Anonymous) nal then
           None
         else
           Some (dummy_loc, ind, (List.map (fun _ -> Anonymous) params)@nal));
        decomp_block avoid' p (l,l')
    | (_::l),(y::l') ->
        y := (Anonymous,None);
        decomp_block avoid p (l,l')
    | _ -> anomaly "set_arity_signature"
  in
  decomp_block [] pred (tomatchl,arsign)

let prepare_predicate_from_tycon loc dep env isevars tomatchs c =
  let cook (n, l, env) = function
    | c,IsInd (_,IndType(indf,realargs)) ->
	let indf' = lift_inductive_family n indf in
	let sign = make_arity_signature env dep indf' in
	let p = List.length realargs in
	if dep then
	  (n + p + 1, c::(List.rev realargs)@l, push_rels sign env)
	else
	  (n + p, (List.rev realargs)@l, push_rels sign env)
    | c,NotInd _ ->
	(n, l, env) in
  let n, allargs, env = List.fold_left cook (0, [], env) tomatchs in
  let allargs =
    List.map (fun c -> lift n (nf_betadeltaiota env (evars_of isevars) c)) allargs in
  let rec build_skeleton env c =
    (* Don't put into normal form, it has effects on the synthesis of evars *)
 (* let c = whd_betadeltaiota env (evars_of isevars) c in *)
    (* We turn all subterms possibly dependent into an evar with maximum ctxt*)
    if isEvar c or List.exists (eq_constr c) allargs then
      mkExistential isevars env (loc, CasesType)
    else
      map_constr_with_full_binders push_rel build_skeleton env c in
  build_skeleton env (lift n c)
  
(* Here, [pred] is assumed to be in the context built from all *)
(* realargs and terms to match *)
let build_initial_predicate isdep pred tomatchl =
  let nar = List.fold_left (fun n (_,t) ->
    let p = match t with IsInd (_,IndType(_,a)) -> List.length a | _ -> 0 in
    if isdep then n+p+1 else n+p) 0 tomatchl in
  let cook = function
    | _,IsInd (_,IndType(_,realargs)) -> List.length realargs
    | _,NotInd _ -> 0 in
  let rec buildrec n pred = function
    | [] -> PrCcl pred
    | tm::ltm ->
        let nrealargs = cook tm in
        let pred, p, user_p =
          if isdep then 
            if dependent (mkRel (nar-n)) pred then pred, 1, 1
            else liftn (-1) (nar-n) pred, 0, 1
          else pred, 0, 0 in
	PrLetIn ((nrealargs,p=1), buildrec (n+nrealargs+user_p) pred ltm)
  in buildrec 0 pred tomatchl

let extract_arity_signature env0 tomatchl tmsign =
  let get_one_sign n tm {contents = (na,t)} =
    match tm with
      | NotInd (bo,typ) -> 
	  (match t with
	    | None -> [na,option_app (lift n) bo,lift n typ]
	    | Some (loc,_,_) -> 
 	    user_err_loc (loc,"",
	    str "Unexpected type annotation for a term of non inductive type"))
      | IsInd (_,IndType(indf,realargs)) ->
          let indf' = lift_inductive_family n indf in
	  let (ind,params) = dest_ind_family indf' in
	  let nrealargs = List.length realargs in
	  let realnal =
	    match t with
	      | Some (loc,ind',nal) ->
		  let nparams = List.length params in
		  if ind <> ind' then
		    user_err_loc (loc,"",str "Wrong inductive type");
		  if List.length nal <> nparams + nrealargs then
		    user_err_loc (loc,"",
		    str "Wrong number of arguments for inductive type");
		  let parnal,realnal = list_chop nparams nal in
		  if List.exists ((<>) Anonymous) parnal then
		    user_err_loc (loc,"",
		    str "The parameters of inductive type must be implicit");
		  List.rev realnal
	      | None -> list_tabulate (fun _ -> Anonymous) nrealargs in
	  let arsign = fst (get_arity env0 indf') in
	  (na,None,build_dependent_inductive env0 indf')
	  ::(List.map2 (fun x (_,c,t) ->(x,c,t)) realnal arsign) in
  let rec buildrec n = function
    | [],[] -> []
    | (_,tm)::ltm, x::tmsign ->
	let l = get_one_sign n tm x in
	(buildrec (n + List.length l) (ltm,tmsign)) @ l
    | _ -> assert false
  in buildrec 0 (tomatchl,tmsign)

(* Builds the predicate. If the predicate is dependent, its context is
 * made of 1+nrealargs assumptions for each matched term in an inductive
 * type and 1 assumption for each term not _syntactically_ in an
 * inductive type.

 * V7 case: determines whether the multiple case is dependent or not
 * - if its arity is made of nrealargs assumptions for each matched
 * term in an inductive type and nothing for terms not _syntactically_
 * in an inductive type, then it is non dependent
 * - if its arity is made of 1+nrealargs assumptions for each matched
 * term in an inductive type and nothing for terms not _syntactically_
 * in an inductive type, then it is dependent and needs an adjustement
 * to fulfill the criterion above that terms not in an inductive type
 * counts for 1 in the dependent case

 * V8 case: each matched terms are independently considered dependent
 * or not

 * A type constraint but no annotation case: it is assumed non dependent
 *)

let prepare_predicate loc typing_fun isevars env tomatchs sign tycon = function
  (* No type annotation at all *)
  | (None,{contents = None}) ->
      (match tycon with
       | None -> None
       | Some t ->
	 let pred = prepare_predicate_from_tycon loc false env isevars tomatchs t in
	 Some (build_initial_predicate false pred tomatchs))

  (* v8 style type annotation *)
  | (None,{contents = Some rtntyp}) ->

      (* We extract the signature of the arity *)
      let arsign = extract_arity_signature env tomatchs sign in
      let env = push_rels arsign env in
      let predccl = (typing_fun (mk_tycon (new_Type ())) env rtntyp).uj_val in
      Some (build_initial_predicate true predccl tomatchs)

  (* v7 style type annotation; set the v8 annotation by side effect *)
  | (Some pred,x) ->
      let loc = loc_of_rawconstr pred in
      let dep, n, predj =
	let isevars_copy = evars_of isevars in
        (* We first assume the predicate is non dependent *)
	let ndep_arity = build_expected_arity env isevars false tomatchs in
        try
	  false, nb_prod ndep_arity, typing_fun (mk_tycon ndep_arity) env pred
	with PretypeError _ | TypeError _ |
	    Stdpp.Exc_located (_,(PretypeError _ | TypeError _)) ->
        evars_reset_evd isevars_copy isevars;
        (* We then assume the predicate is dependent *)
	let dep_arity = build_expected_arity env isevars true tomatchs in
	try
	  true, nb_prod dep_arity, typing_fun (mk_tycon dep_arity) env pred
	with PretypeError _ | TypeError _ |
	  Stdpp.Exc_located (_,(PretypeError _ | TypeError _)) ->
        evars_reset_evd isevars_copy isevars;
        (* Otherwise we attempt to type it without constraints, possibly *)
        (* failing with an error message; it may also be well-typed *)
	(* but fails to satisfy arity constraints in case_dependent *)
        let predj = typing_fun empty_tycon env pred in
	error_wrong_predicate_arity_loc
	  loc env predj.uj_val ndep_arity dep_arity
      in
      let predccl = extract_predicate_conclusion dep tomatchs predj.uj_val in
(*
      let etapred,cdep = case_dependent env (evars_of isevars) loc predj tomatchs in
*)
      set_arity_signature dep n sign tomatchs pred x;
      Some (build_initial_predicate dep predccl tomatchs)


(**************************************************************************)
(* Main entry of the matching compilation                                 *)

let compile_cases loc (typing_fun,isevars) tycon env (predopt, tomatchl, eqns)=

  (* We build the matrix of patterns and right-hand-side *)
  let matx = matx_of_eqns env tomatchl eqns in

  (* We build the vector of terms to match consistently with the *)
  (* constructors found in patterns *)
  let rawtms, tmsign = List.split tomatchl in
  let tomatchs = coerce_to_indtype typing_fun isevars env matx rawtms in

  (* We build the elimination predicate if any and check its consistency *)
  (* with the type of arguments to match *)
  let pred = prepare_predicate loc typing_fun isevars env tomatchs tmsign tycon predopt in

  (* We deal with initial aliases *)
  let matx = prepare_initial_aliases (known_dependent pred) tomatchs matx in 

  (* We push the initial terms to match and push their alias to rhs' envs *)
  (* names of aliases will be recovered from patterns (hence Anonymous here) *)
  let initial_pushed = List.map (fun tm -> Pushed (tm,[])) tomatchs in
 
  let pb =
    { env      = env;
      isevars  = isevars;
      pred     = pred;
      tomatch  = initial_pushed;
      history  = start_history (List.length initial_pushed);
      mat      = matx;
      caseloc  = loc;
      typing_function = typing_fun } in
  
  let _, j = compile pb in

  (* We check for unused patterns *)
  List.iter (check_unused_pattern env) matx;
  
  match tycon with
    | Some p ->	Coercion.inh_conv_coerce_to loc env isevars j p
    | None -> j
