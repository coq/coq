(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Compat
open Util
open Names
open Nameops
open Term
open Termops
open Namegen
open Declarations
open Inductiveops
open Environ
open Sign
open Reductionops
open Typeops
open Type_errors
open Glob_term
open Retyping
open Pretype_errors
open Evarutil
open Evarconv
open Evd

(* Pattern-matching errors *)

type pattern_matching_error =
  | BadPattern of constructor * constr
  | BadConstructor of constructor * inductive
  | WrongNumargConstructor of constructor * int
  | WrongNumargInductive of inductive * int
  | WrongPredicateArity of constr * constr * constr
  | NeedsInversion of constr * constr
  | UnusedClause of cases_pattern list
  | NonExhaustive of cases_pattern list
  | CannotInferPredicate of (constr * types) array

exception PatternMatchingError of env * pattern_matching_error

let raise_pattern_matching_error (loc,ctx,te) =
  Loc.raise loc (PatternMatchingError(ctx,te))

let error_bad_pattern_loc loc cstr ind =
  raise_pattern_matching_error (loc, Global.env(), BadPattern (cstr,ind))

let error_bad_constructor_loc loc cstr ind =
  raise_pattern_matching_error (loc, Global.env(), BadConstructor (cstr,ind))

let error_wrong_numarg_constructor_loc loc env c n =
  raise_pattern_matching_error (loc, env, WrongNumargConstructor(c,n))

let error_wrong_numarg_inductive_loc loc env c n =
  raise_pattern_matching_error (loc, env, WrongNumargInductive(c,n))

let error_wrong_predicate_arity_loc loc env c n1 n2 =
  raise_pattern_matching_error (loc, env, WrongPredicateArity (c,n1,n2))

let error_needs_inversion env x t =
  raise (PatternMatchingError (env, NeedsInversion (x,t)))

module type S = sig
  val compile_cases :
    loc -> case_style ->
    (type_constraint -> env -> evar_map ref -> glob_constr -> unsafe_judgment) * evar_map ref ->
    type_constraint ->
    env -> glob_constr option * tomatch_tuples * cases_clauses ->
    unsafe_judgment
end

let rec list_try_compile f = function
  | [a] -> f a
  | [] -> anomaly "try_find_f"
  | h::t ->
      try f h
      with UserError _ | TypeError _ | PretypeError _
	| Loc.Exc_located (_,(UserError _ | TypeError _ | PretypeError _)) ->
	    list_try_compile f t

let force_name =
  let nx = Name (id_of_string "x") in function Anonymous -> nx | na -> na

(************************************************************************)
(*            Pattern-matching compilation (Cases)                      *)
(************************************************************************)

(************************************************************************)
(* Configuration, errors and warnings *)

open Pp

let msg_may_need_inversion () =
  strbrk "Found a matching with no clauses on a term unknown to have an empty inductive type."

(* Utils *)
let make_anonymous_patvars n =
  list_make n (PatVar (dummy_loc,Anonymous))

(* Environment management *)
let push_rels vars env = List.fold_right push_rel vars env

(* We have x1:t1...xn:tn,xi':ti,y1..yk |- c and re-generalize
   over xi:ti to get x1:t1...xn:tn,xi':ti,y1..yk |- c[xi:=xi'] *)

let relocate_rel n1 n2 k j = if j = n1+k then n2+k else j

let rec relocate_index n1 n2 k t = match kind_of_term t with
  | Rel j when j = n1+k -> mkRel (n2+k)
  | Rel j when j < n1+k -> t
  | Rel j when j > n1+k -> t
  | _ -> map_constr_with_binders succ (relocate_index n1 n2) k t

type alias_constr =
  | DepAlias
  | NonDepAlias

let mkSpecialLetInJudge j (na,(deppat,nondeppat,d,t)) =
  { uj_val =
    if
      isRel deppat or not (dependent (mkRel 1) j.uj_val) or
      d = NonDepAlias & not (dependent (mkRel 1) j.uj_type)
    then
      (* The body of pat is not needed to type j - see *)
      (* insert_aliases - and both deppat and nondeppat have the *)
      (* same type, then one can freely substitute one by the other. *)
      (* We use nondeppat only if it's a Rel to preserve sharing. *)
      if isRel nondeppat then
        subst1 nondeppat j.uj_val
      else subst1 deppat j.uj_val
    else
      (* The body of pat is not needed to type j but its value *)
      (* is dependent in the type of j; our choice is to *)
      (* enforce this dependency *)
      mkLetIn (na,deppat,t,j.uj_val);
    uj_type = subst1 deppat j.uj_type }

(**********************************************************************)
(* Structures used in compiling pattern-matching *)

type 'a rhs =
    { rhs_env    : env;
      rhs_vars   : identifier list;
      avoid_ids  : identifier list;
      it         : 'a option}

type 'a equation =
    { patterns     : cases_pattern list;
      rhs          : 'a rhs;
      alias_stack  : name list;
      eqn_loc      : loc;
      used         : bool ref }

type 'a matrix = 'a equation list

type dep_status = KnownDep | KnownNotDep | DepUnknown

(* 1st argument of IsInd is the original ind before extracting the summary *)
type tomatch_type =
  | IsInd of types * inductive_type * name list
  | NotInd of constr option * types

type tomatch_status =
  | Pushed of ((constr * tomatch_type) * int list * (name * dep_status))
  | Alias of (constr * constr * alias_constr * constr)
  | Abstract of int * rel_declaration

type tomatch_stack = tomatch_status list

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

let feed_history arg = function
  | Continuation (n, l, h) when n>=1 ->
      Continuation (n-1, arg :: l, h)
  | Continuation (n, _, _) ->
      anomaly ("Bad number of expected remaining patterns: "^(string_of_int n))
  | Result _ ->
      anomaly "Exhausted pattern history"

(* This is for non exhaustive error message *)

let rec glob_pattern_of_partial_history args2 = function
  | Continuation (n, args1, h) ->
      let args3 = make_anonymous_patvars (n - (List.length args2)) in
      build_glob_pattern (List.rev_append args1 (args2@args3)) h
  | Result pl -> pl

and build_glob_pattern args = function
  | Top -> args
  | MakeAlias (AliasLeaf, rh) ->
      assert (args = []);
      glob_pattern_of_partial_history [PatVar (dummy_loc, Anonymous)] rh
  | MakeAlias (AliasConstructor pci, rh) ->
      glob_pattern_of_partial_history
	[PatCstr (dummy_loc, pci, args, Anonymous)] rh

let complete_history = glob_pattern_of_partial_history []

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

   env, evd |- match terms_to_tomatch return pred with mat end

  where terms_to_match is some sequence of "instructions" (t1 ... tp)

  and mat is some matrix

   (p11 ... p1n -> rhs1)
   (    ...            )
   (pm1 ... pmn -> rhsm)

  Terms to match: there are 3 kinds of instructions

  - "Pushed" terms to match are typed in [env]; these are usually just
    Rel(n) except for the initial terms given by user; in Pushed ((c,tm),deps,na),
    [c] is the reference to the term (which is a Rel or an initial term), [tm] is
    its type (telling whether we know if it is an inductive type or not),
    [deps] is the list of terms to abstract before matching on [c] (these are
    rels too)
  - "Abstract" instructions means that an abstraction has to be inserted in the
    current branch to build (this means a pattern has been detected dependent
    in another one and a generalization is necessary to ensure well-typing)
    Abstract instructions extend the [env] in which the other instructions
    are typed
  - "Alias" instructions means an alias has to be inserted (this alias
    is usually removed at the end, except when its type is not the
    same as the type of the matched term from which it comes -
    typically because the inductive types are "real" parameters)

  Right-hand sides:

  They consist of a raw term to type in an environment specific to the
  clause they belong to: the names of declarations are those of the
  variables present in the patterns. Therefore, they come with their
  own [rhs_env] (actually it is the same as [env] except for the names
  of variables).

*)

type 'a pattern_matching_problem =
    { env       : env;
      evdref    : evar_map ref;
      pred      : constr;
      tomatch   : tomatch_stack;
      history   : pattern_continuation;
      mat       : 'a matrix;
      caseloc   : loc;
      casestyle : case_style;
      typing_function: type_constraint -> env -> evar_map ref -> 'a option -> unsafe_judgment }

(*--------------------------------------------------------------------------*
 * A few functions to infer the inductive type from the patterns instead of *
 * checking that the patterns correspond to the ind. type of the            *
 * destructurated object. Allows type inference of examples like            *
 *  match n with O => true | _ => false end                                 *
 *  match x in I with C => true | _ => false end                            *
 *--------------------------------------------------------------------------*)

(* Computing the inductive type from the matrix of patterns *)

(* We use the "in I" clause to coerce the terms to match and otherwise
   use the constructor to know in which type is the matching problem

   Note that insertion of coercions inside nested patterns is done
   each time the matrix is expanded *)

let rec find_row_ind = function
    [] -> None
  | PatVar _ :: l -> find_row_ind l
  | PatCstr(loc,c,_,_) :: _ -> Some (loc,c)

let inductive_template evdref env tmloc ind =
  let arsign = get_full_arity_sign env ind in
  let hole_source = match tmloc with
    | Some loc -> fun i -> (loc, TomatchTypeParameter (ind,i))
    | None -> fun _ -> (dummy_loc, InternalHole) in
   let (_,evarl,_) =
    List.fold_right
      (fun (na,b,ty) (subst,evarl,n) ->
	match b with
        | None ->
	    let ty' = substl subst ty in
	    let e = e_new_evar evdref env ~src:(hole_source n) ty' in
	    (e::subst,e::evarl,n+1)
	| Some b ->
	    (substl subst b::subst,evarl,n+1))
      arsign ([],[],1) in
   applist (mkInd ind,List.rev evarl)

let try_find_ind env sigma typ realnames =
  let (IndType(_,realargs) as ind) = find_rectype env sigma typ in
  let names =
    match realnames with
      | Some names -> names
      | None -> list_make (List.length realargs) Anonymous in
  IsInd (typ,ind,names)


let inh_coerce_to_ind evdref env ty tyi =
  let expected_typ = inductive_template evdref env None tyi in
     (* devrait être indifférent d'exiger leq ou pas puisque pour
        un inductif cela doit être égal *)
  let _ = e_cumul env evdref expected_typ ty in ()

let unify_tomatch_with_patterns evdref env loc typ pats realnames =
  match find_row_ind pats with
    | None -> NotInd (None,typ)
    | Some (_,(ind,_)) ->
	inh_coerce_to_ind evdref env typ ind;
	try try_find_ind env !evdref typ realnames
	with Not_found -> NotInd (None,typ)

let find_tomatch_tycon evdref env loc = function
  (* Try if some 'in I ...' is present and can be used as a constraint *)
  | Some (_,ind,_,realnal) ->
      mk_tycon (inductive_template evdref env loc ind),Some (List.rev realnal)
  | None ->
      empty_tycon,None

let coerce_row typing_fun evdref env pats (tomatch,(_,indopt)) =
  let loc = Some (loc_of_glob_constr tomatch) in
  let tycon,realnames = find_tomatch_tycon evdref env loc indopt in
  let j = typing_fun tycon env evdref tomatch in
  let typ = nf_evar !evdref j.uj_type in
  let t =
    try try_find_ind env !evdref typ realnames
    with Not_found ->
      unify_tomatch_with_patterns evdref env loc typ pats realnames in
  (j.uj_val,t)

let coerce_to_indtype typing_fun evdref env matx tomatchl =
  let pats = List.map (fun r ->  r.patterns) matx in
  let matx' = match matrix_transpose pats with
    | [] -> List.map (fun _ -> []) tomatchl (* no patterns at all *)
    | m -> m in
  List.map2 (coerce_row typing_fun evdref env) matx' tomatchl

(************************************************************************)
(* Utils *)

let mkExistential env ?(src=(dummy_loc,InternalHole)) evdref =
  e_new_evar evdref env ~src:src (new_Type ())

let evd_comb2 f evdref x y =
  let (evd',y) = f !evdref x y in
  evdref := evd';
  y


module Cases_F(Coercion : Coercion.S) : S = struct

let adjust_tomatch_to_pattern pb ((current,typ),deps,dep) =
  (* Ideally, we could find a common inductive type to which both the
     term to match and the patterns coerce *)
  (* In practice, we coerce the term to match if it is not already an
     inductive type and it is not dependent; moreover, we use only
     the first pattern type and forget about the others *)
  let typ,names =
    match typ with IsInd(t,_,names) -> t,Some names | NotInd(_,t) -> t,None in
  let tmtyp =
    try try_find_ind pb.env !(pb.evdref) typ names
    with Not_found -> NotInd (None,typ) in
  match tmtyp with
  | NotInd (None,typ) ->
      let tm1 = List.map (fun eqn -> List.hd eqn.patterns) pb.mat in
      (match find_row_ind tm1 with
	| None -> (current,tmtyp)
	| Some (_,(ind,_)) ->
	    let indt = inductive_template pb.evdref pb.env None ind in
	    let current =
	      if deps = [] & isEvar typ then
	      (* Don't insert coercions if dependent; only solve evars *)
		let _ = e_cumul pb.env pb.evdref indt typ in
		current
	      else
		(evd_comb2 (Coercion.inh_conv_coerce_to dummy_loc pb.env)
		  pb.evdref (make_judge current typ) (mk_tycon_type indt)).uj_val in
	    let sigma =  !(pb.evdref) in
	    (current,try_find_ind pb.env sigma indt names))
  | _ -> (current,tmtyp)

let type_of_tomatch = function
  | IsInd (t,_,_) -> t
  | NotInd (_,t) -> t

let mkDeclTomatch na = function
  | IsInd (t,_,_) -> (na,None,t)
  | NotInd (c,t) -> (na,c,t)

let map_tomatch_type f = function
  | IsInd (t,ind,names) -> IsInd (f t,map_inductive_type f ind,names)
  | NotInd (c,t) -> NotInd (Option.map f c, f t)

let liftn_tomatch_type n depth = map_tomatch_type (liftn n depth)
let lift_tomatch_type n = liftn_tomatch_type n 1

(**********************************************************************)
(* Utilities on patterns *)

let current_pattern eqn =
  match eqn.patterns with
    | pat::_ -> pat
    | [] -> anomaly "Empty list of patterns"

let alias_of_pat = function
  | PatVar (_,name) -> name
  | PatCstr(_,_,_,name) -> name

let remove_current_pattern eqn =
  match eqn.patterns with
    | pat::pats ->
	{ eqn with
	    patterns = pats;
	    alias_stack = alias_of_pat pat :: eqn.alias_stack }
    | [] -> anomaly "Empty list of patterns"

let prepend_pattern tms eqn = {eqn with patterns = tms@eqn.patterns }

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

let check_and_adjust_constructor env ind cstrs = function
  | PatVar _ as pat -> pat
  | PatCstr (loc,((_,i) as cstr),args,alias) as pat ->
      (* Check it is constructor of the right type *)
      let ind' = inductive_of_constructor cstr in
      if eq_ind ind' ind then
	(* Check the constructor has the right number of args *)
	let ci = cstrs.(i-1) in
	let nb_args_constr = ci.cs_nargs in
	if List.length args = nb_args_constr then pat
	else
	  try
	    let args' = adjust_local_defs loc (args, List.rev ci.cs_args)
	    in PatCstr (loc, cstr, args', alias)
	  with NotAdjustable ->
	    error_wrong_numarg_constructor_loc loc (Global.env())
	      cstr nb_args_constr
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
    | [] -> errorlabstrm "build_leaf" (msg_may_need_inversion())
    | eqn::_ ->
	set_used_pattern eqn;
        eqn.rhs

(**********************************************************************)
(* Functions to deal with matrix factorization *)

let occur_in_rhs na rhs =
  match na with
    | Anonymous -> false
    | Name id -> List.mem id rhs.rhs_vars

let is_dep_patt_in eqn = function
  | PatVar (_,name) -> occur_in_rhs name eqn.rhs
  | PatCstr _ -> true

let mk_dep_patt_row (pats,eqn) =
  List.map (is_dep_patt_in eqn) pats

let dependencies_in_pure_rhs nargs eqns =
  if eqns = [] then list_make nargs false (* Only "_" patts *) else
  let deps_rows = List.map mk_dep_patt_row eqns in
  let deps_columns = matrix_transpose deps_rows in
  List.map (List.exists ((=) true)) deps_columns

let dependent_decl a = function
  | (na,None,t) -> dependent a t
  | (na,Some c,t) -> dependent a t || dependent a c

let rec dep_in_tomatch n = function
  | (Pushed _ | Alias _) :: l -> dep_in_tomatch n l
  | Abstract (_,d) :: l -> dependent_decl (mkRel n) d or dep_in_tomatch (n+1) l
  | [] -> false

let dependencies_in_rhs nargs current tms eqns =
  match kind_of_term current with
  | Rel n when dep_in_tomatch n tms -> list_make nargs true
  | _ -> dependencies_in_pure_rhs nargs eqns

(* Computing the matrix of dependencies *)

(* [find_dependency_list tmi [d(i+1);...;dn]] computes in which
   declarations [d(i+1);...;dn] the term [tmi] is dependent in.

   [find_dependencies_signature (used1,...,usedn) ((tm1,d1),...,(tmn,dn))]
   returns [(deps1,...,depsn)] where [depsi] is a subset of n,..,i+1
   denoting in which of the d(i+1)...dn, the term tmi is dependent.
   Dependencies are expressed by index, e.g. in dependency list
   [n-2;1], [1] points to [dn] and [n-2] to [d3]
*)

let rec find_dependency_list tm = function
  | [] -> []
  | (used,tdeps,d)::rest ->
      let deps = find_dependency_list tm rest in
      if used && dependent_decl tm d
      then list_add_set (List.length rest + 1) (list_union deps tdeps)
      else deps

let find_dependencies is_dep_or_cstr_in_rhs (tm,d) nextlist =
  let deps = find_dependency_list tm nextlist in
  if is_dep_or_cstr_in_rhs || deps <> []
  then ((true ,deps,d)::nextlist)
  else ((false,[]  ,d)::nextlist)

let find_dependencies_signature deps_in_rhs typs =
  let l = List.fold_right2 find_dependencies deps_in_rhs typs [] in
  List.map (fun (_,deps,_) -> deps) l

(* Assume we had terms t1..tq to match in a context xp:Tp,...,x1:T1 |-
   and xn:Tn has just been regeneralized into x:Tn so that the terms
   to match are now to be considered in the context xp:Tp,...,x1:T1,x:Tn |-.

   [relocate_index_tomatch n 1 tomatch] updates t1..tq so that
   former references to xn1 are now references to x. Note that t1..tq
   are already adjusted to the context xp:Tp,...,x1:T1,x:Tn |-.

   [relocate_index_tomatch 1 n tomatch] will go the way back.
 *)

let relocate_index_tomatch n1 n2 =
  let rec genrec depth = function
  | [] ->
      []
  | Pushed ((c,tm),l,dep) :: rest ->
      let c = relocate_index n1 n2 depth c in
      let tm = map_tomatch_type (relocate_index n1 n2 depth) tm in
      let l = List.map (relocate_rel n1 n2 depth) l in
      Pushed ((c,tm),l,dep) :: genrec depth rest
  | Alias (c1,c2,d,t) :: rest ->
      Alias (relocate_index n1 n2 depth c1,c2,d,t) :: genrec depth rest
  | Abstract (i,d) :: rest ->
      let i = relocate_rel n1 n2 depth i in
      Abstract (i,map_rel_declaration (relocate_index n1 n2 depth) d)
      :: genrec (depth+1) rest in
  genrec 0

(* [replace_tomatch n c tomatch] replaces [Rel n] by [c] in [tomatch] *)

let rec replace_term n c k t =
  if isRel t && destRel t = n+k then lift k c
  else map_constr_with_binders succ (replace_term n c) k t

let length_of_tomatch_type_sign (dep,_) = function
  | NotInd _ -> if dep<>Anonymous then 1 else 0
  | IsInd (_,_,names) -> List.length names + if dep<>Anonymous then 1 else 0

let replace_tomatch n c =
  let rec replrec depth = function
  | [] -> []
  | Pushed ((b,tm),l,dep) :: rest ->
      let b = replace_term n c depth b in
      let tm = map_tomatch_type (replace_term n c depth) tm in
      List.iter (fun i -> if i=n+depth then anomaly "replace_tomatch") l;
      Pushed ((b,tm),l,dep) :: replrec depth rest
  | Alias (c1,c2,d,t) :: rest ->
      Alias (replace_term n c depth c1,c2,d,t) :: replrec depth rest
  | Abstract (i,d) :: rest ->
      Abstract (i,map_rel_declaration (replace_term n c depth) d)
      :: replrec (depth+1) rest in
  replrec 0

(* [liftn_tomatch_stack]: a term to match has just been substituted by
   some constructor t = (ci x1...xn) and the terms x1 ... xn have been
   added to match; all pushed terms to match must be lifted by n
   (knowing that [Abstract] introduces a binder in the list of pushed
   terms to match).
*)

let rec liftn_tomatch_stack n depth = function
  | [] -> []
  | Pushed ((c,tm),l,dep)::rest ->
      let c = liftn n depth c in
      let tm = liftn_tomatch_type n depth tm in
      let l = List.map (fun i -> if i<depth then i else i+n) l in
      Pushed ((c,tm),l,dep)::(liftn_tomatch_stack n depth rest)
  | Alias (c1,c2,d,t)::rest ->
      Alias (liftn n depth c1,liftn n depth c2,d,liftn n depth t)
      ::(liftn_tomatch_stack n depth rest)
  | Abstract (i,d)::rest ->
      let i = if i<depth then i else i+n in
      Abstract (i,map_rel_declaration (liftn n depth) d)
      ::(liftn_tomatch_stack n (depth+1) rest)

let lift_tomatch_stack n = liftn_tomatch_stack n 1

(* if [current] has type [I(p1...pn u1...um)] and we consider the case
   of constructor [ci] of type [I(p1...pn u'1...u'm)], then the
   default variable [name] is expected to have which type?
   Rem: [current] is [(Rel i)] except perhaps for initial terms to match *)

(************************************************************************)
(* Some heuristics to get names for variables pushed in pb environment *)
(* Typical requirement:

   [match y with (S (S x)) => x | x => x end] should be compiled into
   [match y with O => y | (S n) => match n with O => y | (S x) => x end end]

   and [match y with (S (S n)) => n | n => n end] into
   [match y with O => y | (S n0) => match n0 with O => y | (S n) => n end end]

   i.e. user names should be preserved and created names should not
   interfere with user names

   The exact names here are not important for typing (because they are
   put in pb.env and not in the rhs.rhs_env of branches. However,
   whether a name is Anonymous or not may have an effect on whether a
   generalization is done or not.
 *)

let merge_name get_name obj = function
  | Anonymous -> get_name obj
  | na -> na

let merge_names get_name = List.map2 (merge_name get_name)

let get_names env sign eqns =
  let names1 = list_make (List.length sign) Anonymous in
  (* If any, we prefer names used in pats, from top to bottom *)
  let names2 =
    List.fold_right
      (fun (pats,eqn) names -> merge_names alias_of_pat pats names)
      eqns names1 in
  (* Otherwise, we take names from the parameters of the constructor but
     avoiding conflicts with user ids *)
  let allvars =
    List.fold_left (fun l (_,eqn) -> list_union l eqn.rhs.avoid_ids) [] eqns in
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
(* We just factorized a match over a matrix of equations         *)
(* "C xi1 .. xin as xi" as a single match over "C y1 .. yn as y" *)
(* We now replace the names y1 .. yn y by the actual names       *)
(* xi1 .. xin xi to be found in the i-th clause of the matrix    *)

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
  (* name2 takes the meet of all needed aliases *)
  let name2 =
    List.fold_right (merge_name (fun x -> x)) eqnsnames Anonymous in
  (* Only needed aliases are kept by build_aliases_context *)
  let eqnsnames, sign1, sign2, env =
    build_aliases_context env sigma [name2] eqnsnames [alias] in
  let eqns = list_map3 (insert_aliases_eqn sign1) eqnsnames alias_rests eqns in
  sign2, env, eqns

let push_generalized_decl_eqn env n (na,c,t) eqn =
  let na = match na with
  | Anonymous -> Anonymous
  | Name id -> pi1 (Environ.lookup_rel n eqn.rhs.rhs_env) in
  push_rels_eqn [(na,c,t)] eqn

(**********************************************************************)
(* Functions to deal with elimination predicate *)

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

The predicate has the form phi = [y1..yq][z:I(y1..yq)]psi and it has to
satisfy the following n+1 equations:

  Gamma, x11...x1p1 |- (phi u11..u1q (C1 x11..x1p1))  =  T1
   ...
  Gamma, xn1...xnpn |- (phi un1..unq (Cn xn1..xnpn))  =  Tn
  Gamma             |- (phi u01..u0q t)               =  T

Some hints:

- Clearly, if xij occurs in Ti, then, a "match z with (Ci xi1..xipi)
  => ... end"  or a "psi(yk)", with psi extracting xij from uik, should be
  inserted somewhere in Ti.

- If T is undefined, an easy solution is to insert a "match z with
  (Ci xi1..xipi) => ... end" in front of each Ti

- Otherwise, T1..Tn and T must be step by step unified, if some of them
  diverge, then try to replace the diverging subterm by one of y1..yq or z.

- The main problem is what to do when an existential variables is encountered

*)

(* Propagation of user-provided predicate through compilation steps *)

let rec map_predicate f k ccl = function
  | [] -> f k ccl
  | Pushed ((_,tm),_,dep) :: rest ->
      let k' = length_of_tomatch_type_sign dep tm in
      map_predicate f (k+k') ccl rest
  | Alias _ :: rest ->
      map_predicate f k ccl rest
  | Abstract _ :: rest ->
      map_predicate f (k+1) ccl rest

let noccur_predicate_between n = map_predicate (noccur_between n)

let liftn_predicate n = map_predicate (liftn n)

let lift_predicate n = liftn_predicate n 1

let regeneralize_index_predicate n = map_predicate (relocate_index n 1) 0

let substnl_predicate sigma = map_predicate (substnl sigma)

(* This is parallel bindings *)
let subst_predicate (args,copt) ccl tms =
  let sigma = match copt with
    | None -> List.rev args
    | Some c -> c::(List.rev args) in
  substnl_predicate sigma 0 ccl tms

let specialize_predicate_var (cur,typ,dep) tms ccl =
  let c = if dep<>Anonymous then Some cur else None in
  let l =
    match typ with
    | IsInd (_,IndType(_,realargs),names) -> if names<>[] then realargs else []
    | NotInd _ -> [] in
  subst_predicate (l,c) ccl tms

(*****************************************************************************)
(* We have pred = [X:=realargs;x:=c]P typed in Gamma1, x:I(realargs), Gamma2 *)
(* and we want to abstract P over y:t(x) typed in the same context to get    *)
(*                                                                           *)
(*    pred' = [X:=realargs;x':=c](y':t(x'))P[y:=y']                          *)
(*                                                                           *)
(* We first need to lift t(x) s.t. it is typed in Gamma, X:=rargs, x'        *)
(* then we have to replace x by x' in t(x) and y by y' in P                  *)
(*****************************************************************************)
let generalize_predicate (names,(nadep,_)) ny d tms ccl =
  if nadep=Anonymous then anomaly "Undetected dependency";
  let p = List.length names + 1 in
  let ccl = lift_predicate 1 ccl tms in
  regeneralize_index_predicate (ny+p+1) ccl tms

(*****************************************************************************)
(* We just matched over cur:ind(realargs) in the following matching problem  *)
(*                                                                           *)
(*   env |- match cur tms return ccl with ... end                            *)
(*                                                                           *)
(* and we want to build the predicate corresponding to the individual        *)
(* matching over cur                                                         *)
(*                                                                           *)
(*    pred = fun X:realargstyps x:ind(X)] PI tms.ccl                         *)
(*                                                                           *)
(* where pred is computed by abstract_predicate and PI tms.ccl by            *)
(* extract_predicate                                                         *)
(*****************************************************************************)
let rec extract_predicate ccl = function
  | Alias (deppat,nondeppat,_,_)::tms ->
      (* substitution already done in build_branch *)
      extract_predicate ccl tms
  | Abstract (i,d)::tms ->
      mkProd_or_LetIn d (extract_predicate ccl tms)
  | Pushed ((cur,NotInd _),_,(dep,_))::tms ->
      let tms = if dep<>Anonymous then lift_tomatch_stack 1 tms else tms in
      let pred = extract_predicate ccl tms in
      if dep<>Anonymous then subst1 cur pred else pred
  | Pushed ((cur,IsInd (_,IndType(_,realargs),_)),_,(dep,_))::tms ->
      let realargs = List.rev realargs in
      let k = if dep<>Anonymous then 1 else 0 in
      let tms = lift_tomatch_stack (List.length realargs + k) tms in
      let pred = extract_predicate ccl tms in
      substl (if dep<>Anonymous then cur::realargs else realargs) pred
  | [] ->
      ccl

let abstract_predicate env sigma indf cur (names,(nadep,_)) tms ccl =
  let sign = make_arity_signature env true indf in
  (* n is the number of real args + 1 *)
  let n = List.length sign in
  let tms = lift_tomatch_stack n tms in
  let tms =
    match kind_of_term cur with
      | Rel i -> relocate_index_tomatch (i+n) 1 tms
      | _ -> (* Initial case *) tms in
  let sign = List.map2 (fun na (_,c,t) -> (na,c,t)) (nadep::names) sign in
  let ccl = if nadep <> Anonymous then ccl else lift_predicate 1 ccl tms in
  let pred = extract_predicate ccl tms in
  it_mkLambda_or_LetIn_name env pred sign

let known_dependent (_,dep) = (dep = KnownDep)

(* [expand_arg] is used by [specialize_predicate]
   if Yk denotes [Xk;xk] or [Xk],
   it replaces gamma, x1...xn, x1...xk Yk+1...Yn |- pred
   by gamma, x1...xn, x1...xk-1 [Xk;xk] Yk+1...Yn |- pred (if dep) or
   by gamma, x1...xn, x1...xk-1 [Xk] Yk+1...Yn |- pred (if not dep) *)

let expand_arg tms (p,ccl) ((_,t),_,na) =
  let k = length_of_tomatch_type_sign na t in
  (p+k,liftn_predicate (k-1) (p+1) ccl tms)

let adjust_impossible_cases pb pred tomatch submat =
  if submat = [] then
    match kind_of_term (whd_evar !(pb.evdref) pred) with
    | Evar (evk,_) when snd (evar_source evk !(pb.evdref)) = ImpossibleCase ->
	let default = (coq_unit_judge ()).uj_type in
	pb.evdref := Evd.define evk default !(pb.evdref);
      (* we add an "assert false" case *)
      let pats = List.map (fun _ -> PatVar (dummy_loc,Anonymous)) tomatch in
      let aliasnames =
	map_succeed (function Alias _ -> Anonymous | _ -> failwith"") tomatch
      in
      [ { patterns = pats;
          rhs = { rhs_env = pb.env;
	          rhs_vars = [];
		  avoid_ids = [];
		  it = None };
	  alias_stack = Anonymous::aliasnames;
	  eqn_loc = dummy_loc;
	  used = ref false } ]
    | _ ->
	submat
  else
    submat

(*****************************************************************************)
(* Let  pred = PI [X;x:I(X)]. PI tms. P  be a typing predicate for the       *)
(* following pattern-matching problem:                                       *)
(*                                                                           *)
(*  Gamma |- match Pushed(c:I(V)) as x in I(X), tms return pred with...end   *)
(*                                                                           *)
(* where the branch with constructor Ci:(x1:T1)...(xn:Tn)->I(realargsi)      *)
(* is considered. Assume each Ti is some Ii(argsi) with Ti:PI Ui. sort_i     *)
(* We let subst = X:=realargsi;x:=Ci(x1,...,xn) and replace pred by          *)
(*                                                                           *)
(* pred' = PI [X1:Ui;x1:I1(X1)]...[Xn:Un;xn:In(Xn)]. (PI tms. P)[subst]      *)
(*                                                                           *)
(* s.t. the following well-typed sub-pattern-matching problem is obtained    *)
(*                                                                           *)
(* Gamma,x'1..x'n |-                                                         *)
(*   match                                                                   *)
(*      Pushed(x'1) as x1 in I(X1),                                          *)
(*      ..,                                                                  *)
(*      Pushed(x'n) as xn in I(Xn),                                          *)
(*      tms                                                                  *)
(*      return pred'                                                         *)
(*   with .. end                                                             *)
(*                                                                           *)
(*****************************************************************************)
let specialize_predicate newtomatchs (names,(depna,_)) arsign cs tms ccl =
  (* Assume some gamma st: gamma |- PI [X,x:I(X)]. PI tms. ccl *)
  let nrealargs = List.length names in
  let k = nrealargs + (if depna<>Anonymous then 1 else 0) in
  (* We adjust pred st: gamma, x1..xn |- PI [X,x:I(X)]. PI tms. ccl' *)
  (* so that x can later be instantiated by Ci(x1..xn) *)
  (* and X by the realargs for Ci *)
  let n = cs.cs_nargs in
  let ccl' = liftn_predicate n (k+1) ccl tms in
  (* We prepare the substitution of X and x:I(X) *)
  let realargsi =
    if nrealargs <> 0 then
      adjust_subst_to_rel_context arsign (Array.to_list cs.cs_concl_realargs)
    else
      [] in
  let copti =
    if depna<>Anonymous then Some (build_dependent_constructor cs) else None in
  (* The substituends realargsi, copti are all defined in gamma, x1...xn *)
  (* We need _parallel_ bindings to get gamma, x1...xn |- PI tms. ccl'' *)
  (* Note: applying the substitution in tms is not important (is it sure?) *)
  let ccl'' =
    whd_betaiota Evd.empty (subst_predicate (realargsi, copti) ccl' tms) in
  (* We adjust ccl st: gamma, x'1..x'n, x1..xn, tms |- ccl'' *)
  let ccl''' = liftn_predicate n (n+1) ccl'' tms in
  (* We finally get gamma,x'1..x'n,x |- [X1;x1:I(X1)]..[Xn;xn:I(Xn)]pred'''*)
  snd (List.fold_left (expand_arg tms) (1,ccl''') newtomatchs)

let find_predicate loc env evdref p current (IndType (indf,realargs)) dep tms =
  let pred = abstract_predicate env !evdref indf current dep tms p in
  (pred, whd_betaiota !evdref
           (applist (pred, realargs@[current])))

(* Take into account that a type has been discovered to be inductive, leading
   to more dependencies in the predicate if the type has indices *)
let adjust_predicate_from_tomatch tomatch (current,typ as ct) pb =
  let ((_,oldtyp),deps,((nadep,_) as dep)) = tomatch in
  match typ, oldtyp with
  | IsInd (_,_,names), NotInd _ ->
      let k = if nadep <> Anonymous then 2 else 1 in
      let n = List.length names in
      { pb with pred = liftn_predicate n k pb.pred pb.tomatch },
      (ct,List.map (fun i -> if i >= k then i+n else i) deps,dep)
  | _ ->
      pb, (ct,deps,dep)

(* Remove commutative cuts that turn out to be non-dependent after
   some evars have been instantiated *)

let ungeneralize_branch n (sign,body) cs =
  match kind_of_term body with
  | Lambda (_,_,c) | LetIn (_,_,_,c) ->
      (sign,subst1 (mkRel (n+cs.cs_nargs)) c)
  | Case _ ->
      (* Typically case of a match *)
      (* Not clear what to do; is it avoidable? should we go down the match? *)
      (sign,applist (body,[mkRel (n+cs.cs_nargs)]))
  | _ -> assert false

let postprocess_dependencies evd current brs tomatch pred deps cs =
  let rec aux k brs tomatch pred tocheck deps = match deps, tomatch with
  | [], _ -> brs,tomatch,pred,[]
  | n::deps, Abstract (i,d) :: tomatch ->
      let d = map_rel_declaration (nf_evar evd) d in
      if List.exists (fun c -> dependent_decl (lift k c) d) tocheck then
        (* The dependency is real *)
        let brs,tomatch,pred,inst = aux (k+1) brs tomatch pred (mkRel n::tocheck) deps in
        let inst = if pi2 d = None then mkRel n::inst else inst in
        brs, Abstract (i,d) :: tomatch, pred, inst
      else
        (* Finally, no dependency remains, so, we can replace the generalized *)
        (* terms by its actual value in both the remaining terms to match and *)
        (* the bodies of the Case *)
        let pred = lift_predicate (-1) pred tomatch in
        let tomatch = relocate_index_tomatch 1 (n+1) tomatch in
        let tomatch = lift_tomatch_stack (-1) tomatch in
        let brs = array_map2 (ungeneralize_branch n) brs cs in
        aux k brs tomatch pred tocheck deps
  | _ -> assert false
  in aux 0 brs tomatch pred [current] deps

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

let group_equations pb ind current cstrs mat =
  let mat =
    if first_clause_irrefutable pb.env mat then [List.hd mat] else mat in
  let brs = Array.create (Array.length cstrs) [] in
  let only_default = ref true in
  let _ =
    List.fold_right (* To be sure it's from bottom to top *)
      (fun eqn () ->
	 let rest = remove_current_pattern eqn in
	 let pat = current_pattern eqn in
	 match check_and_adjust_constructor pb.env ind cstrs pat with
	   | PatVar (_,name) ->
	       (* This is a default clause that we expand *)
	       for i=1 to Array.length cstrs do
		 let args = make_anonymous_patvars cstrs.(i-1).cs_nargs in
		 brs.(i-1) <- (args, rest) :: brs.(i-1)
	       done
	   | PatCstr (loc,((_,i)),args,_) ->
	       (* This is a regular clause *)
	       only_default := false;
	       brs.(i-1) <- (args,rest) :: brs.(i-1)) mat () in
  (brs,!only_default)

(************************************************************************)
(* Here starts the pattern-matching compilation algorithm *)

(* Abstracting over dependent subterms to match *)
let rec generalize_problem names pb = function
  | [] -> pb
  | i::l ->
      let d = map_rel_declaration (lift i) (Environ.lookup_rel i pb.env) in
      let d = on_pi3 (whd_betaiota !(pb.evdref)) d in (* for better rendering *)
      let pb' = generalize_problem names pb l in
      let tomatch = lift_tomatch_stack 1 pb'.tomatch in
      let tomatch = relocate_index_tomatch (i+1) 1 tomatch in
      { pb' with
	  tomatch = Abstract (i,d) :: tomatch;
          pred = generalize_predicate names i d pb'.tomatch pb'.pred  }

(* No more patterns: typing the right-hand side of equations *)
let build_leaf pb =
  let rhs = extract_rhs pb in
  let j = pb.typing_function (mk_tycon pb.pred) rhs.rhs_env pb.evdref rhs.it in
  j_nf_evar !(pb.evdref) j

(* Building the sub-problem when all patterns are variables *)
let shift_problem ((current,t),_,(nadep,_)) pb =
  {pb with
     tomatch = Alias (current,current,NonDepAlias,type_of_tomatch t)::pb.tomatch;
     pred = specialize_predicate_var (current,t,nadep) pb.tomatch pb.pred;
     history = push_history_pattern 0 AliasLeaf pb.history;
     mat = List.map remove_current_pattern pb.mat }

(* Build the sub-pattern-matching problem for a given branch "C x1..xn as x" *)
let build_branch current deps (realnames,dep) pb arsign eqns const_info =
  (* We remember that we descend through constructor C *)
  let alias_type =
    if Array.length const_info.cs_concl_realargs = 0
      & not (known_dependent dep) & deps = []
    then
      NonDepAlias
    else
      DepAlias
  in
  let history =
    push_history_pattern const_info.cs_nargs
      (AliasConstructor const_info.cs_cstr)
      pb.history in

  (* We prepare the matching on x1:T1 .. xn:Tn using some heuristic to *)
  (* build the name x1..xn from the names present in the equations *)
  (* that had matched constructor C *)
  let cs_args = const_info.cs_args in
  let names = get_names pb.env cs_args eqns in

  (* We build the matrix obtained by expanding the matching on *)
  (* "C x1..xn as x" followed by a residual matching on eqn into *)
  (* a matching on "x1 .. xn eqn" *)
  let submat = List.map (fun (tms,eqn) -> prepend_pattern tms eqn) eqns in
  let typs = List.map2 (fun (_,c,t) na -> (na,c,t)) cs_args names in

  let typs' =
    list_map_i (fun i d -> (mkRel i,map_rel_declaration (lift i) d)) 1 typs in

  (* We compute over which of x(i+1)..xn and x matching on xi will need a *)
  (* generalization *)
  let dep_sign =
    find_dependencies_signature
      (dependencies_in_rhs const_info.cs_nargs current pb.tomatch eqns)
      (List.rev typs') in

  (* The dependent term to subst in the types of the remaining UnPushed
     terms is relative to the current context enriched by topushs *)
  let ci = build_dependent_constructor const_info in

  (* We replace [(mkRel 1)] by its expansion [ci] *)
  (* and context "Gamma = Gamma1, current, Gamma2" by "Gamma;typs;curalias" *)
  (* This is done in two steps : first from "Gamma |- tms" *)
  (* into  "Gamma; typs; curalias |- tms" *)
  let tomatch = lift_tomatch_stack const_info.cs_nargs pb.tomatch in

  let tomatch = match kind_of_term current with
    | Rel i -> replace_tomatch (i+const_info.cs_nargs) ci tomatch
    | _ -> (* non-rel initial term *) tomatch in

  let pred_is_not_dep =
    noccur_predicate_between 1 (List.length realnames + 1) pb.pred tomatch in

  let typs' =
    List.map2
      (fun (tm,(na,c,t)) deps ->
	let dep = match dep with
	  | Name _ as na',k -> (if na <> Anonymous then na else na'),k
	  | Anonymous,KnownNotDep ->
	      if deps = [] && pred_is_not_dep then
		(Anonymous,KnownNotDep)
	      else
		(force_name na,KnownDep)
	  | _,_ -> anomaly "Inconsistent dependency" in
	((tm,NotInd(c,t)),deps,dep))
      typs' (List.rev dep_sign) in

  let pred =
    specialize_predicate typs' (realnames,dep) arsign const_info tomatch pb.pred in

  let currents = List.map (fun x -> Pushed x) typs' in

  let ind =
    appvect (
      applist (mkInd (inductive_of_constructor const_info.cs_cstr),
      List.map (lift const_info.cs_nargs) const_info.cs_params),
      const_info.cs_concl_realargs) in

  let cur_alias = lift (List.length typs) current in
  let currents = Alias (ci,cur_alias,alias_type,ind) :: currents in
  let tomatch = List.rev_append currents tomatch in

  let submat = adjust_impossible_cases pb pred tomatch submat in
  if submat = [] then
    raise_pattern_matching_error
      (dummy_loc, pb.env, NonExhaustive (complete_history history));

  typs,
  { pb with
      env = push_rels typs pb.env;
      tomatch = tomatch;
      pred = pred;
      history = history;
      mat = List.map (push_rels_eqn_with_names typs) submat }

(**********************************************************************
 INVARIANT:

  pb = { env, subst, tomatch, mat, ...}
  tomatch = list of Pushed (c:T) or Abstract (na:T) or Alias (c:T)

  "Pushed" terms and types are relative to env
  "Abstract" types are relative to env enriched by the previous terms to match

*)

(**********************************************************************)
(* Main compiling descent *)
let rec compile pb =
  match pb.tomatch with
    | (Pushed cur)::rest -> match_current { pb with tomatch = rest } cur
    | (Alias x)::rest -> compile_alias pb x rest
    | (Abstract (i,d))::rest -> compile_generalization pb i d rest
    | [] -> build_leaf pb

(* Case splitting *)
and match_current pb tomatch =
  let tm = adjust_tomatch_to_pattern pb tomatch in
  let pb,tomatch = adjust_predicate_from_tomatch tomatch tm pb in
  let ((current,typ),deps,dep) = tomatch in
  match typ with
    | NotInd (_,typ) ->
	check_all_variables typ pb.mat;
	compile (shift_problem tomatch pb)
    | IsInd (_,(IndType(indf,realargs) as indt),names) ->
	let mind,_ = dest_ind_family indf in
	let cstrs = get_constructors pb.env indf in
	let arsign, _ = get_arity pb.env indf in
	let eqns,onlydflt = group_equations pb mind current cstrs pb.mat in
	if (Array.length cstrs <> 0 or pb.mat <> []) & onlydflt  then
	  compile (shift_problem tomatch pb)
	else
          let _constraints = Array.map (solve_constraints indt) cstrs in

	  (* We generalize over terms depending on current term to match *)
	  let pb = generalize_problem (names,dep) pb deps in

	  (* We compile branches *)
	  let brvals = array_map2 (compile_branch current (names,dep) deps pb arsign) eqns cstrs in
	  (* We build the (elementary) case analysis *)
          let brvals,tomatch,pred,inst =
            postprocess_dependencies !(pb.evdref) current
              brvals pb.tomatch pb.pred deps cstrs in
          let brvals = Array.map (fun (sign,body) ->
            it_mkLambda_or_LetIn body sign) brvals in
	  let (pred,typ) =
	    find_predicate pb.caseloc pb.env pb.evdref
	      pred current indt (names,dep) tomatch in
	  let ci = make_case_info pb.env mind pb.casestyle in
	  let pred = nf_betaiota !(pb.evdref) pred in
	  let case = mkCase (ci,pred,current,brvals) in
	  Typing.check_allowed_sort pb.env !(pb.evdref) mind current pred;
	  { uj_val = applist (case, inst);
	    uj_type = prod_applist typ inst }

and compile_branch current names deps pb arsign eqns cstr =
  let sign, pb = build_branch current deps names pb arsign eqns cstr in
  sign, (compile pb).uj_val

(* Abstract over a declaration before continuing splitting *)
and compile_generalization pb i d rest =
  let pb =
    { pb with
       env = push_rel d pb.env;
       tomatch = rest;
       mat = List.map (push_generalized_decl_eqn pb.env i d) pb.mat } in
  let j = compile pb in
  { uj_val = mkLambda_or_LetIn d j.uj_val;
    uj_type = mkProd_or_LetIn d j.uj_type }

and compile_alias pb aliases rest =
  let history = simplify_history pb.history in
  let sign, newenv, mat = insert_aliases pb.env !(pb.evdref) aliases pb.mat in
  let n = List.length sign in
  let tomatch = lift_tomatch_stack n rest in
  let pb =
    {pb with
       env = newenv;
       tomatch = tomatch;
       pred = lift_predicate n pb.pred tomatch;
       history = history;
       mat = mat } in
  let j = compile pb in
  List.fold_left mkSpecialLetInJudge j sign

(* pour les alias des initiaux, enrichir les env de ce qu'il faut et
substituer après par les initiaux *)

(**************************************************************************)
(* Preparation of the pattern-matching problem                            *)

(* builds the matrix of equations testing that each eqn has n patterns
 * and linearizing the _ patterns.
 * Syntactic correctness has already been done in astterm *)
let matx_of_eqns env tomatchl eqns =
  let build_eqn (loc,ids,lpat,rhs) =
    let initial_lpat,initial_rhs = lpat,rhs in
    let initial_rhs = rhs in
    let rhs =
      { rhs_env = env;
        rhs_vars = free_glob_vars initial_rhs;
	avoid_ids = ids@(ids_of_named_context (named_context env));
	it = Some initial_rhs } in
    { patterns = initial_lpat;
      alias_stack = [];
      eqn_loc = loc;
      used = ref false;
      rhs = rhs }
  in List.map build_eqn eqns

(***************** Building an inversion predicate ************************)

(* Let "match t1 in I1 u11..u1n_1 ... tm in Im um1..umn_m with ... end : T"
   be a pattern-matching problem. We assume that each uij can be
   decomposed under the form pij(vij1..vijq_ij) where pij(aij1..aijq_ij)
   is a pattern depending on some variables aijk and the vijk are
   instances of these variables.  We also assume that each ti has the
   form of a pattern qi(wi1..wiq_i) where qi(bi1..biq_i) is a pattern
   depending on some variables bik and the wik are instances of these
   variables (in practice, there is no reason that ti is already
   constructed and the qi will be degenerated).

   We then look for a type U(..a1jk..b1 .. ..amjk..bm) so that
   T = U(..v1jk..t1 .. ..vmjk..tm). This a higher-order matching
   problem with a priori different solutions (one of them if T itself!).

   We finally invert the uij and the ti and build the return clause

   phi(x11..x1n_1y1..xm1..xmn_mym) =
     match x11..x1n_1 y1 .. xm1..xmn_m ym with
         | p11..p1n_1 q1 .. pm1..pmn_m qm => U(..a1jk..b1 .. ..amjk..bm)
         |  _ .. _    _  ..  _ .. _    _  => True
    end

   so that "phi(u11..u1n_1t1..um1..umn_mtm) = T" (note that the clause
   returning True never happens and any inhabited type can be put instead).
*)

let adjust_to_extended_env_and_remove_deps env extenv subst t =
  let n = rel_context_length (rel_context env) in
  let n' = rel_context_length (rel_context extenv) in
  (* We first remove the bindings that are dependently typed (they are
     difficult to manage and it is not sure these are so useful in practice);
     Notes:
     - [subst] is made of pairs [(id,u)] where id is a name in [extenv] and
       [u] a term typed in [env];
     - [subst0] is made of items [(p,u,(u,ty))] where [ty] is the type of [u]
       and both are adjusted to [extenv] while [p] is the index of [id] in
       [extenv] (after expansion of the aliases) *)
  let subst0 = map_succeed (fun (x,u) ->
    (* d1 ... dn dn+1 ... dn'-p+1 ... dn' *)
    (* \--env-/          (= x:ty)         *)
    (* \--------------extenv------------/ *)
    let (p,_,_) = lookup_rel_id x (rel_context extenv) in
    let rec traverse_local_defs p =
      match pi2 (lookup_rel p extenv) with
      | Some c -> assert (isRel c); traverse_local_defs (p + destRel c)
      | None -> p in
    let p = traverse_local_defs p in
    let u = lift (n'-n) u in
    (p,u,expand_vars_in_term extenv u)) subst in
  let t0 = lift (n'-n) t in
  (subst0,t0)

let push_binder d (k,env,subst) =
  (k+1,push_rel d env,List.map (fun (na,u,d) -> (na,lift 1 u,d)) subst)

let rec list_assoc_in_triple x = function
    [] -> raise Not_found
  | (a,b,_)::l -> if compare a x = 0 then b else list_assoc_in_triple x l

(* Let vijk and ti be a set of dependent terms and T a type, all
 * defined in some environment env. The vijk and ti are supposed to be
 * instances for variables aijk and bi.
 *
 * [abstract_tycon Gamma0 Sigma subst T Gamma] looks for U(..v1jk..t1 .. ..vmjk..tm)
 * defined in some extended context
 * "Gamma0, ..a1jk:V1jk.. b1:W1 .. ..amjk:Vmjk.. bm:Wm"
 * such that env |- T = U(..v1jk..t1 .. ..vmjk..tm). To not commit to
 * a particular solution, we replace each subterm t in T that unifies with
 * a subset u1..ul of the vijk and ti by a special evar
 * ?id(x=t;c1:=c1,..,cl=cl) defined in context Gamma0,x,c1,...,cl |- ?id
 * (where the c1..cl are the aijk and bi matching the u1..ul), and
 * similarly for each ti.
*)

let abstract_tycon loc env evdref subst _tycon extenv t =
  let sigma = !evdref in
  let t = nf_betaiota sigma t in (* it helps in some cases to remove K-redex *)
  let subst0,t0 = adjust_to_extended_env_and_remove_deps env extenv subst t in
  (* We traverse the type T of the original problem Xi looking for subterms
     that match the non-constructor part of the constraints (this part
     is in subst); these subterms are the "good" subterms and we replace them
     by an evar that may depend (and only depend) on the corresponding
     convertible subterms of the substitution *)
  let rec aux (k,env,subst as x) t =
    let t = whd_evar !evdref t in match kind_of_term t with
    | Rel n when pi2 (lookup_rel n env) <> None ->
        map_constr_with_full_binders push_binder aux x t
    | Evar ev ->
        let ty = get_type_of env sigma t in
        let inst =
	  list_map_i
	    (fun i _ ->
              try list_assoc_in_triple i subst0 with Not_found -> mkRel i)
              1 (rel_context env) in
        let ev = e_new_evar evdref env ~src:(loc, CasesType) ty in
        evdref := add_conv_pb (Reduction.CONV,env,substl inst ev,t) !evdref;
        ev
    | _ ->
    let good = List.filter (fun (_,u,_) -> is_conv_leq env sigma t u) subst in
    if good <> [] then
      let u = pi3 (List.hd good) in (* u is in extenv *)
      let vl = List.map pi1 good in
      let ty = lift (-k) (aux x (get_type_of env !evdref t)) in
      let depvl = free_rels ty in
      let inst =
	list_map_i
	  (fun i _ -> if List.mem i vl then u else mkRel i) 1
	  (rel_context extenv) in
      let rel_filter =
	List.map (fun a -> not (isRel a) || dependent a u
                           || Intset.mem (destRel a) depvl) inst in
      let named_filter =
	List.map (fun (id,_,_) -> dependent (mkVar id) u)
	  (named_context extenv) in
      let filter = rel_filter@named_filter in
      let ev =
	e_new_evar evdref extenv ~src:(loc, CasesType) ~filter:filter ty in
      evdref := add_conv_pb (Reduction.CONV,extenv,substl inst ev,u) !evdref;
      lift k ev
    else
      map_constr_with_full_binders push_binder aux x t in
  aux (0,extenv,subst0) t0

let build_tycon loc env tycon_env subst tycon extenv evdref t =
  let t,tt = match t with
    | None ->
	(* This is the situation we are building a return predicate and
           we are in an impossible branch *)
	let n = rel_context_length (rel_context env) in
	let n' = rel_context_length (rel_context tycon_env) in
        let tt = new_Type () in
	let impossible_case_type =
	  e_new_evar evdref env ~src:(loc,ImpossibleCase) tt in
	(lift (n'-n) impossible_case_type, tt)
    | Some t ->
        let t = abstract_tycon loc tycon_env evdref subst tycon extenv t in
        let evd,tt = Typing.e_type_of extenv !evdref t in
        evdref := evd;
        (t,tt) in
  { uj_val = t; uj_type = tt }

(* For a multiple pattern-matching problem Xi on t1..tn with return
 * type T, [build_inversion_problem Gamma Sigma (t1..tn) T] builds a return
 * predicate for Xi that is itself made by an auxiliary
 * pattern-matching problem of which the first clause reveals the
 * pattern structure of the constraints on the inductive types of the t1..tn,
 * and the second clause is a wildcard clause for catching the
 * impossible cases. See above "Building an inversion predicate" for
 * further explanations
 *)

let build_inversion_problem loc env sigma tms t =
  let make_patvar t (subst,avoid) =
    let id = next_name_away (named_hd env t Anonymous) avoid in
    PatVar (dummy_loc,Name id), ((id,t)::subst, id::avoid) in
  let rec reveal_pattern t (subst,avoid as acc) =
    match kind_of_term (whd_betadeltaiota env sigma t) with
    | Construct cstr -> PatCstr (dummy_loc,cstr,[],Anonymous), acc
    | App (f,v) when isConstruct f ->
	let cstr = destConstruct f in
	let n = constructor_nrealargs env cstr in
	let l = list_lastn n (Array.to_list v) in
	let l,acc = list_fold_map' reveal_pattern l acc in
	PatCstr (dummy_loc,cstr,l,Anonymous), acc
    | _ -> make_patvar t acc in
  let rec aux n env acc_sign tms acc =
    match tms with
    | [] -> [], acc_sign, acc
    | (t, IsInd (_,IndType(indf,realargs),_)) :: tms ->
	let patl,acc = list_fold_map' reveal_pattern realargs acc in
	let pat,acc = make_patvar t acc in
	let indf' = lift_inductive_family n indf in
	let sign = make_arity_signature env true indf' in
	let p = List.length realargs in
	let env' = push_rels sign env in
	let patl',acc_sign,acc = aux (n+p+1) env' (sign@acc_sign) tms acc in
	patl@pat::patl',acc_sign,acc
    | (t, NotInd (bo,typ)) :: tms ->
	aux n env acc_sign tms acc in
  let avoid0 = ids_of_context env in
  (* [patl] is a list of patterns revealing the substructure of
     constructors present in the constraints on the type of the
     multiple terms t1..tn that are matched in the original problem;
     [subst] is the substitution of the free pattern variables in
     [patl] that returns the non-constructor parts of the constraints.
     Especially, if the ti has type I ui1..uin_i, and the patterns associated
     to ti are pi1..pin_i, then subst(pij) is uij; the substitution is
     useful to recognize which subterms of the whole type T of the original
     problem have to be abstracted *)
  let patl,sign,(subst,avoid) = aux 0 env [] tms ([],avoid0) in
  let n = List.length sign in

  let decls =
    list_map_i (fun i d -> (mkRel i,map_rel_declaration (lift i) d)) 1 sign in
  let decls = List.rev decls in
  let dep_sign = find_dependencies_signature (list_make n true) decls in

  let pb_env = push_rels sign env in
  let sub_tms =
    List.map2 (fun deps (tm,(na,b,t)) ->
      let typ =
	if b<>None then NotInd (None,t) else
	  try try_find_ind pb_env sigma t None
	  with Not_found -> NotInd (None,t) in
      let na_dep =
	if deps = [] then (Anonymous,KnownNotDep) else (force_name na,KnownDep)
      in
      Pushed ((tm,typ),deps,na_dep))
      dep_sign decls in
  let subst = List.map (fun (na,t) -> (na,lift n t)) subst in
  (* [eqn1] is the first clause of the auxiliary pattern-matching that
     serves as skeleton for the return type: [patl] is the
     substructure of constructors extracted from the list of
     constraints on the inductive types of the multiple terms matched
     in the original pattern-matching problem Xi *)
  let eqn1 =
    { patterns = patl;
      alias_stack = [];
      eqn_loc = dummy_loc;
      used = ref false;
      rhs = { rhs_env = pb_env;
              (* we assume all vars are used; in practice we discard dependent
		 vars so that the field rhs_vars is normally not used *)
              rhs_vars = List.map fst subst;
              avoid_ids = avoid;
	      it = Some (lift n t) } } in
  (* [eqn2] is the default clause of the auxiliary pattern-matching: it will
     catch the clauses of the original pattern-matching problem Xi whose
     type constraints are incompatible with the constraints on the
     inductive types of the multiple terms matched in Xi *)
  let eqn2 =
    { patterns = List.map (fun _ -> PatVar (dummy_loc,Anonymous)) patl;
      alias_stack = [];
      eqn_loc = dummy_loc;
      used = ref false;
      rhs = { rhs_env = pb_env;
              rhs_vars = [];
	      avoid_ids = avoid0;
	      it = None } } in
  (* [pb] is the auxiliary pattern-matching serving as skeleton for the
      return type of the original problem Xi *)
  let evdref = ref sigma in
  let pb =
    { env       = pb_env;
      evdref    = evdref;
      pred      = new_Type();
      tomatch   = sub_tms;
      history   = start_history n;
      mat       = [eqn1;eqn2];
      caseloc   = loc;
      casestyle = RegularStyle;
      typing_function = build_tycon loc env pb_env subst} in
  let pred = (compile pb).uj_val in
  (!evdref,pred)

(* Here, [pred] is assumed to be in the context built from all *)
(* realargs and terms to match *)
let build_initial_predicate knowndep allnames pred =
  let nar = List.fold_left (fun n names -> List.length names + n) 0 allnames in
  let rec buildrec n pred deps = function
    | [] -> List.rev deps,pred
    | (na::realnames)::lnames ->
        let n' = n + List.length realnames in
        let pred, dep =
          if dependent (mkRel (nar-n')) pred then pred, (force_name na,knowndep)
          else liftn (-1) (nar-n') pred, (Anonymous,KnownNotDep) in
        buildrec (n'+1) pred (dep::deps) lnames
    | _ -> assert false
  in buildrec 0 pred [] allnames

let extract_arity_signature env0 tomatchl tmsign =
  let get_one_sign n tm (na,t) =
    match tm with
      | NotInd (bo,typ) ->
	  (match t with
	    | None -> [na,Option.map (lift n) bo,lift n typ]
	    | Some (loc,_,_,_) ->
 	    user_err_loc (loc,"",
	    str"Unexpected type annotation for a term of non inductive type."))
      | IsInd (term,IndType(indf,realargs),_) ->
          let indf' = lift_inductive_family n indf in
	  let (ind,_) = dest_ind_family indf' in
	  let nparams_ctxt,nrealargs_ctxt = inductive_nargs env0 ind in
	  let arsign = fst (get_arity env0 indf') in
	  let realnal =
	    match t with
	      | Some (loc,ind',nparams,realnal) ->
		  if ind <> ind' then
		    user_err_loc (loc,"",str "Wrong inductive type.");
		  if nparams_ctxt <> nparams
		    or nrealargs_ctxt <> List.length realnal then
		      anomaly "Ill-formed 'in' clause in cases";
		  List.rev realnal
	      | None -> list_make nrealargs_ctxt Anonymous in
	  (na,None,build_dependent_inductive env0 indf')
	  ::(List.map2 (fun x (_,c,t) ->(x,c,t)) realnal arsign) in
  let rec buildrec n = function
    | [],[] -> []
    | (_,tm)::ltm, x::tmsign ->
	let l = get_one_sign n tm x in
	l :: buildrec (n + List.length l) (ltm,tmsign)
    | _ -> assert false
  in List.rev (buildrec 0 (tomatchl,tmsign))

let inh_conv_coerce_to_tycon loc env evdref j tycon =
  match tycon with
    | Some p ->
	let (evd',j) = Coercion.inh_conv_coerce_to loc env !evdref j p in
          evdref := evd';
          j
    | None -> j

(* We put the tycon inside the arity signature, possibly discovering dependencies. *)

let prepare_predicate_from_arsign_tycon loc tomatchs sign arsign c =
  let nar = List.fold_left (fun n sign -> List.length sign + n) 0 arsign in
  let subst, len =
    List.fold_left2 (fun (subst, len) (tm, tmtype) sign ->
      let signlen = List.length sign in
	match kind_of_term tm with
	  | Rel n when dependent tm c
		&& signlen = 1 (* The term to match is not of a dependent type itself *) ->
	      ((n, len) :: subst, len - signlen)
	  | Rel n when signlen > 1 (* The term is of a dependent type,
				      maybe some variable in its type appears in the tycon. *) ->
	      (match tmtype with
		  NotInd _ -> (subst, len - signlen)
		| IsInd (_, IndType(indf,realargs),_) ->
		    let subst =
		      if dependent tm c && List.for_all isRel realargs
		      then (n, 1) :: subst else subst
		    in
		      List.fold_left
			(fun (subst, len) arg ->
			  match kind_of_term arg with
			  | Rel n when dependent arg c ->
			      ((n, len) :: subst, pred len)
			  | _ -> (subst, pred len))
			(subst, len) realargs)
	  | _ -> (subst, len - signlen))
      ([], nar) tomatchs arsign
  in
  let rec predicate lift c =
    match kind_of_term c with
      | Rel n when n > lift ->
	  (try
	      (* Make the predicate dependent on the matched variable *)
	      let idx = List.assoc (n - lift) subst in
		mkRel (idx + lift)
	    with Not_found ->
	      (* A variable that is not matched, lift over the arsign. *)
	      mkRel (n + nar))
      | _ ->
	  map_constr_with_binders succ predicate lift c
  in predicate 0 c


(* Builds the predicate. If the predicate is dependent, its context is
 * made of 1+nrealargs assumptions for each matched term in an inductive
 * type and 1 assumption for each term not _syntactically_ in an
 * inductive type.

 * Each matched terms are independently considered dependent or not.

 * A type constraint but no annotation case: we try to specialize the
 * tycon to make the predicate if it is not closed.
 *)

let prepare_predicate loc typing_fun sigma env tomatchs sign tycon pred =
  let arsign = extract_arity_signature env tomatchs sign in
  let names = List.rev (List.map (List.map pi1) arsign) in
  let preds =
    match pred, tycon with
    (* No type annotation *)
    | None, Some (None, t) when not (noccur_with_meta 0 max_int t) ->
	(* If the tycon is not closed w.r.t real variables, we try *)
        (* two different strategies *)
	(* First strategy: we abstract the tycon wrt to the dependencies *)
        let pred1 =
          prepare_predicate_from_arsign_tycon loc tomatchs sign arsign t in
	(* Second strategy: we build an "inversion" predicate *)
	let sigma2,pred2 = build_inversion_problem loc env sigma tomatchs t in
	[sigma, KnownDep, pred1; sigma2, DepUnknown, pred2]
    | None, _ ->
	(* No dependent type constraint, or no constraints at all: *)
	(* we use two strategies *)
        let sigma,t = match tycon with
	| Some (None, t) -> sigma,t
	| _ -> new_type_evar sigma env ~src:(loc, CasesType) in
        (* First strategy: we build an "inversion" predicate *)
	let sigma1,pred1 = build_inversion_problem loc env sigma tomatchs t in
	(* Second strategy: we directly use the evar as a non dependent pred *)
        let pred2 = lift (List.length names) t in
	[sigma1, DepUnknown, pred1; sigma, KnownNotDep, pred2]
    (* Some type annotation *)
    | Some rtntyp, _ ->
      (* We extract the signature of the arity *)
      let envar = List.fold_right push_rels arsign env in
      let sigma, newt = new_sort_variable sigma in
      let evdref = ref sigma in
      let predcclj = typing_fun (mk_tycon (mkSort newt)) envar evdref rtntyp in
      let sigma = Option.cata (fun tycon ->
          let na = (Name (id_of_string "x"),KnownNotDep) in
          let tms = List.map (fun tm -> Pushed(tm,[],na)) tomatchs in
          let predinst = extract_predicate predcclj.uj_val tms in
          Coercion.inh_conv_coerces_to loc env !evdref predinst tycon)
        !evdref tycon in
      let predccl = (j_nf_evar sigma predcclj).uj_val in
      [sigma, KnownDep, predccl]
  in
  List.map
    (fun (sigma,dep,pred) ->
      let (nal,pred) = build_initial_predicate dep names pred in
      sigma,nal,pred)
    preds

(**************************************************************************)
(* Main entry of the matching compilation                                 *)

let compile_cases loc style (typing_fun, evdref) tycon env (predopt, tomatchl, eqns) =

  (* We build the matrix of patterns and right-hand side *)
  let matx = matx_of_eqns env tomatchl eqns in

  (* We build the vector of terms to match consistently with the *)
  (* constructors found in patterns *)
  let tomatchs = coerce_to_indtype typing_fun evdref env matx tomatchl in

  (* If an elimination predicate is provided, we check it is compatible
     with the type of arguments to match; if none is provided, we
     build alternative possible predicates *)
  let sign = List.map snd tomatchl in
  let preds = prepare_predicate loc typing_fun !evdref env tomatchs sign tycon predopt in

  let compile_for_one_predicate (sigma,nal,pred) =
    (* We push the initial terms to match and push their alias to rhs' envs *)
    (* names of aliases will be recovered from patterns (hence Anonymous *)
    (* here) *)

    let initial_pushed = List.map2 (fun tm na -> Pushed(tm,[],na)) tomatchs nal in

    (* A typing function that provides with a canonical term for absurd cases*)
    let typing_fun tycon env evdref = function
    | Some t ->	typing_fun tycon env evdref t
    | None -> coq_unit_judge () in

    let myevdref = ref sigma in

    let pb =
      { env       = env;
        evdref    = myevdref;
	pred      = pred;
	tomatch   = initial_pushed;
	history   = start_history (List.length initial_pushed);
	mat       = matx;
	caseloc   = loc;
	casestyle = style;
	typing_function = typing_fun } in

    let j = compile pb in
    evdref := !myevdref;
    j in

  (* Return the term compiled with the first possible elimination  *)
  (* predicate for which the compilation succeeds *)
  let j = list_try_compile compile_for_one_predicate preds in

  (* We check for unused patterns *)
  List.iter (check_unused_pattern env) matx;

  (* We coerce to the tycon (if an elim predicate was provided) *)
  inh_conv_coerce_to_tycon loc env evdref j tycon

end
