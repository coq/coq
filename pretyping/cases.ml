(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Nameops
open Term
open Vars
open Context
open Termops
open Namegen
open Declarations
open Inductiveops
open Environ
open Reductionops
open Type_errors
open Glob_term
open Glob_ops
open Retyping
open Pretype_errors
open Evarutil
open Evarsolve
open Evarconv
open Evd

(* Pattern-matching errors *)

type pattern_matching_error =
  | BadPattern of constructor * constr
  | BadConstructor of constructor * inductive
  | WrongNumargConstructor of constructor * int
  | WrongNumargInductive of inductive * int
  | UnusedClause of cases_pattern list
  | NonExhaustive of cases_pattern list
  | CannotInferPredicate of (constr * types) array

exception PatternMatchingError of env * evar_map * pattern_matching_error

let raise_pattern_matching_error (loc,env,sigma,te) =
  Loc.raise loc (PatternMatchingError(env,sigma,te))

let error_bad_pattern_loc loc env sigma cstr ind =
  raise_pattern_matching_error
    (loc, env, sigma, BadPattern (cstr,ind))

let error_bad_constructor_loc loc env cstr ind =
  raise_pattern_matching_error
    (loc, env, Evd.empty, BadConstructor (cstr,ind))

let error_wrong_numarg_constructor_loc loc env c n =
  raise_pattern_matching_error (loc, env, Evd.empty, WrongNumargConstructor(c,n))

let error_wrong_numarg_inductive_loc loc env c n =
  raise_pattern_matching_error (loc, env, Evd.empty, WrongNumargInductive(c,n))

let rec list_try_compile f = function
  | [a] -> f a
  | [] -> anomaly (str "try_find_f")
  | h::t ->
      try f h
      with UserError _ | TypeError _ | PretypeError _ | PatternMatchingError _ ->
	    list_try_compile f t

let force_name =
  let nx = Name default_dependent_ident in function Anonymous -> nx | na -> na

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
  List.make n (PatVar (Loc.ghost,Anonymous))

(* We have x1:t1...xn:tn,xi':ti,y1..yk |- c and re-generalize
   over xi:ti to get x1:t1...xn:tn,xi':ti,y1..yk |- c[xi:=xi'] *)

let relocate_rel n1 n2 k j = if Int.equal j (n1 + k) then n2+k else j

let rec relocate_index n1 n2 k t = match kind_of_term t with
  | Rel j when Int.equal j (n1 + k) -> mkRel (n2+k)
  | Rel j when j < n1+k -> t
  | Rel j when j > n1+k -> t
  | _ -> map_constr_with_binders succ (relocate_index n1 n2) k t

(**********************************************************************)
(* Structures used in compiling pattern-matching *)

type 'a rhs =
    { rhs_env    : env;
      rhs_vars   : Id.t list;
      avoid_ids  : Id.t list;
      it         : 'a option}

type 'a equation =
    { patterns     : cases_pattern list;
      rhs          : 'a rhs;
      alias_stack  : Name.t list;
      eqn_loc      : Loc.t;
      used         : bool ref }

type 'a matrix = 'a equation list

(* 1st argument of IsInd is the original ind before extracting the summary *)
type tomatch_type =
  | IsInd of types * inductive_type * Name.t list
  | NotInd of constr option * types

(* spiwack: The first argument of [Pushed] is [true] for initial
   Pushed and [false] otherwise. Used to decide whether the term being
   matched on must be aliased in the variable case (only initial
   Pushed need to be aliased). The first argument of [Alias] is [true]
   if the alias was introduced by an initial pushed and [false]
   otherwise.*)
type tomatch_status =
  | Pushed of (bool*((constr * tomatch_type) * int list * Name.t))
  | Alias of (bool*(Name.t * constr * (constr * types)))
  | NonDepAlias
  | Abstract of int * rel_declaration

type tomatch_stack = tomatch_status list

(* We keep a constr for aliases and a cases_pattern for error message *)

type pattern_history =
  | Top
  | MakeConstructor of constructor * pattern_continuation

and pattern_continuation =
  | Continuation of int * cases_pattern list * pattern_history
  | Result of cases_pattern list

let start_history n = Continuation (n, [], Top)

let feed_history arg = function
  | Continuation (n, l, h) when n>=1 ->
      Continuation (n-1, arg :: l, h)
  | Continuation (n, _, _) ->
      anomaly (str "Bad number of expected remaining patterns: " ++ int n)
  | Result _ ->
      anomaly (Pp.str "Exhausted pattern history")

(* This is for non exhaustive error message *)

let rec glob_pattern_of_partial_history args2 = function
  | Continuation (n, args1, h) ->
      let args3 = make_anonymous_patvars (n - (List.length args2)) in
      build_glob_pattern (List.rev_append args1 (args2@args3)) h
  | Result pl -> pl

and build_glob_pattern args = function
  | Top -> args
  | MakeConstructor (pci, rh) ->
      glob_pattern_of_partial_history
	[PatCstr (Loc.ghost, pci, args, Anonymous)] rh

let complete_history = glob_pattern_of_partial_history []

(* This is to build glued pattern-matching history and alias bodies *)

let pop_history_pattern = function
  | Continuation (0, l, Top) ->
      Result (List.rev l)
  | Continuation (0, l, MakeConstructor (pci, rh)) ->
      feed_history (PatCstr (Loc.ghost,pci,List.rev l,Anonymous)) rh
  | _ ->
      anomaly (Pp.str "Constructor not yet filled with its arguments")

let pop_history h =
  feed_history (PatVar (Loc.ghost, Anonymous)) h

(* Builds a continuation expecting [n] arguments and building [ci] applied
   to this [n] arguments *)

let push_history_pattern n pci cont =
  Continuation (n, [], MakeConstructor (pci, cont))

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
  - "Abstract" instructions mean that an abstraction has to be inserted in the
    current branch to build (this means a pattern has been detected dependent
    in another one and a generalization is necessary to ensure well-typing)
    Abstract instructions extend the [env] in which the other instructions
    are typed
  - "Alias" instructions mean an alias has to be inserted (this alias
    is usually removed at the end, except when its type is not the
    same as the type of the matched term from which it comes -
    typically because the inductive types are "real" parameters)
  - "NonDepAlias" instructions mean the completion of a matching over
    a term to match as for Alias but without inserting this alias
    because there is no dependency in it

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
      caseloc   : Loc.t;
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
  let indu = evd_comb1 (Evd.fresh_inductive_instance env) evdref ind in
  let arsign = inductive_alldecls_env env indu in
  let hole_source = match tmloc with
    | Some loc -> fun i -> (loc, Evar_kinds.TomatchTypeParameter (ind,i))
    | None -> fun _ -> (Loc.ghost, Evar_kinds.InternalHole) in
   let (_,evarl,_) =
    List.fold_right
      (fun (na,b,ty) (subst,evarl,n) ->
	match b with
        | None ->
	    let ty' = substl subst ty in
	    let e = e_new_evar env evdref ~src:(hole_source n) ty' in
	    (e::subst,e::evarl,n+1)
	| Some b ->
	    (substl subst b::subst,evarl,n+1))
      arsign ([],[],1) in
   applist (mkIndU indu,List.rev evarl)

let try_find_ind env sigma typ realnames =
  let (IndType(_,realargs) as ind) = find_rectype env sigma typ in
  let names =
    match realnames with
      | Some names -> names
      | None -> List.make (List.length realargs) Anonymous in
  IsInd (typ,ind,names)

let inh_coerce_to_ind evdref env loc ty tyi =
  let sigma = !evdref in
  let expected_typ = inductive_template evdref env loc tyi in
  (* Try to refine the type with inductive information coming from the
     constructor and renounce if not able to give more information *)
  (* devrait être indifférent d'exiger leq ou pas puisque pour
     un inductif cela doit être égal *)
  if not (e_cumul env evdref expected_typ ty) then evdref := sigma

let binding_vars_of_inductive = function
  | NotInd _ -> []
  | IsInd (_,IndType(_,realargs),_) -> List.filter isRel realargs

let extract_inductive_data env sigma (_,b,t) =
  match b with
  | None ->
    let tmtyp =
      try try_find_ind env sigma t None
      with Not_found -> NotInd (None,t) in
    let tmtypvars = binding_vars_of_inductive tmtyp in
    (tmtyp,tmtypvars)
  | Some _ ->
    (NotInd (None, t), [])

let unify_tomatch_with_patterns evdref env loc typ pats realnames =
  match find_row_ind pats with
    | None -> NotInd (None,typ)
    | Some (_,(ind,_)) ->
	inh_coerce_to_ind evdref env loc typ ind;
	try try_find_ind env !evdref typ realnames
	with Not_found -> NotInd (None,typ)

let find_tomatch_tycon evdref env loc = function
  (* Try if some 'in I ...' is present and can be used as a constraint *)
  | Some (_,ind,realnal) ->
      mk_tycon (inductive_template evdref env loc ind),Some (List.rev realnal)
  | None ->
      empty_tycon,None

let coerce_row typing_fun evdref env pats (tomatch,(_,indopt)) =
  let loc = Some (loc_of_glob_constr tomatch) in
  let tycon,realnames = find_tomatch_tycon evdref env loc indopt in
  let j = typing_fun tycon env evdref tomatch in
  let evd, j = Coercion.inh_coerce_to_base (loc_of_glob_constr tomatch) env !evdref j in
  evdref := evd;
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

let mkExistential env ?(src=(Loc.ghost,Evar_kinds.InternalHole)) evdref =
  let e, u = e_new_type_evar env evdref univ_flexible_alg ~src:src in e

let evd_comb2 f evdref x y =
  let (evd',y) = f !evdref x y in
  evdref := evd';
  y

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
	      if List.is_empty deps && isEvar typ then
	      (* Don't insert coercions if dependent; only solve evars *)
		let _ = e_cumul pb.env pb.evdref indt typ in
		current
	      else
		(evd_comb2 (Coercion.inh_conv_coerce_to true Loc.ghost pb.env)
		  pb.evdref (make_judge current typ) indt).uj_val in
	    let sigma =  !(pb.evdref) in
	    (current,try_find_ind pb.env sigma indt names))
  | _ -> (current,tmtyp)

let type_of_tomatch = function
  | IsInd (t,_,_) -> t
  | NotInd (_,t) -> t

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
    | [] -> anomaly (Pp.str "Empty list of patterns")

let alias_of_pat = function
  | PatVar (_,name) -> name
  | PatCstr(_,_,_,name) -> name

let remove_current_pattern eqn =
  match eqn.patterns with
    | pat::pats ->
	{ eqn with
	    patterns = pats;
	    alias_stack = alias_of_pat pat :: eqn.alias_stack }
    | [] -> anomaly (Pp.str "Empty list of patterns")

let push_current_pattern (cur,ty) eqn =
  match eqn.patterns with
    | pat::pats ->
        let rhs_env = push_rel (alias_of_pat pat,Some cur,ty) eqn.rhs.rhs_env in
	{ eqn with
            rhs = { eqn.rhs with rhs_env = rhs_env };
	    patterns = pats }
    | [] -> anomaly (Pp.str "Empty list of patterns")

(* spiwack: like [push_current_pattern] but does not introduce an
   alias in rhs_env. Aliasing binders are only useful for variables at
   the root of a pattern matching problem (initial push), so we
   distinguish the cases. *)
let push_noalias_current_pattern eqn =
  match eqn.patterns with
  | _::pats ->
      { eqn with patterns = pats }
  | [] -> anomaly (Pp.str "push_noalias_current_pattern: Empty list of patterns")



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
	if Int.equal (List.length args) nb_args_constr then pat
	else
	  try
	    let args' = adjust_local_defs loc (args, List.rev ci.cs_args)
	    in PatCstr (loc, cstr, args', alias)
	  with NotAdjustable ->
	    error_wrong_numarg_constructor_loc loc env cstr nb_args_constr
      else
	(* Try to insert a coercion *)
	try
	  Coercion.inh_pattern_coerce_to loc env pat ind' ind
	with Not_found ->
	  error_bad_constructor_loc loc env cstr ind

let check_all_variables env sigma typ mat =
  List.iter
    (fun eqn -> match current_pattern eqn with
       | PatVar (_,id) -> ()
       | PatCstr (loc,cstr_sp,_,_) ->
	   error_bad_pattern_loc loc env sigma cstr_sp typ)
    mat

let check_unused_pattern env eqn =
  if not !(eqn.used) then
    raise_pattern_matching_error
      (eqn.eqn_loc, env, Evd.empty, UnusedClause eqn.patterns)

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
    | Name id -> Id.List.mem id rhs.rhs_vars

let is_dep_patt_in eqn = function
  | PatVar (_,name) -> Flags.is_program_mode () || occur_in_rhs name eqn.rhs
  | PatCstr _ -> true

let mk_dep_patt_row (pats,_,eqn) =
  List.map (is_dep_patt_in eqn) pats

let dependencies_in_pure_rhs nargs eqns =
  if List.is_empty eqns then
    List.make nargs (not (Flags.is_program_mode ()))  (* Only "_" patts *) else
  let deps_rows = List.map mk_dep_patt_row eqns in
  let deps_columns = matrix_transpose deps_rows in
  List.map (List.exists (fun x -> x)) deps_columns

let dependent_decl a = function
  | (na,None,t) -> dependent a t
  | (na,Some c,t) -> dependent a t || dependent a c

let rec dep_in_tomatch n = function
  | (Pushed _ | Alias _ | NonDepAlias) :: l -> dep_in_tomatch n l
  | Abstract (_,d) :: l -> dependent_decl (mkRel n) d || dep_in_tomatch (n+1) l
  | [] -> false

let dependencies_in_rhs nargs current tms eqns =
  match kind_of_term current with
  | Rel n when dep_in_tomatch n tms -> List.make nargs true
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

let rec find_dependency_list tmblock = function
  | [] -> []
  | (used,tdeps,d)::rest ->
      let deps = find_dependency_list tmblock rest in
      if used && List.exists (fun x -> dependent_decl x d) tmblock
      then
        List.add_set Int.equal
          (List.length rest + 1) (List.union Int.equal deps tdeps)
      else deps

let find_dependencies is_dep_or_cstr_in_rhs (tm,(_,tmtypleaves),d) nextlist =
  let deps = find_dependency_list (tm::tmtypleaves) nextlist in
  if is_dep_or_cstr_in_rhs || not (List.is_empty deps)
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
  | Pushed (b,((c,tm),l,na)) :: rest ->
      let c = relocate_index n1 n2 depth c in
      let tm = map_tomatch_type (relocate_index n1 n2 depth) tm in
      let l = List.map (relocate_rel n1 n2 depth) l in
      Pushed (b,((c,tm),l,na)) :: genrec depth rest
  | Alias (initial,(na,c,d)) :: rest ->
      (* [c] is out of relocation scope *)
      Alias (initial,(na,c,map_pair (relocate_index n1 n2 depth) d)) :: genrec depth rest
  | NonDepAlias :: rest ->
      NonDepAlias :: genrec depth rest
  | Abstract (i,d) :: rest ->
      let i = relocate_rel n1 n2 depth i in
      Abstract (i,map_rel_declaration (relocate_index n1 n2 depth) d)
      :: genrec (depth+1) rest in
  genrec 0

(* [replace_tomatch n c tomatch] replaces [Rel n] by [c] in [tomatch] *)

let rec replace_term n c k t =
  if isRel t && Int.equal (destRel t) (n + k) then lift k c
  else map_constr_with_binders succ (replace_term n c) k t

let length_of_tomatch_type_sign na t =
  let l = match na with
  | Anonymous -> 0
  | Name _ -> 1
  in
  match t with
  | NotInd _ -> l
  | IsInd (_, _, names) -> List.length names + l

let replace_tomatch n c =
  let rec replrec depth = function
  | [] -> []
  | Pushed (initial,((b,tm),l,na)) :: rest ->
      let b = replace_term n c depth b in
      let tm = map_tomatch_type (replace_term n c depth) tm in
      List.iter (fun i -> if Int.equal i (n + depth) then anomaly (Pp.str "replace_tomatch")) l;
      Pushed (initial,((b,tm),l,na)) :: replrec depth rest
  | Alias (initial,(na,b,d)) :: rest ->
      (* [b] is out of replacement scope *)
      Alias (initial,(na,b,map_pair (replace_term n c depth) d)) :: replrec depth rest
  | NonDepAlias  :: rest ->
      NonDepAlias :: replrec depth rest
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
  | Pushed (initial,((c,tm),l,na))::rest ->
      let c = liftn n depth c in
      let tm = liftn_tomatch_type n depth tm in
      let l = List.map (fun i -> if i<depth then i else i+n) l in
      Pushed (initial,((c,tm),l,na))::(liftn_tomatch_stack n depth rest)
  | Alias (initial,(na,c,d))::rest ->
      Alias (initial,(na,liftn n depth c,map_pair (liftn n depth) d))
      ::(liftn_tomatch_stack n depth rest)
  | NonDepAlias  :: rest ->
      NonDepAlias :: liftn_tomatch_stack n depth rest
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
  let names1 = List.make (List.length sign) Anonymous in
  (* If any, we prefer names used in pats, from top to bottom *)
  let names2,aliasname =
    List.fold_right
      (fun (pats,pat_alias,eqn) (names,aliasname) ->
        (merge_names alias_of_pat pats names,
         merge_name (fun x -> x) pat_alias aliasname))
      eqns (names1,Anonymous) in
  (* Otherwise, we take names from the parameters of the constructor but
     avoiding conflicts with user ids *)
  let allvars =
    List.fold_left (fun l (_,_,eqn) -> List.union Id.equal l eqn.rhs.avoid_ids)
      [] eqns in
  let names3,_ =
    List.fold_left2
      (fun (l,avoid) d na ->
	 let na =
	   merge_name
	     (fun (na,_,t) -> Name (next_name_away (named_hd env t na) avoid))
	     d na
	 in
         (na::l,(out_name na)::avoid))
      ([],allvars) (List.rev sign) names2 in
  names3,aliasname

(*****************************************************************)
(* Recovering names for variables pushed to the rhs' environment *)
(* We just factorized a match over a matrix of equations         *)
(* "C xi1 .. xin as xi" as a single match over "C y1 .. yn as y" *)
(* We now replace the names y1 .. yn y by the actual names       *)
(* xi1 .. xin xi to be found in the i-th clause of the matrix    *)

let set_declaration_name x (_,c,t) = (x,c,t)

let recover_initial_subpattern_names = List.map2 set_declaration_name

let recover_alias_names get_name = List.map2 (fun x (_,c,t) ->(get_name x,c,t))

let push_rels_eqn sign eqn =
  {eqn with
     rhs = {eqn.rhs with rhs_env = push_rel_context sign eqn.rhs.rhs_env} }

let push_rels_eqn_with_names sign eqn =
  let subpats = List.rev (List.firstn (List.length sign) eqn.patterns) in
  let subpatnames = List.map alias_of_pat subpats in
  let sign = recover_initial_subpattern_names subpatnames sign in
  push_rels_eqn sign eqn

let push_generalized_decl_eqn env n (na,c,t) eqn =
  let na = match na with
  | Anonymous -> Anonymous
  | Name id -> pi1 (Environ.lookup_rel n eqn.rhs.rhs_env) in
  push_rels_eqn [(na,c,t)] eqn

let drop_alias_eqn eqn =
  { eqn with alias_stack = List.tl eqn.alias_stack }

let push_alias_eqn alias eqn =
  let aliasname = List.hd eqn.alias_stack in
  let eqn = drop_alias_eqn eqn in
  let alias = set_declaration_name aliasname alias in
  push_rels_eqn [alias] eqn

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
  | Pushed (_,((_,tm),_,na)) :: rest ->
      let k' = length_of_tomatch_type_sign na tm in
      map_predicate f (k+k') ccl rest
  | (Alias _ | NonDepAlias) :: rest ->
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
  let c = match dep with
  | Anonymous -> None
  | Name _ -> Some cur
  in
  let l =
    match typ with
    | IsInd (_, IndType (_, _), []) -> []
    | IsInd (_, IndType (_, realargs), names) -> realargs
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
let generalize_predicate (names,na) ny d tms ccl =
  let () = match na with
  | Anonymous -> anomaly (Pp.str "Undetected dependency")
  | _ -> () in
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
  | (Alias _ | NonDepAlias)::tms ->
      (* substitution already done in build_branch *)
      extract_predicate ccl tms
  | Abstract (i,d)::tms ->
      mkProd_wo_LetIn d (extract_predicate ccl tms)
  | Pushed (_,((cur,NotInd _),_,na))::tms ->
      begin match na with
      | Anonymous -> extract_predicate ccl tms
      | Name _ ->
        let tms = lift_tomatch_stack 1 tms in
        let pred = extract_predicate ccl tms in
        subst1 cur pred
      end
  | Pushed (_,((cur,IsInd (_,IndType(_,realargs),_)),_,na))::tms ->
      let realargs = List.rev realargs in
      let k, nrealargs = match na with
      | Anonymous -> 0, realargs
      | Name _ -> 1, (cur :: realargs)
      in
      let tms = lift_tomatch_stack (List.length realargs + k) tms in
      let pred = extract_predicate ccl tms in
      substl nrealargs pred
  | [] ->
      ccl

let abstract_predicate env sigma indf cur realargs (names,na) tms ccl =
  let sign = make_arity_signature env true indf in
  (* n is the number of real args + 1 (+ possible let-ins in sign) *)
  let n = List.length sign in
  (* Before abstracting we generalize over cur and on those realargs *)
  (* that are rels, consistently with the specialization made in     *)
  (* build_branch                                                    *)
  let tms = List.fold_right2 (fun par arg tomatch ->
    match kind_of_term par with
    | Rel i -> relocate_index_tomatch (i+n) (destRel arg) tomatch
    | _ -> tomatch) (realargs@[cur]) (extended_rel_list 0 sign)
       (lift_tomatch_stack n tms) in
  (* Pred is already dependent in the current term to match (if      *)
  (* (na<>Anonymous) and its realargs; we just need to adjust it to  *)
  (* full sign if dep in cur is not taken into account               *)
  let ccl = match na with
  | Anonymous -> lift_predicate 1 ccl tms
  | Name _ -> ccl
  in
  let pred = extract_predicate ccl tms in
  (* Build the predicate properly speaking *)
  let sign = List.map2 set_declaration_name (na::names) sign in
  it_mkLambda_or_LetIn_name env pred sign

(* [expand_arg] is used by [specialize_predicate]
   if Yk denotes [Xk;xk] or [Xk],
   it replaces gamma, x1...xn, x1...xk Yk+1...Yn |- pred
   by gamma, x1...xn, x1...xk-1 [Xk;xk] Yk+1...Yn |- pred (if dep) or
   by gamma, x1...xn, x1...xk-1 [Xk] Yk+1...Yn |- pred (if not dep) *)

let expand_arg tms (p,ccl) ((_,t),_,na) =
  let k = length_of_tomatch_type_sign na t in
  (p+k,liftn_predicate (k-1) (p+1) ccl tms)


let use_unit_judge evd =
  let j, ctx = coq_unit_judge () in
  let evd' = Evd.merge_context_set Evd.univ_flexible_alg evd ctx in
    evd', j

let add_assert_false_case pb tomatch =
  let pats = List.map (fun _ -> PatVar (Loc.ghost,Anonymous)) tomatch in
  let aliasnames =
    List.map_filter (function Alias _ | NonDepAlias -> Some Anonymous | _ -> None) tomatch
  in
  [ { patterns = pats;
      rhs = { rhs_env = pb.env;
	      rhs_vars = [];
	      avoid_ids = [];
	      it = None };
      alias_stack = Anonymous::aliasnames;
      eqn_loc = Loc.ghost;
      used = ref false } ]

let adjust_impossible_cases pb pred tomatch submat =
  match submat with
  | [] ->
    begin match kind_of_term pred with
    | Evar (evk,_) when snd (evar_source evk !(pb.evdref)) == Evar_kinds.ImpossibleCase ->
        if not (Evd.is_defined !(pb.evdref) evk) then begin
	  let evd, default = use_unit_judge !(pb.evdref) in
	  pb.evdref := Evd.define evk default.uj_type evd
        end;
        add_assert_false_case pb tomatch
    | _ ->
	submat
    end
  | _ ->
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
let specialize_predicate newtomatchs (names,depna) arsign cs tms ccl =
  (* Assume some gamma st: gamma |- PI [X,x:I(X)]. PI tms. ccl *)
  let nrealargs = List.length names in
  let l = match depna with Anonymous -> 0 | Name _ -> 1 in
  let k = nrealargs + l in
  (* We adjust pred st: gamma, x1..xn |- PI [X,x:I(X)]. PI tms. ccl' *)
  (* so that x can later be instantiated by Ci(x1..xn) *)
  (* and X by the realargs for Ci *)
  let n = cs.cs_nargs in
  let ccl' = liftn_predicate n (k+1) ccl tms in
  (* We prepare the substitution of X and x:I(X) *)
  let realargsi =
    if not (Int.equal nrealargs 0) then
      adjust_subst_to_rel_context arsign (Array.to_list cs.cs_concl_realargs)
    else
      [] in
  let copti = match depna with
  | Anonymous -> None
  | Name _ -> Some (build_dependent_constructor cs)
  in
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
  let pred = abstract_predicate env !evdref indf current realargs dep tms p in
  (pred, whd_betaiota !evdref
           (applist (pred, realargs@[current])))

(* Take into account that a type has been discovered to be inductive, leading
   to more dependencies in the predicate if the type has indices *)
let adjust_predicate_from_tomatch tomatch (current,typ as ct) pb =
  let ((_,oldtyp),deps,na) = tomatch in
  match typ, oldtyp with
  | IsInd (_,_,names), NotInd _ ->
      let k = match na with
      | Anonymous -> 1
      | Name _ -> 2
      in
      let n = List.length names in
      { pb with pred = liftn_predicate n k pb.pred pb.tomatch },
      (ct,List.map (fun i -> if i >= k then i+n else i) deps,na)
  | _ ->
      pb, (ct,deps,na)

(* Remove commutative cuts that turn out to be non-dependent after
   some evars have been instantiated *)

let rec ungeneralize n ng body =
  match kind_of_term body with
  | Lambda (_,_,c) when Int.equal ng 0 ->
      subst1 (mkRel n) c
  | Lambda (na,t,c) ->
      (* We traverse an inner generalization *)
      mkLambda (na,t,ungeneralize (n+1) (ng-1) c)
  | LetIn (na,b,t,c) ->
      (* We traverse an alias *)
      mkLetIn (na,b,t,ungeneralize (n+1) ng c)
  | Case (ci,p,c,brs) ->
      (* We traverse a split *)
      let p =
        let sign,p = decompose_lam_assum p in
        let sign2,p = decompose_prod_n_assum ng p in
        let p = prod_applist p [mkRel (n+List.length sign+ng)] in
        it_mkLambda_or_LetIn (it_mkProd_or_LetIn p sign2) sign in
      mkCase (ci,p,c,Array.map2 (fun q c ->
        let sign,b = decompose_lam_n_assum q c in
        it_mkLambda_or_LetIn (ungeneralize (n+q) ng b) sign)
        ci.ci_cstr_ndecls brs)
  | App (f,args) ->
      (* We traverse an inner generalization *)
      assert (isCase f);
      mkApp (ungeneralize n (ng+Array.length args) f,args)
  | _ -> assert false

let ungeneralize_branch n k (sign,body) cs =
  (sign,ungeneralize (n+cs.cs_nargs) k body)

let rec is_dependent_generalization ng body =
  match kind_of_term body with
  | Lambda (_,_,c) when Int.equal ng 0 ->
      dependent (mkRel 1) c
  | Lambda (na,t,c) ->
      (* We traverse an inner generalization *)
      is_dependent_generalization (ng-1) c
  | LetIn (na,b,t,c) ->
      (* We traverse an alias *)
      is_dependent_generalization ng c
  | Case (ci,p,c,brs) ->
      (* We traverse a split *)
      Array.exists2 (fun q c ->
        let _,b = decompose_lam_n_assum q c in is_dependent_generalization ng b)
        ci.ci_cstr_ndecls brs
  | App (g,args) ->
      (* We traverse an inner generalization *)
      assert (isCase g);
      is_dependent_generalization (ng+Array.length args) g
  | _ -> assert false

let is_dependent_branch k (_,br) =
  is_dependent_generalization k br

let postprocess_dependencies evd tocheck brs tomatch pred deps cs =
  let rec aux k brs tomatch pred tocheck deps = match deps, tomatch with
  | [], _ -> brs,tomatch,pred,[]
  | n::deps, Abstract (i,d) :: tomatch ->
      let d = map_rel_declaration (nf_evar evd) d in
      let is_d = match d with (_, None, _) -> false | _ -> true in
      if is_d || List.exists (fun c -> dependent_decl (lift k c) d) tocheck
                 && Array.exists (is_dependent_branch k) brs then
        (* Dependency in the current term to match and its dependencies is real *)
        let brs,tomatch,pred,inst = aux (k+1) brs tomatch pred (mkRel n::tocheck) deps in
        let inst = match d with
        | (_, None, _) -> mkRel n :: inst
        | _ -> inst
        in
        brs, Abstract (i,d) :: tomatch, pred, inst
      else
        (* Finally, no dependency remains, so, we can replace the generalized *)
        (* terms by its actual value in both the remaining terms to match and *)
        (* the bodies of the Case *)
        let pred = lift_predicate (-1) pred tomatch in
        let tomatch = relocate_index_tomatch 1 (n+1) tomatch in
        let tomatch = lift_tomatch_stack (-1) tomatch in
        let brs = Array.map2 (ungeneralize_branch n k) brs cs in
        aux k brs tomatch pred tocheck deps
  | _ -> assert false
  in aux 0 brs tomatch pred tocheck deps

(************************************************************************)
(* Sorting equations by constructor *)

let rec irrefutable env = function
  | PatVar (_,name) -> true
  | PatCstr (_,cstr,args,_) ->
      let ind = inductive_of_constructor cstr in
      let (_,mip) = Inductive.lookup_mind_specif env ind in
      let one_constr = Int.equal (Array.length mip.mind_user_lc) 1 in
      one_constr && List.for_all (irrefutable env) args

let first_clause_irrefutable env = function
  | eqn::mat -> List.for_all (irrefutable env) eqn.patterns
  | _ -> false

let group_equations pb ind current cstrs mat =
  let mat =
    if first_clause_irrefutable pb.env mat then [List.hd mat] else mat in
  let brs = Array.make (Array.length cstrs) [] in
  let only_default = ref None in
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
		 brs.(i-1) <- (args, name, rest) :: brs.(i-1)
	       done;
	       if !only_default == None then only_default := Some true
	   | PatCstr (loc,((_,i)),args,name) ->
	       (* This is a regular clause *)
	       only_default := Some false;
	       brs.(i-1) <- (args, name, rest) :: brs.(i-1)) mat () in
  (brs,Option.default false !only_default)

(************************************************************************)
(* Here starts the pattern-matching compilation algorithm *)

(* Abstracting over dependent subterms to match *)
let rec generalize_problem names pb = function
  | [] -> pb, []
  | i::l ->
      let (na,b,t as d) = map_rel_declaration (lift i) (Environ.lookup_rel i pb.env) in
      let pb',deps = generalize_problem names pb l in
      begin match (na, b) with
      | Anonymous, Some _ -> pb', deps
      | _ ->
        let d = on_pi3 (whd_betaiota !(pb.evdref)) d in (* for better rendering *)
        let tomatch = lift_tomatch_stack 1 pb'.tomatch in
        let tomatch = relocate_index_tomatch (i+1) 1 tomatch in
        { pb' with
            tomatch = Abstract (i,d) :: tomatch;
            pred = generalize_predicate names i d pb'.tomatch pb'.pred  },
        i::deps
      end

(* No more patterns: typing the right-hand side of equations *)
let build_leaf pb =
  let rhs = extract_rhs pb in
  let j = pb.typing_function (mk_tycon pb.pred) rhs.rhs_env pb.evdref rhs.it in
  j_nf_evar !(pb.evdref) j

(* Build the sub-pattern-matching problem for a given branch "C x1..xn as x" *)
(* spiwack: the [initial] argument keeps track whether the branch is a
   toplevel branch ([true]) or a deep one ([false]). *)
let build_branch initial current realargs deps (realnames,curname) pb arsign eqns const_info =
  (* We remember that we descend through constructor C *)
  let history =
    push_history_pattern const_info.cs_nargs (fst const_info.cs_cstr) pb.history in

  (* We prepare the matching on x1:T1 .. xn:Tn using some heuristic to *)
  (* build the name x1..xn from the names present in the equations *)
  (* that had matched constructor C *)
  let cs_args = const_info.cs_args in
  let names,aliasname = get_names pb.env cs_args eqns in
  let typs = List.map2 (fun (_,c,t) na -> (na,c,t)) cs_args names in

  (* We build the matrix obtained by expanding the matching on *)
  (* "C x1..xn as x" followed by a residual matching on eqn into *)
  (* a matching on "x1 .. xn eqn" *)
  let submat = List.map (fun (tms,_,eqn) -> prepend_pattern tms eqn) eqns in

  (* We adjust the terms to match in the context they will be once the *)
  (* context [x1:T1,..,xn:Tn] will have been pushed on the current env *)
  let typs' =
    List.map_i (fun i d -> (mkRel i,map_rel_declaration (lift i) d)) 1 typs in

  let extenv = push_rel_context typs pb.env in

  let typs' =
    List.map (fun (c,d) ->
      (c,extract_inductive_data extenv !(pb.evdref) d,d)) typs' in

  (* We compute over which of x(i+1)..xn and x matching on xi will need a *)
  (* generalization *)
  let dep_sign =
    find_dependencies_signature
      (dependencies_in_rhs const_info.cs_nargs current pb.tomatch eqns)
      (List.rev typs') in

  (* The dependent term to subst in the types of the remaining UnPushed
     terms is relative to the current context enriched by topushs *)
  let ci = build_dependent_constructor const_info in

  (* Current context Gamma has the form Gamma1;cur:I(realargs);Gamma2 *)
  (* We go from Gamma |- PI tms. pred to                              *)
  (* Gamma;x1..xn;curalias:I(x1..xn) |- PI tms'. pred'                *)
  (* where, in tms and pred, those realargs that are vars are         *)
  (* replaced by the corresponding xi and cur replaced by curalias    *)
  let cirealargs = Array.to_list const_info.cs_concl_realargs in

  (* Do the specialization for terms to match *)
  let tomatch = List.fold_right2 (fun par arg tomatch ->
    match kind_of_term par with
    | Rel i -> replace_tomatch (i+const_info.cs_nargs) arg tomatch
    | _ -> tomatch) (current::realargs) (ci::cirealargs)
      (lift_tomatch_stack const_info.cs_nargs pb.tomatch) in

  let pred_is_not_dep =
    noccur_predicate_between 1 (List.length realnames + 1) pb.pred tomatch in

  let typs' =
    List.map2
      (fun (tm,(tmtyp,_),(na,_,_)) deps ->
	let na = match curname, na with
	| Name _, Anonymous -> curname
	| Name _, Name _ -> na
	| Anonymous, _ ->
	    if List.is_empty deps && pred_is_not_dep then Anonymous else force_name na in
	((tm,tmtyp),deps,na))
      typs' (List.rev dep_sign) in

  (* Do the specialization for the predicate *)
  let pred =
    specialize_predicate typs' (realnames,curname) arsign const_info tomatch pb.pred in

  let currents = List.map (fun x -> Pushed (false,x)) typs' in

  let alias = match aliasname with
  | Anonymous ->
      NonDepAlias
  | Name _ ->
      let cur_alias = lift const_info.cs_nargs current in
      let ind =
        appvect (
          applist (mkIndU (inductive_of_constructor (fst const_info.cs_cstr), snd const_info.cs_cstr),
                   List.map (lift const_info.cs_nargs) const_info.cs_params),
          const_info.cs_concl_realargs) in
      Alias (initial,(aliasname,cur_alias,(ci,ind))) in

  let tomatch = List.rev_append (alias :: currents) tomatch in

  let submat = adjust_impossible_cases pb pred tomatch submat in
  let () = match submat with
  | [] ->
    raise_pattern_matching_error
      (Loc.ghost, pb.env, Evd.empty, NonExhaustive (complete_history history))
  | _ -> ()
  in

  typs,
  { pb with
      env = extenv;
      tomatch = tomatch;
      pred = pred;
      history = history;
      mat = List.map (push_rels_eqn_with_names typs) submat }

(**********************************************************************
 INVARIANT:

  pb = { env, pred, tomatch, mat, ...}
  tomatch = list of Pushed (c:T), Abstract (na:T), Alias (c:T) or NonDepAlias

  all terms and types in Pushed, Abstract and Alias are relative to env
  enriched by the Abstract coming before

*)

let mk_case pb (ci,pred,c,brs) =
  let mib = lookup_mind (fst ci.ci_ind) pb.env in
    match mib.mind_record with
    | Some (Some (_, cs, pbs)) ->
      Reduction.beta_appvect brs.(0) 
	(Array.map (fun p -> mkProj (Projection.make p true, c)) cs)
    | _ -> mkCase (ci,pred,c,brs)

(**********************************************************************)
(* Main compiling descent *)
let rec compile pb =
  match pb.tomatch with
    | Pushed cur :: rest -> match_current { pb with tomatch = rest } cur
    | Alias (initial,x) :: rest -> compile_alias initial pb x rest
    | NonDepAlias :: rest -> compile_non_dep_alias pb rest
    | Abstract (i,d) :: rest -> compile_generalization pb i d rest
    | [] -> build_leaf pb

(* Case splitting *)
and match_current pb (initial,tomatch) =
  let tm = adjust_tomatch_to_pattern pb tomatch in
  let pb,tomatch = adjust_predicate_from_tomatch tomatch tm pb in
  let ((current,typ),deps,dep) = tomatch in
  match typ with
    | NotInd (_,typ) ->
	check_all_variables pb.env !(pb.evdref) typ pb.mat;
	compile_all_variables initial tomatch pb
    | IsInd (_,(IndType(indf,realargs) as indt),names) ->
	let mind,_ = dest_ind_family indf in
        let mind = Tacred.check_privacy pb.env mind in
	let cstrs = get_constructors pb.env indf in
	let arsign, _ = get_arity pb.env indf in
	let eqns,onlydflt = group_equations pb (fst mind) current cstrs pb.mat in
        let no_cstr = Int.equal (Array.length cstrs) 0 in
	if (not no_cstr || not (List.is_empty pb.mat)) && onlydflt then
	  compile_all_variables initial tomatch pb
	else
	  (* We generalize over terms depending on current term to match *)
	  let pb,deps = generalize_problem (names,dep) pb deps in

	  (* We compile branches *)
	  let brvals = Array.map2 (compile_branch initial current realargs (names,dep) deps pb arsign) eqns cstrs in
	  (* We build the (elementary) case analysis *)
          let depstocheck = current::binding_vars_of_inductive typ in
          let brvals,tomatch,pred,inst =
            postprocess_dependencies !(pb.evdref) depstocheck
              brvals pb.tomatch pb.pred deps cstrs in
          let brvals = Array.map (fun (sign,body) ->
            it_mkLambda_or_LetIn body sign) brvals in
	  let (pred,typ) =
	    find_predicate pb.caseloc pb.env pb.evdref
	      pred current indt (names,dep) tomatch in
	  let ci = make_case_info pb.env (fst mind) pb.casestyle in
	  let pred = nf_betaiota !(pb.evdref) pred in
	  let case = mk_case pb (ci,pred,current,brvals) in
	  Typing.check_allowed_sort pb.env !(pb.evdref) mind current pred;
	  { uj_val = applist (case, inst);
	    uj_type = prod_applist typ inst }


(* Building the sub-problem when all patterns are variables. Case
   where [current] is an intially pushed term. *)
and shift_problem ((current,t),_,na) pb =
  let ty = type_of_tomatch t in
  let tomatch = lift_tomatch_stack 1 pb.tomatch in
  let pred = specialize_predicate_var (current,t,na) pb.tomatch pb.pred in
  let pb =
    { pb with
       env = push_rel (na,Some current,ty) pb.env;
       tomatch = tomatch;
       pred = lift_predicate 1 pred tomatch;
       history = pop_history pb.history;
       mat = List.map (push_current_pattern (current,ty)) pb.mat } in
  let j = compile pb in
  { uj_val = subst1 current j.uj_val;
    uj_type = subst1 current j.uj_type }

(* Building the sub-problem when all patterns are variables,
   non-initial case. Variables which appear as subterms of constructor
   are already introduced in the context, we avoid creating aliases to
   themselves by treating this case specially. *)
and pop_problem ((current,t),_,na) pb =
  let pred = specialize_predicate_var (current,t,na) pb.tomatch pb.pred in
  let pb =
    { pb with
       pred = pred;
       history = pop_history pb.history;
       mat = List.map push_noalias_current_pattern pb.mat } in
  compile pb

(* Building the sub-problem when all patterns are variables. *)
and compile_all_variables initial cur pb =
  if initial then shift_problem cur pb
  else pop_problem cur pb

(* Building the sub-problem when all patterns are variables *)
and compile_branch initial current realargs names deps pb arsign eqns cstr =
  let sign, pb = build_branch initial current realargs deps names pb arsign eqns cstr in
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
    uj_type = mkProd_wo_LetIn d j.uj_type }

(* spiwack: the [initial] argument keeps track whether the alias has
   been introduced by a toplevel branch ([true]) or a deep one
   ([false]). *)
and compile_alias initial pb (na,orig,(expanded,expanded_typ)) rest =
  let f c t =
    let alias = (na,Some c,t) in
    let pb =
      { pb with
         env = push_rel alias pb.env;
         tomatch = lift_tomatch_stack 1 rest;
         pred = lift_predicate 1 pb.pred pb.tomatch;
         history = pop_history_pattern pb.history;
         mat = List.map (push_alias_eqn alias) pb.mat } in
    let j = compile pb in
    { uj_val =
        if isRel c || isVar c || count_occurrences (mkRel 1) j.uj_val <= 1 then
          subst1 c j.uj_val
        else
          mkLetIn (na,c,t,j.uj_val);
      uj_type = subst1 c j.uj_type } in
  (* spiwack: when an alias appears on a deep branch, its non-expanded
     form is automatically a variable of the same name. We avoid
     introducing such superfluous aliases so that refines are elegant. *)
  let just_pop () =
    let pb =
      { pb with
        tomatch = rest;
        history = pop_history_pattern pb.history;
        mat = List.map drop_alias_eqn pb.mat } in
    compile pb
  in
  let sigma = !(pb.evdref) in
  if not (Flags.is_program_mode ()) && (isRel orig || isVar orig) then
    (* Try to compile first using non expanded alias *)
    try
      if initial then f orig (Retyping.get_type_of pb.env !(pb.evdref) orig)
      else just_pop ()
    with e when precatchable_exception e ->
    (* Try then to compile using expanded alias *)
    pb.evdref := sigma;
    f expanded expanded_typ
  else
    (* Try to compile first using expanded alias *)
    try f expanded expanded_typ
    with e when precatchable_exception e ->
    (* Try then to compile using non expanded alias *)
    pb.evdref := sigma;
    if initial then f orig (Retyping.get_type_of pb.env !(pb.evdref) orig)
    else just_pop ()


(* Remember that a non-trivial pattern has been consumed *)
and compile_non_dep_alias pb rest =
  let pb =
    { pb with
       tomatch = rest;
       history = pop_history_pattern pb.history;
       mat = List.map drop_alias_eqn pb.mat } in
  compile pb

(* pour les alias des initiaux, enrichir les env de ce qu'il faut et
substituer après par les initiaux *)

(**************************************************************************)
(* Preparation of the pattern-matching problem                            *)

(* builds the matrix of equations testing that each eqn has n patterns
 * and linearizing the _ patterns.
 * Syntactic correctness has already been done in astterm *)
let matx_of_eqns env eqns =
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
  let map (x, u) =
    (* d1 ... dn dn+1 ... dn'-p+1 ... dn' *)
    (* \--env-/          (= x:ty)         *)
    (* \--------------extenv------------/ *)
    let (p, _, _) = lookup_rel_id x (rel_context extenv) in
    let rec traverse_local_defs p =
      match pi2 (lookup_rel p extenv) with
      | Some c -> assert (isRel c); traverse_local_defs (p + destRel c)
      | None -> p in
    let p = traverse_local_defs p in
    let u = lift (n' - n) u in
    try Some (p, u, expand_vars_in_term extenv u)
      (* pedrot: does this really happen to raise [Failure _]? *)
    with Failure _ -> None in
  let subst0 = List.map_filter map subst in
  let t0 = lift (n' - n) t in
  (subst0, t0)

let push_binder d (k,env,subst) =
  (k+1,push_rel d env,List.map (fun (na,u,d) -> (na,lift 1 u,d)) subst)

let rec list_assoc_in_triple x = function
    [] -> raise Not_found
  | (a, b, _)::l -> if Int.equal a x then b else list_assoc_in_triple x l

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

let abstract_tycon loc env evdref subst tycon extenv t =
  let t = nf_betaiota !evdref t in (* it helps in some cases to remove K-redex*)
  let src = match kind_of_term t with
    | Evar (evk,_) -> (loc,Evar_kinds.SubEvar evk)
    | _ -> (loc,Evar_kinds.CasesType true) in
  let subst0,t0 = adjust_to_extended_env_and_remove_deps env extenv subst t in
  (* We traverse the type T of the original problem Xi looking for subterms
     that match the non-constructor part of the constraints (this part
     is in subst); these subterms are the "good" subterms and we replace them
     by an evar that may depend (and only depend) on the corresponding
     convertible subterms of the substitution *)
  let rec aux (k,env,subst as x) t =
    let t = whd_evar !evdref t in match kind_of_term t with
    | Rel n when pi2 (lookup_rel n env) != None -> t
    | Evar ev ->
        let ty = get_type_of env !evdref t in
	let ty = Evarutil.evd_comb1 (refresh_universes (Some false) env) evdref ty in
        let inst =
	  List.map_i
	    (fun i _ ->
              try list_assoc_in_triple i subst0 with Not_found -> mkRel i)
              1 (rel_context env) in
        let ev' = e_new_evar env evdref ~src ty in
        begin match solve_simple_eqn (evar_conv_x full_transparent_state) env !evdref (None,ev,substl inst ev') with
        | Success evd -> evdref := evd
        | UnifFailure _ -> assert false
        end;
        ev'
    | _ ->
    let good = List.filter (fun (_,u,_) -> is_conv_leq env !evdref t u) subst in
    match good with
    | [] ->
      map_constr_with_full_binders push_binder aux x t
    | (_, _, u) :: _ -> (* u is in extenv *)
      let vl = List.map pi1 good in
      let ty = 
	let ty = get_type_of env !evdref t in
	  Evarutil.evd_comb1 (refresh_universes (Some false) env) evdref ty
      in
      let ty = lift (-k) (aux x ty) in
      let depvl = free_rels ty in
      let inst =
	List.map_i
	  (fun i _ -> if Int.List.mem i vl then u else mkRel i) 1
	  (rel_context extenv) in
      let rel_filter =
	List.map (fun a -> not (isRel a) || dependent a u
                           || Int.Set.mem (destRel a) depvl) inst in
      let named_filter =
	List.map (fun (id,_,_) -> dependent (mkVar id) u)
	  (named_context extenv) in
      let filter = Filter.make (rel_filter @ named_filter) in
      let candidates = u :: List.map mkRel vl in
      let ev = e_new_evar extenv evdref ~src ~filter ~candidates ty in
      lift k ev
  in
  aux (0,extenv,subst0) t0

let build_tycon loc env tycon_env subst tycon extenv evdref t =
  let t,tt = match t with
    | None ->
	(* This is the situation we are building a return predicate and
           we are in an impossible branch *)
	let n = rel_context_length (rel_context env) in
	let n' = rel_context_length (rel_context tycon_env) in
	let impossible_case_type, u =
	  e_new_type_evar (reset_context env) evdref univ_flexible_alg ~src:(loc,Evar_kinds.ImpossibleCase) in
	(lift (n'-n) impossible_case_type, mkSort u)
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
    PatVar (Loc.ghost,Name id), ((id,t)::subst, id::avoid) in
  let rec reveal_pattern t (subst,avoid as acc) =
    match kind_of_term (whd_betadeltaiota env sigma t) with
    | Construct (cstr,u) -> PatCstr (Loc.ghost,cstr,[],Anonymous), acc
    | App (f,v) when isConstruct f ->
	let cstr,u = destConstruct f in
	let n = constructor_nrealargs_env env cstr in
	let l = List.lastn n (Array.to_list v) in
	let l,acc = List.fold_map' reveal_pattern l acc in
	PatCstr (Loc.ghost,cstr,l,Anonymous), acc
    | _ -> make_patvar t acc in
  let rec aux n env acc_sign tms acc =
    match tms with
    | [] -> [], acc_sign, acc
    | (t, IsInd (_,IndType(indf,realargs),_)) :: tms ->
	let patl,acc = List.fold_map' reveal_pattern realargs acc in
	let pat,acc = make_patvar t acc in
	let indf' = lift_inductive_family n indf in
	let sign = make_arity_signature env true indf' in
	let sign = recover_alias_names alias_of_pat (pat :: List.rev patl) sign in
	let p = List.length realargs in
	let env' = push_rel_context sign env in
	let patl',acc_sign,acc = aux (n+p+1) env' (sign@acc_sign) tms acc in
	patl@pat::patl',acc_sign,acc
    | (t, NotInd (bo,typ)) :: tms ->
      let pat,acc = make_patvar t acc in
      let d = (alias_of_pat pat,None,typ) in
      let patl,acc_sign,acc = aux (n+1) (push_rel d env) (d::acc_sign) tms acc in
      pat::patl,acc_sign,acc in
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
    List.map_i (fun i d -> (mkRel i,map_rel_declaration (lift i) d)) 1 sign in

  let pb_env = push_rel_context sign env in
  let decls =
    List.map (fun (c,d) -> (c,extract_inductive_data pb_env sigma d,d)) decls in

  let decls = List.rev decls in
  let dep_sign = find_dependencies_signature (List.make n true) decls in

  let sub_tms =
    List.map2 (fun deps (tm,(tmtyp,_),(na,b,t)) ->
      let na = if List.is_empty deps then Anonymous else force_name na in
      Pushed (true,((tm,tmtyp),deps,na)))
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
      eqn_loc = Loc.ghost;
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
    { patterns = List.map (fun _ -> PatVar (Loc.ghost,Anonymous)) patl;
      alias_stack = [];
      eqn_loc = Loc.ghost;
      used = ref false;
      rhs = { rhs_env = pb_env;
              rhs_vars = [];
	      avoid_ids = avoid0;
	      it = None } } in
  (* [pb] is the auxiliary pattern-matching serving as skeleton for the
      return type of the original problem Xi *)
  (* let sigma, s = Evd.new_sort_variable sigma in *)
(*FIXME TRY *)
  (* let sigma, s = Evd.new_sort_variable univ_flexible sigma in *)
  let s' = Retyping.get_sort_of env sigma t in
  let sigma, s = Evd.new_sort_variable univ_flexible_alg sigma in
  let sigma = Evd.set_leq_sort env sigma s' s in
  let evdref = ref sigma in
  (* let ty = evd_comb1 (refresh_universes false) evdref ty in *)
  let pb =
    { env       = pb_env;
      evdref    = evdref;
      pred      = (*ty *) mkSort s;
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
let build_initial_predicate arsign pred =
  let rec buildrec n pred tmnames = function
    | [] -> List.rev tmnames,pred
    | ((na,c,t)::realdecls)::lnames ->
        let n' = n + List.length realdecls in
        buildrec (n'+1) pred (force_name na::tmnames) lnames
    | _ -> assert false
  in buildrec 0 pred [] (List.rev arsign)

let extract_arity_signature ?(dolift=true) env0 tomatchl tmsign =
  let lift = if dolift then lift else fun n t -> t in
  let get_one_sign n tm (na,t) =
    match tm with
      | NotInd (bo,typ) ->
	  (match t with
	    | None -> [na,Option.map (lift n) bo,lift n typ]
	    | Some (loc,_,_) ->
 	    user_err_loc (loc,"",
	    str"Unexpected type annotation for a term of non inductive type."))
      | IsInd (term,IndType(indf,realargs),_) ->
          let indf' = if dolift then lift_inductive_family n indf else indf in
	  let ((ind,u),_) = dest_ind_family indf' in
	  let nrealargs_ctxt = inductive_nrealdecls_env env0 ind in
	  let arsign = fst (get_arity env0 indf') in
	  let realnal =
	    match t with
	      | Some (loc,ind',realnal) ->
		  if not (eq_ind ind ind') then
		    user_err_loc (loc,"",str "Wrong inductive type.");
		  if not (Int.equal nrealargs_ctxt (List.length realnal)) then
		      anomaly (Pp.str "Ill-formed 'in' clause in cases");
		  List.rev realnal
	      | None -> List.make nrealargs_ctxt Anonymous in
	  (na,None,build_dependent_inductive env0 indf')
	  ::(List.map2 (fun x (_,c,t) ->(x,c,t)) realnal arsign) in
  let rec buildrec n = function
    | [],[] -> []
    | (_,tm)::ltm, (_,x)::tmsign ->
	let l = get_one_sign n tm x in
	l :: buildrec (n + List.length l) (ltm,tmsign)
    | _ -> assert false
  in List.rev (buildrec 0 (tomatchl,tmsign))

let inh_conv_coerce_to_tycon loc env evdref j tycon =
  match tycon with
    | Some p ->
	let (evd',j) = Coercion.inh_conv_coerce_to true loc env !evdref j p in
          evdref := evd';
          j
    | None -> j

(* We put the tycon inside the arity signature, possibly discovering dependencies. *)

let prepare_predicate_from_arsign_tycon loc tomatchs arsign c =
  let nar = List.fold_left (fun n sign -> List.length sign + n) 0 arsign in
  let subst, len =
    List.fold_left2 (fun (subst, len) (tm, tmtype) sign ->
      let signlen = List.length sign in
	match kind_of_term tm with
	  | Rel n when dependent tm c
		&& Int.equal signlen 1 (* The term to match is not of a dependent type itself *) ->
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
	      let idx = Int.List.assoc (n - lift) subst in
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

let prepare_predicate loc typing_fun env sigma tomatchs arsign tycon pred =
  let preds =
    match pred, tycon with
    (* No type annotation *)
    | None, Some t when not (noccur_with_meta 0 max_int t) ->
	(* If the tycon is not closed w.r.t real variables, we try *)
        (* two different strategies *)
	(* First strategy: we abstract the tycon wrt to the dependencies *)
        let pred1 =
          prepare_predicate_from_arsign_tycon loc tomatchs arsign t in
	(* Second strategy: we build an "inversion" predicate *)
	let sigma2,pred2 = build_inversion_problem loc env sigma tomatchs t in
	[sigma, pred1; sigma2, pred2]
    | None, _ ->
	(* No dependent type constraint, or no constraints at all: *)
	(* we use two strategies *)
        let sigma,t = match tycon with
	| Some t -> sigma,t
	| None -> 
	  let sigma, (t, _) = 
	    new_type_evar env sigma univ_flexible_alg ~src:(loc, Evar_kinds.CasesType false) in
	    sigma, t
	in
        (* First strategy: we build an "inversion" predicate *)
	let sigma1,pred1 = build_inversion_problem loc env sigma tomatchs t in
	(* Second strategy: we directly use the evar as a non dependent pred *)
        let pred2 = lift (List.length (List.flatten arsign)) t in
	[sigma1, pred1; sigma, pred2]
    (* Some type annotation *)
    | Some rtntyp, _ ->
      (* We extract the signature of the arity *)
      let envar = List.fold_right push_rel_context arsign env in
      let sigma, newt = new_sort_variable univ_flexible_alg sigma in
      let evdref = ref sigma in
      let predcclj = typing_fun (mk_tycon (mkSort newt)) envar evdref rtntyp in
      let sigma = !evdref in
      (* let sigma = Option.cata (fun tycon -> *)
      (*     let na = Name (Id.of_string "x") in *)
      (*     let tms = List.map (fun tm -> Pushed(tm,[],na)) tomatchs in *)
      (*     let predinst = extract_predicate predcclj.uj_val tms in *)
      (*     Coercion.inh_conv_coerce_to loc env !evdref predinst tycon) *)
      (*   !evdref tycon in *)
      let predccl = (j_nf_evar sigma predcclj).uj_val in
      [sigma, predccl]
  in
  List.map
    (fun (sigma,pred) ->
      let (nal,pred) = build_initial_predicate arsign pred in
      sigma,nal,pred)
    preds

(** Program cases *)

open Program

let ($) f x = f x

let string_of_name name =
  match name with
    | Anonymous -> "anonymous"
    | Name n -> Id.to_string n

let make_prime_id name =
  let str = string_of_name name in
    Id.of_string str, Id.of_string (str ^ "'")

let prime avoid name =
  let previd, id = make_prime_id name in
    previd, next_ident_away id avoid

let make_prime avoid prevname =
  let previd, id = prime !avoid prevname in
    avoid := id :: !avoid;
    previd, id

let eq_id avoid id =
  let hid = Id.of_string ("Heq_" ^ Id.to_string id) in
  let hid' = next_ident_away hid avoid in
    hid'

let mk_eq evdref typ x y = papp evdref coq_eq_ind [| typ; x ; y |]
let mk_eq_refl evdref typ x = papp evdref coq_eq_refl [| typ; x |]
let mk_JMeq evdref typ x typ' y =
  papp evdref coq_JMeq_ind [| typ; x ; typ'; y |]
let mk_JMeq_refl evdref typ x = 
  papp evdref coq_JMeq_refl [| typ; x |]

let hole = GHole (Loc.ghost, Evar_kinds.QuestionMark (Evar_kinds.Define true), Misctypes.IntroAnonymous, None)

let constr_of_pat env evdref arsign pat avoid =
  let rec typ env (ty, realargs) pat avoid =
    match pat with
    | PatVar (l,name) ->
	let name, avoid = match name with
	    Name n -> name, avoid
	  | Anonymous ->
	      let previd, id = prime avoid (Name (Id.of_string "wildcard")) in
		Name id, id :: avoid
	in
	  (PatVar (l, name), [name, None, ty] @ realargs, mkRel 1, ty, 
	   (List.map (fun x -> mkRel 1) realargs), 1, avoid)
    | PatCstr (l,((_, i) as cstr),args,alias) ->
	let cind = inductive_of_constructor cstr in
	let IndType (indf, _) = 
	  try find_rectype env ( !evdref) (lift (-(List.length realargs)) ty)
	  with Not_found -> error_case_not_inductive env 
	    {uj_val = ty; uj_type = Typing.type_of env !evdref ty}
	in
	let (ind,u), params = dest_ind_family indf in
	if not (eq_ind ind cind) then error_bad_constructor_loc l env cstr ind;
	let cstrs = get_constructors env indf in
	let ci = cstrs.(i-1) in
	let nb_args_constr = ci.cs_nargs in
	assert (Int.equal nb_args_constr (List.length args));
	let patargs, args, sign, env, n, m, avoid =
	  List.fold_right2
	    (fun (na, c, t) ua (patargs, args, sign, env, n, m, avoid)  ->
	       let pat', sign', arg', typ', argtypargs, n', avoid =
		 let liftt = liftn (List.length sign) (succ (List.length args)) t in
		   typ env (substl args liftt, []) ua avoid
	       in
	       let args' = arg' :: List.map (lift n') args in
	       let env' = push_rel_context sign' env in
		 (pat' :: patargs, args', sign' @ sign, env', n' + n, succ m, avoid))
	    ci.cs_args (List.rev args) ([], [], [], env, 0, 0, avoid)
	in
	let args = List.rev args in
	let patargs = List.rev patargs in
	let pat' = PatCstr (l, cstr, patargs, alias) in
	let cstr = mkConstructU ci.cs_cstr in
	let app = applistc cstr (List.map (lift (List.length sign)) params) in
	let app = applistc app args in
	let apptype = Retyping.get_type_of env ( !evdref) app in
	let IndType (indf, realargs) = find_rectype env ( !evdref) apptype in
	  match alias with
	      Anonymous ->
		pat', sign, app, apptype, realargs, n, avoid
	    | Name id ->
		let sign = (alias, None, lift m ty) :: sign in
		let avoid = id :: avoid in
		let sign, i, avoid =
		  try
		    let env = push_rel_context sign env in
		    evdref := the_conv_x_leq (push_rel_context sign env)
		      (lift (succ m) ty) (lift 1 apptype) !evdref;
		    let eq_t = mk_eq evdref (lift (succ m) ty)
		      (mkRel 1) (* alias *)
		      (lift 1 app) (* aliased term *)
		    in
		    let neq = eq_id avoid id in
		      (Name neq, Some (mkRel 0), eq_t) :: sign, 2, neq :: avoid
		  with Reduction.NotConvertible -> sign, 1, avoid
		in
		  (* Mark the equality as a hole *)
		  pat', sign, lift i app, lift i apptype, realargs, n + i, avoid
  in
  let pat', sign, patc, patty, args, z, avoid = typ env (pi3 (List.hd arsign), List.tl arsign) pat avoid in
    pat', (sign, patc, (pi3 (List.hd arsign), args), pat'), avoid


(* shadows functional version *)
let eq_id avoid id =
  let hid = Id.of_string ("Heq_" ^ Id.to_string id) in
  let hid' = next_ident_away hid !avoid in
    avoid := hid' :: !avoid;
    hid'

let is_topvar t =
match kind_of_term t with
| Rel 0 -> true
| _ -> false

let rels_of_patsign l =
  List.map (fun ((na, b, t) as x) ->
    match b with
      | Some t' when is_topvar t' -> (na, None, t)
      | _ -> x) l

let vars_of_ctx ctx =
  let _, y =
    List.fold_right (fun (na, b, t)  (prev, vars) ->
      match b with
	| Some t' when is_topvar t' ->
	    prev,
	    (GApp (Loc.ghost,
		(GRef (Loc.ghost, delayed_force coq_eq_refl_ref, None)), 
		   [hole; GVar (Loc.ghost, prev)])) :: vars
	| _ ->
	    match na with
		Anonymous -> invalid_arg "vars_of_ctx"
	      | Name n -> n, GVar (Loc.ghost, n) :: vars)
      ctx (Id.of_string "vars_of_ctx_error", [])
  in List.rev y

let rec is_included x y =
  match x, y with
    | PatVar _, _ -> true
    | _, PatVar _ -> true
    | PatCstr (l, (_, i), args, alias), PatCstr (l', (_, i'), args', alias')  ->
	if Int.equal i i' then List.for_all2 is_included args args'
	else false

(* liftsign is the current pattern's complete signature length. 
   Hence pats is already typed in its
   full signature. However prevpatterns are in the original one signature per pattern form.
 *)
let build_ineqs evdref prevpatterns pats liftsign =
  let _tomatchs = List.length pats in
  let diffs =
    List.fold_left
      (fun c eqnpats ->
	  let acc = List.fold_left2
	    (* ppat is the pattern we are discriminating against, curpat is the current one. *)
	    (fun acc (ppat_sign, ppat_c, (ppat_ty, ppat_tyargs), ppat)
	      (curpat_sign, curpat_c, (curpat_ty, curpat_tyargs), curpat) ->
	      match acc with
		  None -> None
		| Some (sign, len, n, c) -> (* FixMe: do not work with ppat_args *)
		    if is_included curpat ppat then
		      (* Length of previous pattern's signature *)
		      let lens = List.length ppat_sign in
		      (* Accumulated length of previous pattern's signatures *)
		      let len' = lens + len in
		      let acc =
			((* Jump over previous prevpat signs *)
			  lift_rel_context len ppat_sign @ sign,
			  len',
			  succ n, (* nth pattern *)
			 (papp evdref coq_eq_ind
			    [| lift (len' + liftsign) curpat_ty;
			       liftn (len + liftsign) (succ lens) ppat_c ;
			       lift len' curpat_c |]) ::
			   List.map (lift lens (* Jump over this prevpat signature *)) c)
		      in Some acc
		    else None)
	   (Some ([], 0, 0, [])) eqnpats pats
	 in match acc with
	     None -> c
	   | Some (sign, len, _, c') ->
	       let conj = it_mkProd_or_LetIn (mk_coq_not (mk_coq_and c'))
		 (lift_rel_context liftsign sign)
	       in
		 conj :: c)
      [] prevpatterns
  in match diffs with [] -> None
    | _ -> Some (mk_coq_and diffs)

let constrs_of_pats typing_fun env evdref eqns tomatchs sign neqs arity =
  let i = ref 0 in
  let (x, y, z) =
    List.fold_left
      (fun (branches, eqns, prevpatterns) eqn ->
	 let _, newpatterns, pats =
	   List.fold_left2
	     (fun (idents, newpatterns, pats) pat arsign ->
		let pat', cpat, idents = constr_of_pat env evdref arsign pat idents in
		  (idents, pat' :: newpatterns, cpat :: pats))
	      ([], [], []) eqn.patterns sign
	 in
	 let newpatterns = List.rev newpatterns and opats = List.rev pats in
	 let rhs_rels, pats, signlen =
	   List.fold_left
	     (fun (renv, pats, n) (sign,c, (s, args), p) ->
	       (* Recombine signatures and terms of all of the row's patterns *)
	       let sign' = lift_rel_context n sign in
	       let len = List.length sign' in
		 (sign' @ renv,
		 (* lift to get outside of previous pattern's signatures. *)
		 (sign', liftn n (succ len) c, 
		  (s, List.map (liftn n (succ len)) args), p) :: pats,
		 len + n))
	     ([], [], 0) opats in
	 let pats, _ = List.fold_left
	   (* lift to get outside of past patterns to get terms in the combined environment. *)
	   (fun (pats, n) (sign, c, (s, args), p) ->
	     let len = List.length sign in
	       ((rels_of_patsign sign, lift n c,
		 (s, List.map (lift n) args), p) :: pats, len + n))
	   ([], 0) pats
	 in
	 let ineqs = build_ineqs evdref prevpatterns pats signlen in
	 let rhs_rels' = rels_of_patsign rhs_rels in
	 let _signenv = push_rel_context rhs_rels' env in
	 let arity =
	   let args, nargs =
	     List.fold_right (fun (sign, c, (_, args), _) (allargs,n) ->
	       (args @ c :: allargs, List.length args + succ n))
	       pats ([], 0)
	   in
	   let args = List.rev args in
	     substl args (liftn signlen (succ nargs) arity)
	 in
	 let rhs_rels', tycon =
	   let neqs_rels, arity =
	     match ineqs with
	     | None -> [], arity
	     | Some ineqs ->
		 [Anonymous, None, ineqs], lift 1 arity
	   in
	   let eqs_rels, arity = decompose_prod_n_assum neqs arity in
	     eqs_rels @ neqs_rels @ rhs_rels', arity
	 in
	 let rhs_env = push_rel_context rhs_rels' env in
	 let j = typing_fun (mk_tycon tycon) rhs_env eqn.rhs.it in
	 let bbody = it_mkLambda_or_LetIn j.uj_val rhs_rels'
	 and btype = it_mkProd_or_LetIn j.uj_type rhs_rels' in
	 let _btype = evd_comb1 (Typing.e_type_of env) evdref bbody in
	 let branch_name = Id.of_string ("program_branch_" ^ (string_of_int !i)) in
	 let branch_decl = (Name branch_name, Some (lift !i bbody), (lift !i btype)) in
	 let branch =
	   let bref = GVar (Loc.ghost, branch_name) in
	     match vars_of_ctx rhs_rels with
		 [] -> bref
	       | l -> GApp (Loc.ghost, bref, l)
	 in
	 let branch = match ineqs with
	     Some _ -> GApp (Loc.ghost, branch, [ hole ])
	   | None -> branch
	 in
	 incr i;
	 let rhs = { eqn.rhs with it = Some branch } in
	   (branch_decl :: branches,
	   { eqn with patterns = newpatterns; rhs = rhs } :: eqns,
	   opats :: prevpatterns))
      ([], [], []) eqns
  in x, y

(* Builds the predicate. If the predicate is dependent, its context is
 * made of 1+nrealargs assumptions for each matched term in an inductive
 * type and 1 assumption for each term not _syntactically_ in an
 * inductive type.

 * Each matched terms are independently considered dependent or not.

 * A type constraint but no annotation case: it is assumed non dependent.
 *)

let lift_ctx n ctx =
  let ctx', _ =
    List.fold_right (fun (c, t) (ctx, n') -> 
		       (liftn n n' c, liftn_tomatch_type n n' t) :: ctx, succ n') 
      ctx ([], 0)
  in ctx'

(* Turn matched terms into variables. *)
let abstract_tomatch env tomatchs tycon =
  let prev, ctx, names, tycon =
    List.fold_left
      (fun (prev, ctx, names, tycon) (c, t) ->
	 let lenctx =  List.length ctx in
	 match kind_of_term c with
	     Rel n -> (lift lenctx c, lift_tomatch_type lenctx t) :: prev, ctx, names, tycon
	   | _ ->
	       let tycon = Option.map
		 (fun t -> subst_term (lift 1 c) (lift 1 t)) tycon in
	       let name = next_ident_away (Id.of_string "filtered_var") names in
		 (mkRel 1, lift_tomatch_type (succ lenctx) t) :: lift_ctx 1 prev,
	       (Name name, Some (lift lenctx c), lift lenctx $ type_of_tomatch t) :: ctx,
	       name :: names, tycon)
      ([], [], [], tycon) tomatchs
  in List.rev prev, ctx, tycon

let build_dependent_signature env evdref avoid tomatchs arsign =
  let avoid = ref avoid in
  let arsign = List.rev arsign in
  let allnames = List.rev_map (List.map pi1) arsign in
  let nar = List.fold_left (fun n names -> List.length names + n) 0 allnames in
  let eqs, neqs, refls, slift, arsign' =
    List.fold_left2
      (fun (eqs, neqs, refl_args, slift, arsigns) (tm, ty) arsign ->
	 (* The accumulator:
	    previous eqs,
	    number of previous eqs,
	    lift to get outside eqs and in the introduced variables ('as' and 'in'),
	    new arity signatures
	 *)
	 match ty with
	 | IsInd (ty, IndType (indf, args), _) when List.length args > 0 ->
	     (* Build the arity signature following the names in matched terms 
		as much as possible *)
	     let argsign = List.tl arsign in (* arguments in inverse application order *)
	     let (appn, appb, appt) as _appsign = List.hd arsign in (* The matched argument *)
	     let argsign = List.rev argsign in (* arguments in application order *)
	     let env', nargeqs, argeqs, refl_args, slift, argsign' =
	       List.fold_left2
		 (fun (env, nargeqs, argeqs, refl_args, slift, argsign') arg (name, b, t) ->
		    let argt = Retyping.get_type_of env !evdref arg in
		    let eq, refl_arg =
		      if Reductionops.is_conv env !evdref argt t then
			(mk_eq evdref (lift (nargeqs + slift) argt)
			   (mkRel (nargeqs + slift))
			   (lift (nargeqs + nar) arg),
			 mk_eq_refl evdref argt arg)
		      else
			(mk_JMeq evdref (lift (nargeqs + slift) t)
			   (mkRel (nargeqs + slift))
			   (lift (nargeqs + nar) argt)
			   (lift (nargeqs + nar) arg),
			 mk_JMeq_refl evdref argt arg)
		    in
		    let previd, id =
		      let name =
			match kind_of_term arg with
			Rel n -> pi1 (lookup_rel n env)
			| _ -> name
		      in
			make_prime avoid name
		    in
		      (env, succ nargeqs,
		       (Name (eq_id avoid previd), None, eq) :: argeqs,
		       refl_arg :: refl_args,
		       pred slift,
		       (Name id, b, t) :: argsign'))
		 (env, neqs, [], [], slift, []) args argsign
	     in
	     let eq = mk_JMeq evdref
	       (lift (nargeqs + slift) appt)
	       (mkRel (nargeqs + slift))
	       (lift (nargeqs + nar) ty)
	       (lift (nargeqs + nar) tm)
	     in
	     let refl_eq = mk_JMeq_refl evdref ty tm in
	     let previd, id = make_prime avoid appn in
	       (((Name (eq_id avoid previd), None, eq) :: argeqs) :: eqs,
		succ nargeqs,
		refl_eq :: refl_args,
		pred slift,
		(((Name id, appb, appt) :: argsign') :: arsigns))

	 | _ -> (* Non dependent inductive or not inductive, just use a regular equality *)
	     let (name, b, typ) = match arsign with [x] -> x | _ -> assert(false) in
	     let previd, id = make_prime avoid name in
	     let arsign' = (Name id, b, typ) in
	     let tomatch_ty = type_of_tomatch ty in
	     let eq =
	       mk_eq evdref (lift nar tomatch_ty)
		 (mkRel slift) (lift nar tm)
	     in
	       ([(Name (eq_id avoid previd), None, eq)] :: eqs, succ neqs,
		(mk_eq_refl evdref tomatch_ty tm) :: refl_args,
		pred slift, (arsign' :: []) :: arsigns))
      ([], 0, [], nar, []) tomatchs arsign
  in
  let arsign'' = List.rev arsign' in
    assert(Int.equal slift 0); (* we must have folded over all elements of the arity signature *)
    arsign'', allnames, nar, eqs, neqs, refls

let context_of_arsign l =
  let (x, _) = List.fold_right
    (fun c (x, n) ->
       (lift_rel_context n c @ x, List.length c + n))
    l ([], 0)
  in x

let compile_program_cases loc style (typing_function, evdref) tycon env
    (predopt, tomatchl, eqns) =
  let typing_fun tycon env = function
    | Some t ->	typing_function tycon env evdref t
    | None -> Evarutil.evd_comb0 use_unit_judge evdref in

  (* We build the matrix of patterns and right-hand side *)
  let matx = matx_of_eqns env eqns in

  (* We build the vector of terms to match consistently with the *)
  (* constructors found in patterns *)
  let tomatchs = coerce_to_indtype typing_function evdref env matx tomatchl in
  let tycon = valcon_of_tycon tycon in
  let tomatchs, tomatchs_lets, tycon' = abstract_tomatch env tomatchs tycon in
  let env = push_rel_context tomatchs_lets env in
  let len = List.length eqns in
  let sign, allnames, signlen, eqs, neqs, args =
    (* The arity signature *)
    let arsign = extract_arity_signature ~dolift:false env tomatchs tomatchl in
      (* Build the dependent arity signature, the equalities which makes
	 the first part of the predicate and their instantiations. *)
    let avoid = [] in
      build_dependent_signature env evdref avoid tomatchs arsign

  in
  let tycon, arity =
    match tycon' with
    | None -> let ev = mkExistential env evdref in ev, ev
    | Some t ->
	let pred = 
	  try
	    let pred = prepare_predicate_from_arsign_tycon loc tomatchs sign t in
	      (* The tycon may be ill-typed after abstraction. *)
	    let env' = push_rel_context (context_of_arsign sign) env in
	      ignore(Typing.sort_of env' evdref pred); pred
	  with e when Errors.noncritical e ->
	    let nar = List.fold_left (fun n sign -> List.length sign + n) 0 sign in
	      lift nar t
	in Option.get tycon, pred
  in
  let neqs, arity =
    let ctx = context_of_arsign eqs in
    let neqs = List.length ctx in
      neqs, it_mkProd_or_LetIn (lift neqs arity) ctx
  in
  let lets, matx =
    (* Type the rhs under the assumption of equations *)
    constrs_of_pats typing_fun env evdref matx tomatchs sign neqs arity
  in
  let matx = List.rev matx in
  let _ = assert (Int.equal len (List.length lets)) in
  let env = push_rel_context lets env in
  let matx = List.map (fun eqn -> { eqn with rhs = { eqn.rhs with rhs_env = env } }) matx in
  let tomatchs = List.map (fun (x, y) -> lift len x, lift_tomatch_type len y) tomatchs in
  let args = List.rev_map (lift len) args in
  let pred = liftn len (succ signlen) arity in
  let nal, pred = build_initial_predicate sign pred in

  (* We push the initial terms to match and push their alias to rhs' envs *)
  (* names of aliases will be recovered from patterns (hence Anonymous here) *)

  let out_tmt na = function NotInd (c,t) -> (na,c,t) | IsInd (typ,_,_) -> (na,None,typ) in
  let typs = List.map2 (fun na (tm,tmt) -> (tm,out_tmt na tmt)) nal tomatchs in
    
  let typs =
    List.map (fun (c,d) -> (c,extract_inductive_data env !evdref d,d)) typs in
    
  let dep_sign =
    find_dependencies_signature
      (List.make (List.length typs) true)
      typs in
    
  let typs' =
    List.map3
      (fun (tm,tmt) deps na ->
         let deps = if not (isRel tm) then [] else deps in
           ((tm,tmt),deps,na))
      tomatchs dep_sign nal in
    
  let initial_pushed = List.map (fun x -> Pushed (true,x)) typs' in
    
  let typing_function tycon env evdref = function
    | Some t ->	typing_function tycon env evdref t
    | None -> evd_comb0 use_unit_judge evdref in

  let pb =
    { env      = env;
      evdref   = evdref;
      pred     = pred;
      tomatch  = initial_pushed;
      history  = start_history (List.length initial_pushed);
      mat      = matx;
      caseloc  = loc;
      casestyle= style;
      typing_function = typing_function } in

  let j = compile pb in
    (* We check for unused patterns *)
    List.iter (check_unused_pattern env) matx;
    let body = it_mkLambda_or_LetIn (applistc j.uj_val args) lets in
    let j =
      { uj_val = it_mkLambda_or_LetIn body tomatchs_lets;
	uj_type = nf_evar !evdref tycon; }
    in j

(**************************************************************************)
(* Main entry of the matching compilation                                 *)

let compile_cases loc style (typing_fun, evdref) tycon env (predopt, tomatchl, eqns) =
  if predopt == None && Flags.is_program_mode () then
    compile_program_cases loc style (typing_fun, evdref) 
      tycon env (predopt, tomatchl, eqns)
  else
      
  (* We build the matrix of patterns and right-hand side *)
  let matx = matx_of_eqns env eqns in

  (* We build the vector of terms to match consistently with the *)
  (* constructors found in patterns *)
  let tomatchs = coerce_to_indtype typing_fun evdref env matx tomatchl in



  (* If an elimination predicate is provided, we check it is compatible
     with the type of arguments to match; if none is provided, we
     build alternative possible predicates *)
  let arsign = extract_arity_signature env tomatchs tomatchl in
  let preds = prepare_predicate loc typing_fun env !evdref tomatchs arsign tycon predopt in

  let compile_for_one_predicate (sigma,nal,pred) =
    (* We push the initial terms to match and push their alias to rhs' envs *)
    (* names of aliases will be recovered from patterns (hence Anonymous *)
    (* here) *)

    let out_tmt na = function NotInd (c,t) -> (na,c,t) | IsInd (typ,_,_) -> (na,None,typ) in
    let typs = List.map2 (fun na (tm,tmt) -> (tm,out_tmt na tmt)) nal tomatchs in

    let typs =
      List.map (fun (c,d) -> (c,extract_inductive_data env sigma d,d)) typs in

    let dep_sign =
      find_dependencies_signature
        (List.make (List.length typs) true)
        typs in

    let typs' =
      List.map3
        (fun (tm,tmt) deps na ->
          let deps = if not (isRel tm) then [] else deps in
          ((tm,tmt),deps,na))
        tomatchs dep_sign nal in

    let initial_pushed = List.map (fun x -> Pushed (true,x)) typs' in

    (* A typing function that provides with a canonical term for absurd cases*)
    let typing_fun tycon env evdref = function
    | Some t ->	typing_fun tycon env evdref t
    | None -> evd_comb0 use_unit_judge evdref in

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

