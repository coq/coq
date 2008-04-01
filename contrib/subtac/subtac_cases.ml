(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Cases
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

open Subtac_utils

(************************************************************************)
(*            Pattern-matching compilation (Cases)                      *)
(************************************************************************)

(************************************************************************)
(* Configuration, errors and warnings *)

open Pp

let mssg_may_need_inversion () =
  str "Found a matching with no clauses on a term unknown to have an empty inductive type"

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

type rhs =
    { rhs_env    : env;
      avoid_ids  : identifier list;
      it         : rawconstr;
    }

type equation =
    { patterns     : cases_pattern list; 
      rhs          : rhs;
      alias_stack  : name list;
      eqn_loc      : loc;
      used         : bool ref }

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

   - [PrLetIn (names,dep,pred)] types a pushed term ([Pushed]),
     if dep<>Anonymous, the term is dependent, let n=|names|, if
     n<>0 then the type of the pushed term is necessarily an
     inductive with n real arguments. Otherwise, it may be
     non inductive, or inductive without real arguments, or inductive
     originating from a subterm in which case real args are not dependent;
     it accounts for n+1 binders if dep or n binders if not dep
   - [PrProd] types abstracted term ([Abstract]); it accounts for one binder
   - [PrCcl] types the right-hand-side
   - Aliases [Alias] have no trace in [predicate_signature]
*)

type predicate_signature =
  | PrLetIn of (name list * name) * predicate_signature
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
      isevars  : Evd.evar_defs ref;
      pred     : predicate_signature option;
      tomatch  : tomatch_stack;
      history  : pattern_continuation;
      mat      : matrix;
      caseloc  : loc;
      casestyle: case_style;
      typing_function: type_constraint -> env -> rawconstr -> unsafe_judgment }

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

let inductive_template isevars env tmloc ind =
  let arsign = get_full_arity_sign env ind in
  let hole_source = match tmloc with 
    | Some loc -> fun i -> (loc, Evd.TomatchTypeParameter (ind,i))
    | None -> fun _ -> (dummy_loc, Evd.InternalHole) in
   let (_,evarl,_) =
    List.fold_right
      (fun (na,b,ty) (subst,evarl,n) ->
	match b with
        | None ->
	    let ty' = substl subst ty in
	    let e = e_new_evar isevars env ~src:(hole_source n) ty' in
	    (e::subst,e::evarl,n+1) 
	| Some b ->
	    (b::subst,evarl,n+1))
      arsign ([],[],1) in
   applist (mkInd ind,List.rev evarl)


(************************************************************************)
(* Utils *)

let mkExistential env ?(src=(dummy_loc,Evd.InternalHole)) isevars =
  e_new_evar isevars env ~src:src (new_Type ())

let evd_comb2 f isevars x y =
  let (evd',y) = f !isevars x y in
  isevars := evd';
  y


module Cases_F(Coercion : Coercion.S) : S = struct

let inh_coerce_to_ind isevars env ty tyi =
  let expected_typ = inductive_template isevars env None tyi in
     (* devrait être indifférent d'exiger leq ou pas puisque pour 
        un inductif cela doit être égal *)
  let _ = e_cumul env isevars expected_typ ty in ()

let unify_tomatch_with_patterns isevars env loc typ pats =
  match find_row_ind pats with
    | None -> NotInd (None,typ)
    | Some (_,(ind,_)) ->
	inh_coerce_to_ind isevars env typ ind;
	try IsInd (typ,find_rectype env (Evd.evars_of !isevars) typ)
	with Not_found -> NotInd (None,typ)

let find_tomatch_tycon isevars env loc = function
  (* Try if some 'in I ...' is present and can be used as a constraint *)
  | Some (_,ind,_,_) -> mk_tycon (inductive_template isevars env loc ind)
  | None -> empty_tycon

let coerce_row typing_fun isevars env pats (tomatch,(_,indopt)) =
  let loc = Some (loc_of_rawconstr tomatch) in
  let tycon = find_tomatch_tycon isevars env loc indopt in
  let j = typing_fun tycon env tomatch in
  let evd, j = Coercion.inh_coerce_to_base (loc_of_rawconstr tomatch) env !isevars j in
  isevars := evd;
  let typ = nf_evar (Evd.evars_of !isevars) j.uj_type in
  let t =
    try IsInd (typ,find_rectype env (Evd.evars_of !isevars) typ)
    with Not_found ->
      unify_tomatch_with_patterns isevars env loc typ pats in
  (j.uj_val,t)

let coerce_to_indtype typing_fun isevars env matx tomatchl =
  let pats = List.map (fun r ->  r.patterns) matx in
  let matx' = match matrix_transpose pats with
    | [] -> List.map (fun _ -> []) tomatchl (* no patterns at all *)
    | m -> m in
  List.map2 (coerce_row typing_fun isevars env) matx' tomatchl



let adjust_tomatch_to_pattern pb ((current,typ),deps) =
  (* Ideally, we could find a common inductive type to which both the
     term to match and the patterns coerce *)
  (* In practice, we coerce the term to match if it is not already an
     inductive type and it is not dependent; moreover, we use only 
     the first pattern type and forget about the others *)
  let typ = match typ with IsInd (t,_) -> t | NotInd (_,t) -> t in
  let typ =
    try IsInd (typ,find_rectype pb.env (Evd.evars_of !(pb.isevars)) typ)
    with Not_found -> NotInd (None,typ) in
  let tomatch = ((current,typ),deps) in
  match typ with
  | NotInd (None,typ) ->
      let tm1 = List.map (fun eqn -> List.hd eqn.patterns) pb.mat in
      (match find_row_ind tm1 with
	| None -> tomatch
	| Some (_,(ind,_)) ->
	    let indt = inductive_template pb.isevars pb.env None ind in
	    let current =
	      if deps = [] & isEvar typ then
	      (* Don't insert coercions if dependent; only solve evars *)
		let _ = e_cumul pb.env pb.isevars indt typ in
		current
	      else
		(evd_comb2 (Coercion.inh_conv_coerce_to dummy_loc pb.env)
		  pb.isevars (make_judge current typ) (mk_tycon_type indt)).uj_val in
	    let sigma = Evd.evars_of !(pb.isevars) in
	    let typ = IsInd (indt,find_rectype pb.env sigma indt) in
	    ((current,typ),deps))
  | _ -> tomatch

   (* extract some ind from [t], possibly coercing from constructors in [tm] *)
let to_mutind env isevars tm c t =
(*  match c with
    | Some body -> *) NotInd (c,t)
(*    | None -> unify_tomatch_with_patterns isevars env t tm*)

let type_of_tomatch = function
  | IsInd (t,_) -> t
  | NotInd (_,t) -> t

let mkDeclTomatch na = function
  | IsInd (t,_) -> (na,None,t)
  | NotInd (c,t) -> (na,c,t)

let map_tomatch_type f = function
  | IsInd (t,ind) -> IsInd (f t,map_inductive_type f ind)
  | NotInd (c,t) -> NotInd (Option.map f c, f t)

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
      if Closure.mind_equiv env ind' ind then
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
    | [] -> errorlabstrm "build_leaf" (mssg_may_need_inversion())
    | eqn::_ ->
	set_used_pattern eqn;
	eqn.rhs

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

   [match y with (S (S x)) => x | x => x end] should be compiled into
   [match y with O => y | (S n) => match n with O => y | (S x) => x end end]

   and [match y with (S (S n)) => n | n => n end] into 
   [match y with O => y | (S n0) => match n0 with O => y | (S n) => n end end]

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

let recover_alias_names get_name = List.map2 (fun x (_,c,t) ->(get_name x,c,t))

let all_name sign = List.map (fun (n, b, t) -> let n = match n with Name _ -> n | Anonymous -> Name (id_of_string "Anonymous") in
				(n, b, t)) sign

let push_rels_eqn sign eqn =
  let sign = all_name sign in
(*    trace (str "push_rels_eqn: " ++ my_print_rel_context eqn.rhs.rhs_env sign ++ str "end");   *)
(* 	str " branch is " ++ my_print_constr (fst eqn.rhs.c_orig) (snd eqn.rhs.c_orig)); *)
(*   let rhs = eqn.rhs in *)
(*   let l, c, s, e = *)
(*     List.fold_right *)
(*       (fun (na, c, t) (itlift, it, sign, env) -> *)
(* 	 (try trace (str "Pushing decl: " ++ pr_rel_decl env (na, c, t) ++ *)
(* 		  str " lift is " ++ int itlift); *)
(* 	 with _ -> trace (str "error in push_rels_eqn")); *)
(* 	 let env' = push_rel (na, c, t) env in *)
(* 	   match sign with  *)
(* 	       [] -> (itlift, lift 1 it, sign, env') *)
(* 	     | (na', c, t) :: sign' ->  *)
(* 		 if na' = na then  *)
(* 		   (pred itlift, it, sign', env') *)
(* 		 else ( *)
(* 		   trace (str "skipping it"); *)
(* 		   (itlift, liftn 1 itlift it, sign, env'))) *)
(*       sign (rhs.rhs_lift, rhs.c_it, eqn.rhs.rhs_sign, eqn.rhs.rhs_env) *)
(*   in *)
    {eqn with rhs = {eqn.rhs with rhs_env = push_rels sign eqn.rhs.rhs_env; } }

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
    push_rels_eqn thissign { eqn with  alias_stack = alias_rest; }
	    

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

(* Inferring the predicate *)
let prepare_unif_pb typ cs =
  let n = List.length (assums_of_rel_context cs.cs_args) in

  (* We may need to invert ci if its parameters occur in typ *)
  let typ' =
    if noccur_between_without_evar 1 n typ then lift (-n) typ
    else (* TODO4-1 *)
      error "Unable to infer return clause of this pattern-matching problem" in
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

- Clearly, if xij occurs in Ti, then, a "match z with (Ci xi1..xipi) => ..."
  should be inserted somewhere in Ti.

- If T is undefined, an easy solution is to insert a "match z with (Ci
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
  let pv'= Array.map (fun (n,sign,_,p) -> n,splay_constr (whd_betaiotaevar (push_rels (List.rev sign) env) (Evd.evars_of isevars)) p) pv in
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
  (* Il faudra substituer les isevars a un certain moment *)
  if Array.length cstrs = 0 then (* "TODO4-3" *)
    error "Inference of annotation for empty inductive types not implemented"
  else
    (* Empiric normalization: p may depend in a irrelevant way on args of the*)
    (* cstr as in [c:{_:Alpha & Beta}] match c with (existS a b)=>(a,b) end *)
    let typs =
      Array.map (local_strong (whd_betaevar empty_env (Evd.evars_of !isevars))) typs
    in
    let eqns = array_map2 prepare_unif_pb typs cstrs in
    (* First strategy: no dependencies at all *)
(*
    let (mis,_) = dest_ind_family indf in
    let (cclargs,_,typn) = eqns.(mis_nconstr mis -1) in
*)
    let (sign,_) = get_arity env indf in
    let mtyp =
      if array_exists is_Type typs then
	(* Heuristic to avoid comparison between non-variables algebric univs*)
	new_Type ()
      else
	mkExistential env ~src:(loc, Evd.CasesType) isevars
    in
    if array_for_all (fun (_,_,typ) -> e_cumul env isevars typ mtyp) eqns
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
  | PrLetIn ((names,dep as tm),pred) ->
      let k' = List.length names + (if dep<>Anonymous then 1 else 0) in
      PrLetIn (tm, map_predicate f (k+k') pred)

let rec noccurn_predicate k = function
  | PrCcl ccl -> noccurn k ccl
  | PrProd pred -> noccurn_predicate (k+1) pred
  | PrLetIn ((names,dep),pred) ->
      let k' = List.length names + (if dep<>Anonymous then 1 else 0) in
      noccurn_predicate (k+k') pred

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
  | PrLetIn (([],dep),pred) ->
      subst_predicate ([],if dep<>Anonymous then Some cur else None) pred
  | PrLetIn ((_,dep),pred) ->
      (match typ with
        | IsInd (_,IndType (_,realargs)) ->
           subst_predicate (realargs,if dep<>Anonymous then Some cur else None) pred
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
let generalize_predicate ny d = function
  | PrLetIn ((names,dep as tm),pred) ->
      if dep=Anonymous then anomaly "Undetected dependency";
      let p = List.length names + 1 in
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
  | PrLetIn (([],dep),pred), Pushed ((cur,_),_)::tms ->
      extract_predicate (if dep<>Anonymous then cur::l else l) (pred,tms)
  | PrLetIn ((_,dep),pred), Pushed ((cur,IsInd (_,(IndType(_,realargs)))),_)::tms ->
      let l = List.rev realargs@l in
      extract_predicate (if dep<>Anonymous then cur::l else l) (pred,tms)
  | PrCcl ccl, [] ->
      substl l ccl
  | _ -> anomaly"extract_predicate: predicate inconsistent with terms to match"

let abstract_predicate env sigma indf cur tms = function
  | (PrProd _ | PrCcl _) -> anomaly "abstract_predicate: must be some LetIn"
  | PrLetIn ((names,dep),pred) ->
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
      let sign,k =
        if names = [] & n <> 1 then
          (* Real args were not considered *)
          (if dep<>Anonymous then
            ((let (_,c,t) = List.hd sign in (dep,c,t)::List.tl sign),n-1)
          else
            (sign,n))
        else
          (* Real args are OK *)
          (List.map2 (fun na (_,c,t) -> (na,c,t)) (dep::names) sign,
           if dep<>Anonymous then 0 else 1) in
      let pred = lift_predicate k pred in
      let pred = extract_predicate [] (pred,tms) in
      (true, it_mkLambda_or_LetIn_name env pred sign)

let rec known_dependent = function
  | None -> false
  | Some (PrLetIn ((_,dep),_)) -> dep<>Anonymous
  | Some (PrCcl _) -> false
  | Some (PrProd _) ->
      anomaly "known_dependent: can only be used when patterns remain"

(* [expand_arg] is used by [specialize_predicate]
   it replaces gamma, x1...xn, x1...xk |- pred
   by gamma, x1...xn, x1...xk-1 |- [X=realargs,xk=xk]pred (if dep) or
   by gamma, x1...xn, x1...xk-1 |- [X=realargs]pred (if not dep) *)

let expand_arg n alreadydep (na,t) deps (k,pred) =
  (* current can occur in pred even if the original problem is not dependent *)
  let dep =
    if alreadydep<>Anonymous then alreadydep
    else if deps = [] && noccurn_predicate 1 pred then Anonymous
    else Name (id_of_string "x") in
  let pred = if dep<>Anonymous then pred else lift_predicate (-1) pred in
  (* There is no dependency in realargs for subpattern *)
  (k-1, PrLetIn (([],dep), pred))


(*****************************************************************************)
(* pred = [X:=realargs;x:=c]P types the following problem:                   *)
(*                                                                           *)
(*  Gamma |- match Pushed(c:I(realargs)) rest with...end: pred               *)
(*                                                                           *)
(* where the branch with constructor Ci:(x1:T1)...(xn:Tn)->I(realargsi)      *)
(* is considered. Assume each Ti is some Ii(argsi).                          *)
(* We let e=Ci(x1,...,xn) and replace pred by                                *)
(*                                                                           *)
(* pred' = [X1:=rargs1,x1:=x1']...[Xn:=rargsn,xn:=xn'](P[X:=realargsi;x:=e]) *)
(*                                                                           *)
(* s.t Gamma,x1'..xn' |- match Pushed(x1')..Pushed(xn') rest with..end :pred'*)
(*                                                                           *)
(*****************************************************************************)
let specialize_predicate tomatchs deps cs = function
  | (PrProd _ | PrCcl _) ->
      anomaly "specialize_predicate: a matched pattern must be pushed"
  | PrLetIn ((names,isdep),pred) ->
      (* Assume some gamma st: gamma, (X,x:=realargs,copt) |- pred *)
      let nrealargs = List.length names in
      let k = nrealargs + (if isdep<>Anonymous then 1 else 0) in
      (* We adjust pred st: gamma, x1..xn, (X,x:=realargs,copt) |- pred' *)
      let n = cs.cs_nargs in
      let pred' = liftn_predicate n (k+1) pred in
      let argsi = if nrealargs <> 0 then Array.to_list cs.cs_concl_realargs else [] in
      let copti = if isdep<>Anonymous then Some (build_dependent_constructor cs) else None in
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
      | Some p -> abstract_predicate env (Evd.evars_of !isevars) indf current tms p
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
		 let n = cstrs.(i-1).cs_nargs in
		 let args = make_anonymous_patvars n in
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
let rec generalize_problem pb = function
  | [] -> pb
  | i::l ->
      let d = map_rel_declaration (lift i) (Environ.lookup_rel i pb.env) in
      let pb' = generalize_problem pb l in
      let tomatch = lift_tomatch_stack 1 pb'.tomatch in
      let tomatch = regeneralize_index_tomatch (i+1) tomatch in
      { pb with
	  tomatch = Abstract d :: tomatch;
          pred = Option.map (generalize_predicate i d) pb'.pred }

(* No more patterns: typing the right-hand-side of equations *)
let build_leaf pb =
  let rhs = extract_rhs pb in
  let tycon = match pb.pred with
    | None -> anomaly "Predicate not found"
    | Some (PrCcl typ) -> mk_tycon typ
    | Some _ -> anomaly "not all parameters of pred have been consumed" in
    pb.typing_function tycon rhs.rhs_env rhs.it

(* Building the sub-problem when all patterns are variables *)
let shift_problem (current,t) pb =
  {pb with
     tomatch = Alias (current,current,NonDepAlias,type_of_tomatch t)::pb.tomatch;
     pred = Option.map (specialize_predicate_var (current,t)) pb.pred;
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
  let env' = push_rels sign pb.env in
  let pred' = Option.map (specialize_predicate (List.rev typs') dep_sign const_info) pb.pred in
    sign,
  { pb with
      env = env';
      tomatch = List.rev_append currents tomatch;
      pred = pred';
      history = history;
      mat = List.map (push_rels_eqn_with_names sign) submat }

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
    | (Abstract d)::rest -> compile_generalization pb d rest
    | [] -> build_leaf pb

and match_current pb tomatch =
  let ((current,typ as ct),deps) = adjust_tomatch_to_pattern pb tomatch in
  match typ with
    | NotInd (_,typ) ->
	check_all_variables typ pb.mat;
	compile (shift_problem ct pb)
    | IsInd (_,(IndType(indf,realargs) as indt)) ->
	let mind,_ = dest_ind_family indf in
	let cstrs = get_constructors pb.env indf in
	let eqns,onlydflt = group_equations pb mind current cstrs pb.mat in
	if (Array.length cstrs <> 0 or pb.mat <> []) & onlydflt  then
	  compile (shift_problem ct pb)
	else
          let _constraints = Array.map (solve_constraints indt) cstrs in

	  (* We generalize over terms depending on current term to match *)
	  let pb = generalize_problem pb deps in

	  (* We compile branches *)
	  let brs = array_map2 (compile_branch current deps pb) eqns cstrs in

	  (* We build the (elementary) case analysis *)
	  let brvals = Array.map (fun (v,_) -> v) brs in
	  let brtyps = Array.map (fun (_,t) -> t) brs in
	  let (pred,typ,s) =
	    find_predicate pb.caseloc pb.env pb.isevars 
	      pb.pred brtyps cstrs current indt pb.tomatch in
	  let ci = make_case_info pb.env mind pb.casestyle in
	  let case = mkCase (ci,nf_betaiota pred,current,brvals) in
	  let inst = List.map mkRel deps in
	  { uj_val = applist (case, inst);
	    uj_type = substl inst typ }

and compile_branch current deps pb eqn cstr =
  let sign, pb = build_branch current deps pb eqn cstr in
  let j = compile pb in
  (it_mkLambda_or_LetIn j.uj_val sign, j.uj_type)

and compile_generalization pb d rest =
  let pb =
    { pb with
       env = push_rel d pb.env;
       tomatch = rest;
       pred = Option.map ungeneralize_predicate pb.pred;
       mat = List.map (push_rels_eqn [d]) pb.mat } in
  let j = compile pb in
  { uj_val = mkLambda_or_LetIn d j.uj_val;
    uj_type = mkProd_or_LetIn d j.uj_type }

and compile_alias pb (deppat,nondeppat,d,t) rest =
  let history = simplify_history pb.history in
  let sign, newenv, mat =
    insert_aliases pb.env (Evd.evars_of !(pb.isevars)) (deppat,nondeppat,d,t) pb.mat in
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
       pred = Option.map (lift_predicate n) pb.pred;
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
let matx_of_eqns env eqns =
  let build_eqn (loc,ids,lpat,rhs) =
    let rhs =
      { rhs_env = env;
	avoid_ids = ids@(ids_of_named_context (named_context env));
	it = rhs;
      } in
    { patterns = lpat;
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
  let rec decomp_lam_force n l p =
    if n=0 then (l,p) else
    match kind_of_term p with
      | Lambda (na,_,c) -> decomp_lam_force (n-1) (na::l) c
      | _ -> (* eta-expansion *)
          let na = Name (id_of_string "x") in
          decomp_lam_force (n-1) (na::l) (applist (lift 1 p, [mkRel 1])) in
  let rec buildrec allnames p = function
    | [] -> (List.rev allnames,p)
    | tm::ltm ->
	match cook tm with
	  | None -> 
              let p = 
                (* adjust to a sign containing the NotInd's *)
                if isdep then lift 1 p else p in
              let names = if isdep then [Anonymous] else [] in
              buildrec (names::allnames) p ltm
	  | Some n ->
              let n = if isdep then n+1 else n in
              let names,p = decomp_lam_force n [] p in
              buildrec (names::allnames) p ltm
  in buildrec [] pred tomatchl

let set_arity_signature dep n arsign tomatchl pred x =
  (* avoid is not exhaustive ! *)
  let rec decomp_lam_force n avoid l p =
    if n = 0 then (List.rev l,p,avoid) else
    match p with
      | RLambda (_,(Name id as na),k,_,c) -> 
          decomp_lam_force (n-1) (id::avoid) (na::l) c
      | RLambda (_,(Anonymous as na),k,_,c) -> decomp_lam_force (n-1) avoid (na::l) c
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

let oldprepare_predicate_from_tycon loc dep env isevars tomatchs sign c =
  let cook (n, l, env, signs) = function
    | c,IsInd (_,IndType(indf,realargs)) ->
	let indf' = lift_inductive_family n indf in
	let sign = make_arity_signature env dep indf' in
	let p = List.length realargs in
	if dep then
	  (n + p + 1, c::(List.rev realargs)@l, push_rels sign env,sign::signs)
	else
	  (n + p, (List.rev realargs)@l, push_rels sign env,sign::signs)
    | c,NotInd _ ->
	(n, l, env, []::signs) in
  let n, allargs, env, signs = List.fold_left cook (0, [], env, []) tomatchs in
  let names = List.rev (List.map (List.map pi1) signs) in
  let allargs =
    List.map (fun c -> lift n (nf_betadeltaiota env (Evd.evars_of !isevars) c)) allargs in
  let rec build_skeleton env c =
    (* Don't put into normal form, it has effects on the synthesis of evars *)
 (* let c = whd_betadeltaiota env (evars_of isevars) c in *)
    (* We turn all subterms possibly dependent into an evar with maximum ctxt*)
    if isEvar c or List.exists (eq_constr c) allargs then
      e_new_evar isevars env  ~src:(loc, Evd.CasesType)
        (Retyping.get_type_of env (Evd.evars_of !isevars) c)
    else
      map_constr_with_full_binders push_rel build_skeleton env c 
  in
    names, build_skeleton env (lift n c)
  
(* Here, [pred] is assumed to be in the context built from all *)
(* realargs and terms to match *)
let build_initial_predicate isdep allnames pred =
  let nar = List.fold_left (fun n names -> List.length names + n) 0 allnames in
  let rec buildrec n pred = function
    | [] -> PrCcl pred
    | names::lnames ->
        let names' = if isdep then List.tl names else names in
        let n' = n + List.length names' in
        let pred, p, user_p =
          if isdep then 
            if dependent (mkRel (nar-n')) pred then pred, 1, 1
            else liftn (-1) (nar-n') pred, 0, 1
          else pred, 0, 0 in
        let na =
          if p=1 then
            let na = List.hd names in
            if na = Anonymous then
              (* peut arriver en raison des evars *)
              Name (id_of_string "x") (*Hum*)
            else na
          else Anonymous in
        PrLetIn ((names',na), buildrec (n'+user_p) pred lnames)
  in buildrec 0 pred allnames

let extract_arity_signature env0 tomatchl tmsign =
  let get_one_sign n tm (na,t) =
    match tm with
      | NotInd (bo,typ) -> 
	  (match t with
	    | None -> [na,Option.map (lift n) bo,lift n typ]
	    | Some (loc,_,_,_) -> 
 	    user_err_loc (loc,"",
	    str "Unexpected type annotation for a term of non inductive type"))
      | IsInd (_,IndType(indf,realargs)) ->
          let indf' = lift_inductive_family n indf in
	  let (ind,params) = dest_ind_family indf' in
	  let nrealargs = List.length realargs in
	  let realnal =
	    match t with
	      | Some (loc,ind',nparams,realnal) ->
		  if ind <> ind' then
		    user_err_loc (loc,"",str "Wrong inductive type");
		  if List.length params <> nparams
		    or nrealargs <> List.length realnal then
		      anomaly "Ill-formed 'in' clause in cases";
		  List.rev realnal
	      | None -> list_tabulate (fun _ -> Anonymous) nrealargs in
	  let arsign = fst (get_arity env0 indf') in
	  (na,None,build_dependent_inductive env0 indf')
	  ::(List.map2 (fun x (_,c,t) ->(x,c,t)) realnal arsign) in
  let rec buildrec n = function
    | [],[] -> []
    | (_,tm)::ltm, x::tmsign ->
	let l = get_one_sign n tm x in
	l :: buildrec (n + List.length l) (ltm,tmsign)
    | _ -> assert false
  in List.rev (buildrec 0 (tomatchl,tmsign))

let extract_arity_signatures env0 tomatchl tmsign =
  let get_one_sign tm (na,t) =
    match tm with
      | NotInd (bo,typ) -> 
	  (match t with
	    | None -> [na,bo,typ]
	    | Some (loc,_,_,_) -> 
 	    user_err_loc (loc,"",
	    str "Unexpected type annotation for a term of non inductive type"))
      | IsInd (_,IndType(indf,realargs)) ->
	  let (ind,params) = dest_ind_family indf in
	  let nrealargs = List.length realargs in
	  let realnal =
	    match t with
	      | Some (loc,ind',nparams,realnal) ->
		  if ind <> ind' then
		    user_err_loc (loc,"",str "Wrong inductive type");
		  if List.length params <> nparams
		    or nrealargs <> List.length realnal then
		      anomaly "Ill-formed 'in' clause in cases";
		  List.rev realnal
	      | None -> list_tabulate (fun _ -> Anonymous) nrealargs in
	  let arsign = fst (get_arity env0 indf) in
	    (na,None,build_dependent_inductive env0 indf)
	    ::(try List.map2 (fun x (_,c,t) ->(x,c,t)) realnal arsign with _ -> assert false) in
  let rec buildrec = function
    | [],[] -> []
    | (_,tm)::ltm, x::tmsign ->
	let l = get_one_sign tm x in
	  l :: buildrec (ltm,tmsign)
    | _ -> assert false
  in List.rev (buildrec (tomatchl,tmsign))

let inh_conv_coerce_to_tycon loc env isevars j tycon =
  match tycon with
    | Some p ->
	let (evd',j) = Coercion.inh_conv_coerce_to loc env !isevars j p in
          isevars := evd';
          j
    | None -> j

let out_ind = function IsInd (_, IndType(x, y)) -> (x, y) | _ -> assert(false)
	       
let string_of_name name = 
  match name with
    | Anonymous -> "anonymous"
    | Name n -> string_of_id n
	
let id_of_name n = id_of_string (string_of_name n)

let make_prime_id name = 
  let str = string_of_name name in
    id_of_string str, id_of_string (str ^ "'")

let prime avoid name = 
  let previd, id = make_prime_id name in
    previd, next_ident_away_from id avoid

let make_prime avoid prevname =
  let previd, id = prime !avoid prevname in
    avoid := id :: !avoid;
    previd, id

let eq_id avoid id = 
  let hid = id_of_string ("Heq_" ^ string_of_id id) in
  let hid' = next_ident_away_from hid avoid in
    hid'

let mk_eq typ x y = mkApp (Lazy.force eq_ind, [| typ; x ; y |])
let mk_eq_refl typ x = mkApp (Lazy.force eq_refl, [| typ; x |])
let mk_JMeq typ x typ' y = 
  mkApp (Lazy.force Subtac_utils.jmeq_ind, [| typ; x ; typ'; y |])
let mk_JMeq_refl typ x = mkApp (Lazy.force Subtac_utils.jmeq_refl, [| typ; x |])
    
let hole = RHole (dummy_loc, Evd.QuestionMark true)

let context_of_arsign l =
  let (x, _) = List.fold_right
    (fun c (x, n) -> 
      (lift_rel_context n c @ x, List.length c + n))
    l ([], 0)
  in x

let constr_of_pat env isevars arsign pat avoid = 
  let rec typ env (ty, realargs) pat avoid = 
    trace (str "Typing pattern " ++ Printer.pr_cases_pattern pat ++ str " in env " ++
	     print_env env ++ str" should have type: " ++ my_print_constr env ty);
    match pat with
    | PatVar (l,name) -> 
	trace (str "Treating pattern variable " ++ str (string_of_id (id_of_name name)));
	let name, avoid = match name with
	    Name n -> name, avoid
	  | Anonymous -> 
	      let previd, id = prime avoid (Name (id_of_string "wildcard")) in
		Name id, id :: avoid 
	in
	  trace (str "Treated pattern variable " ++ str (string_of_id (id_of_name name)));
	  PatVar (l, name), [name, None, ty] @ realargs, mkRel 1, ty, (List.map (fun x -> mkRel 1) realargs), 1, avoid
    | PatCstr (l,((_, i) as cstr),args,alias) ->
	let cind = inductive_of_constructor cstr in
	let IndType (indf, _) = find_rectype env (Evd.evars_of !isevars) (lift (-(List.length realargs)) ty) in
	let ind, params = dest_ind_family indf in
	if ind <> cind then error_bad_constructor_loc l cstr ind;
	let cstrs = get_constructors env indf in
	let ci = cstrs.(i-1) in
	let nb_args_constr = ci.cs_nargs in
	assert(nb_args_constr = List.length args);
	let patargs, args, sign, env, n, m, avoid = 
	  List.fold_right2
	    (fun (na, c, t) ua (patargs, args, sign, env, n, m, avoid)  ->
	       let pat', sign', arg', typ', argtypargs, n', avoid = 
		 typ env (lift (n - m) t, []) ua avoid 
	       in
	       let args' = arg' :: List.map (lift n') args in
	       let env' = push_rels sign' env in
		 (pat' :: patargs, args', sign' @ sign, env', n' + n, succ m, avoid))
	    ci.cs_args (List.rev args) ([], [], [], env, 0, 0, avoid)
	in
	let args = List.rev args in
	let patargs = List.rev patargs in
	let pat' = PatCstr (l, cstr, patargs, alias) in
	let cstr = mkConstruct ci.cs_cstr in
	let app = applistc cstr (List.map (lift (List.length sign)) params) in
	let app = applistc app args in
	  trace (str "Getting type of app: " ++ my_print_constr env app);
	let apptype = Retyping.get_type_of env (Evd.evars_of !isevars) app in	
	  trace (str "Family and args of apptype: " ++ my_print_constr env apptype);
	let IndType (indf, realargs) = find_rectype env (Evd.evars_of !isevars) apptype in
	  trace (str "Got Family and args of apptype: " ++ my_print_constr env apptype);
	  match alias with
	      Anonymous ->
		pat', sign, app, apptype, realargs, n, avoid
	    | Name id ->
		let sign = (alias, None, lift m ty) :: sign in
		let avoid = id :: avoid in
		let sign, i, avoid =
		  try
		    let env = push_rels sign env in
		    isevars := the_conv_x_leq (push_rels sign env) (lift (succ m) ty) (lift 1 apptype) !isevars;
		    trace (str "convertible types for alias : " ++ my_print_constr env (lift (succ m) ty)
		    ++ my_print_constr env (lift 1 apptype));
		    let eq_t = mk_eq (lift (succ m) ty)
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
(*   let tycon, arity = mk_tycon_from_sign env isevars arsign arity in *)
  let pat', sign, patc, patty, args, z, avoid = typ env (pi3 (List.hd arsign), List.tl arsign) pat avoid in 
  let c = it_mkProd_or_LetIn patc sign in
  trace (str "arity signature is : " ++ my_print_rel_context env arsign);
  trace (str "signature is : " ++ my_print_rel_context env sign);
  trace (str "patty, args are : " ++ my_print_constr env (applistc patty args));
  trace (str "Constr_of_pat gives: " ++ my_print_constr env c);
  trace (str "with args: " ++ pp_list (my_print_constr (push_rels sign env)) args);
  pat', (sign, patc, (pi3 (List.hd arsign), args), pat'), avoid


(* shadows functional version *)
let eq_id avoid id = 
  let hid = id_of_string ("Heq_" ^ string_of_id id) in
  let hid' = next_ident_away_from hid !avoid in
    avoid := hid' :: !avoid;
    hid'

let rels_of_patsign = 
  List.map (fun ((na, b, t) as x) -> 
    match b with 
      | Some t' when kind_of_term t' = Rel 0 -> (na, None, t)
      | _ -> x)

let vars_of_ctx ctx = 
  let _, y =
    List.fold_right (fun (na, b, t)  (prev, vars) -> 
      match b with 
	| Some t' when kind_of_term t' = Rel 0 -> 
	    prev, 
	    (RApp (dummy_loc, 
		(RRef (dummy_loc, Lazy.force refl_ref)), [hole; RVar (dummy_loc, prev)])) :: vars
	| _ ->
	    match na with
		Anonymous -> raise (Invalid_argument "vars_of_ctx")
	      | Name n -> n, RVar (dummy_loc, n) :: vars)
      ctx (id_of_string "vars_of_ctx: error", [])
  in List.rev y

let rec is_included x y = 
  match x, y with
    | PatVar _, _ -> true
    | _, PatVar _ -> true
    | PatCstr (l, (_, i), args, alias), PatCstr (l', (_, i'), args', alias')  ->
	if i = i' then List.for_all2 is_included args args'
	else false

(* liftsign is the current pattern's complete signature length. Hence pats is already typed in its
   full signature. However prevpatterns are in the original one signature per pattern form.
 *)
let build_ineqs prevpatterns pats liftsign =
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
(* 			trace (str "Lifting " ++ my_print_constr Environ.empty_env curpat_c ++ str " by " *)
(* 				  ++ int len'); *)
(* 			trace (str "treating " ++ my_print_constr (push_rel_context ppat_sign Environ.empty_env) ppat_c); *)
		      let acc = 
			((* Jump over previous prevpat signs *)
			  lift_rel_context len ppat_sign @ sign, 
			  len',
			  succ n, (* nth pattern *)
			  mkApp (Lazy.force eq_ind,
				[| lift (succ len') curpat_ty ;
				   liftn (len + liftsign) (succ lens) ppat_c ;
				   lift len' curpat_c |]) :: 
			    List.map (lift lens (* Jump over this prevpat signature *)) c)
		      in Some acc
		    else None)
	   (Some ([], 0, 0, [])) eqnpats pats
	 in match acc with 
	     None -> c
	   | Some (sign, len, _, c') ->
	       let conj = it_mkProd_or_LetIn (mk_not (mk_conj c')) 
		 (lift_rel_context liftsign sign) 
	       in
		 conj :: c)
      [] prevpatterns
  in match diffs with [] -> None
    | _ -> Some (mk_conj diffs)
	
let subst_rel_context k ctx subst =
  let (_, ctx') =
    List.fold_right 
      (fun (n, b, t) (k, acc) ->
	 (succ k, (n, Option.map (substnl subst k) b, substnl subst k t) :: acc))
      ctx (k, [])
  in ctx'

let lift_rel_contextn n k sign =
  let rec liftrec k = function
    | (na,c,t)::sign ->
	(na,Option.map (liftn n k) c,liftn n k t)::(liftrec (k-1) sign)
    | [] -> []
  in
  liftrec (rel_context_length sign + k) sign

let constrs_of_pats typing_fun tycon env isevars eqns tomatchs sign neqs eqs arity =
  let i = ref 0 in
  let (x, y, z) = 
    List.fold_left
      (fun (branches, eqns, prevpatterns) eqn ->
	 let _, newpatterns, pats = 
	   List.fold_left2
	     (fun (idents, newpatterns, pats) pat arsign -> 
		let pat', cpat, idents = constr_of_pat env isevars arsign pat idents in
		  (idents, pat' :: newpatterns, cpat :: pats))
	      ([], [], []) eqn.patterns sign
	 in
	 let newpatterns = List.rev newpatterns and opats = List.rev pats in
	 let rhs_rels, pats, signlen = 
	   List.fold_left 
	     (fun (renv, pats, n) (sign,c, (s, args), p) -> 
	       (* Recombine signatures and terms of all of the row's patterns *)
(* 	       trace (str "treating pattern:" ++ my_print_constr Environ.empty_env c); *)
	       let sign' = lift_rel_context n sign in
	       let len = List.length sign' in
		 (sign' @ renv, 
		 (* lift to get outside of previous pattern's signatures. *)
		 (sign', liftn n (succ len) c, (s, List.map (liftn n (succ len)) args), p) :: pats,
		 len + n))
	     ([], [], 0) opats in
	 let pats, _ = List.fold_left 
	   (* lift to get outside of past patterns to get terms in the combined environment. *)
	   (fun (pats, n) (sign, c, (s, args), p) ->
	     let len = List.length sign in
	       ((rels_of_patsign sign, lift n c, (s, List.map (lift n) args), p) :: pats, len + n))
	   ([], 0) pats
	 in
	 let ineqs = build_ineqs prevpatterns pats signlen in
	 let rhs_rels' = rels_of_patsign rhs_rels in
	 let _signenv = push_rel_context rhs_rels' env in
	 let eqs_rels = 
	   let eqs = (*List.concat (List.rev eqs)*) context_of_arsign eqs in
	   let args, nargs = 
	     List.fold_right (fun (sign, c, (_, args), _) (allargs,n) ->
(* 	       trace (str "treating arg:" ++ my_print_constr Environ.empty_env c); *)
	       (args @ c :: allargs, List.length args + succ n))
	       pats ([], 0)
	   in
	   let args = List.rev args in
(* 	     trace (str " equalities " ++ my_print_rel_context Environ.empty_env eqs); *)
(* 	     trace (str " args " ++ pp_list (my_print_constr _signenv) args); *)
	     (* Make room for substitution of prime arguments by constr patterns *)
	     let eqs' = lift_rel_contextn signlen nargs eqs in
	     let eqs'' = subst_rel_context 0 eqs' args in
(* 	       trace (str " new equalities " ++ my_print_rel_context Environ.empty_env eqs'); *)
(* 	       trace (str " subtituted equalities " ++ my_print_rel_context _signenv eqs''); *)
	     eqs''
	 in
	   trace (str "Env with signature is: " ++ my_print_env _signenv);
	 let rhs_rels', lift_ineqs = 
	   match ineqs with
	       None -> eqs_rels @ rhs_rels', 0
	     | Some ineqs -> 
		 let _ = trace (str"Generated inequalities: " ++ my_print_constr _signenv ineqs) in
		 lift_rel_context 1 eqs_rels @ ((Anonymous, None, ineqs) :: rhs_rels'), 1
	 in
	 let rhs_env = push_rels rhs_rels' env in
(* 	          (try trace (str "branch env: " ++ print_env rhs_env) *)
(* 	   	with _ -> trace (str "error in print branch env")); *)
	 let tycon = lift_tycon (List.length eqs_rels + lift_ineqs + signlen) tycon in
	   
	 let j = typing_fun tycon rhs_env eqn.rhs.it in
(* 	   	 (try trace (str "in env: " ++ my_print_env rhs_env ++ str"," ++ *)
(* 	   		       str "Typed branch: " ++ Prettyp.print_judgment rhs_env j); *)
(* 	   	  with _ -> *)
(* 	   	    trace (str "Error in typed branch pretty printing")); *)
	 let bbody = it_mkLambda_or_LetIn j.uj_val rhs_rels'
	 and btype = it_mkProd_or_LetIn j.uj_type rhs_rels' in
	 let branch_name = id_of_string ("branch_" ^ (string_of_int !i)) in
	 let branch_decl = (Name branch_name, Some (lift !i bbody), (lift !i btype)) in
	   (* 	 (try trace (str "Branch decl: " ++ pr_rel_decl env (Name branch_name, Some bbody, btype)) *)
	   (* 	  with _ -> trace (str "Error in branch decl pp")); *)
	 let branch = 
	   let bref = RVar (dummy_loc, branch_name) in
	     match vars_of_ctx rhs_rels with
		 [] -> bref
	       | l -> RApp (dummy_loc, bref, l)
	 in
	 let branch = match ineqs with
	     Some _ -> RApp (dummy_loc, branch, [ hole ])
	   | None -> branch
	 in
	   (* 	 let branch =  *)
	   (* 	   List.fold_left (fun br (eqH, _, t) -> RLambda (dummy_loc, eqH, RHole (dummy_loc, Evd.InternalHole), br)) branch eqs_rels *)
	   (* 	 in *)
	   (* 	 (try trace (str "New branch: " ++ Printer.pr_rawconstr branch) *)
	   (* 	  with _ -> trace (str "Error in new branch pp")); *)
	   incr i;
	   let rhs = { eqn.rhs with it = branch } in
	     (branch_decl :: branches,
	      { eqn with patterns = newpatterns; rhs = rhs } :: eqns,
	      opats :: prevpatterns))
      ([], [], []) eqns
  in x, y
      

(* 		   liftn_rel_declaration *)


(* Builds the predicate. If the predicate is dependent, its context is
 * made of 1+nrealargs assumptions for each matched term in an inductive
 * type and 1 assumption for each term not _syntactically_ in an
 * inductive type.

 * Each matched terms are independently considered dependent or not.

 * A type constraint but no annotation case: it is assumed non dependent.
 *)

let prepare_predicate_from_rettyp loc typing_fun isevars env tomatchs sign tycon rtntyp =
  (* We extract the signature of the arity *)
  let arsign = extract_arity_signature env tomatchs sign in
(*     (try List.iter *)
(*       (fun arsign -> *)
(* 	 trace (str "arity signature: " ++ my_print_rel_context env arsign)) *)
(*       arsign; *)
(*     with _ -> trace (str "error in arity signature printing")); *)
  let env = List.fold_right push_rels arsign env in
  let allnames = List.rev (List.map (List.map pi1) arsign) in
    match rtntyp with
      | Some rtntyp ->
	  let predcclj = typing_fun (mk_tycon (new_Type ())) env rtntyp in
	  let predccl = (j_nf_isevar !isevars predcclj).uj_val in      
	    Some (build_initial_predicate true allnames predccl)
      | None -> 
	  match valcon_of_tycon tycon with
	    | Some ty -> 
		let names,pred = 
		  oldprepare_predicate_from_tycon loc false env isevars tomatchs sign ty
		in Some (build_initial_predicate true names pred)
	    | None -> None
  
let lift_ctx n ctx = 
  let ctx', _ =
    List.fold_right (fun (c, t) (ctx, n') -> (liftn n n' c, liftn_tomatch_type n n' t) :: ctx, succ n') ctx ([], 0)
  in ctx'

(* Turn matched terms into variables. *)
let abstract_tomatch env tomatchs =
  let prev, ctx, names = 
    List.fold_left
      (fun (prev, ctx, names) (c, t) ->
	 let lenctx =  List.length ctx in
	 match kind_of_term c with
	     Rel n -> (lift lenctx c, lift_tomatch_type lenctx t) :: prev, ctx, names
	   | _ -> 
	       let name = next_ident_away_from (id_of_string "filtered_var") names in
		 (mkRel 1, lift_tomatch_type 1 t) :: lift_ctx 1 prev, 
	       (Name name, Some (lift lenctx c), lift lenctx $ type_of_tomatch t) :: ctx, 
	       name :: names)
      ([], [], []) tomatchs
  in List.rev prev, ctx
    
let is_dependent_ind = function
    IsInd (_, IndType (indf, args)) when List.length args > 0 -> true
  | _ -> false

let build_dependent_signature env evars avoid tomatchs arsign =
  let avoid = ref avoid in
  let arsign = List.rev arsign in
  let allnames = List.rev (List.map (List.map pi1) arsign) in
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
	     IsInd (ty, IndType (indf, args)) when List.length args > 0 ->
	       (* Build the arity signature following the names in matched terms as much as possible *)
	       let argsign = List.tl arsign in (* arguments in inverse application order *)
	       let (appn, appb, appt) as _appsign = List.hd arsign in (* The matched argument *)
(* 	       let _ = trace (str "Working on dependent arg: " ++ my_print_rel_context *)
(* 				(push_rel_context argsign env) [_appsign]) *)
(* 	       in *)
	       let argsign = List.rev argsign in (* arguments in application order *)
	       let env', nargeqs, argeqs, refl_args, slift, argsign' =
		 List.fold_left2
		   (fun (env, nargeqs, argeqs, refl_args, slift, argsign') arg (name, b, t) ->
(* 		      trace (str "Matching indexes: " ++ my_print_constr env arg ++ *)
(* 			       str " and " ++ my_print_rel_context env [(name,b,t)]); *)
		      let argt = Retyping.get_type_of env evars arg in
		      let eq, refl_arg = 
			if Reductionops.is_conv env evars argt t then
			  (mk_eq (lift (nargeqs + slift) argt)
			     (mkRel (nargeqs + slift))
			     (lift (nargeqs + nar) arg),
			   mk_eq_refl argt arg)
			else
			  (mk_JMeq (lift (nargeqs + slift) appt)
			     (mkRel (nargeqs + slift))
			     (lift (nargeqs + nar) argt)
			     (lift (nargeqs + nar) arg),
			   mk_JMeq_refl argt arg)
		      in
		      let previd, id = 
			let name = 
			  match kind_of_term arg with 
			      Rel n -> pi1 (lookup_rel n (rel_context env))
			    | _ -> name
			in
			  make_prime avoid name 
		      in
			(env, succ nargeqs, 
			 (Name (eq_id avoid previd), None, eq) :: argeqs, 
			 refl_arg :: refl_args,
			 pred slift,
			 (Name id, b, t) :: argsign'))
		   (env, 0, [], [], slift, []) args argsign
	       in
(* 		 trace (str "neqs: " ++ int neqs ++ spc () ++ *)
(* 			  str "nargeqs: " ++ int nargeqs ++spc () ++ *)
(* 			  str "slift: " ++ int slift ++spc () ++ *)
(* 			  str "nar: " ++ int nar); *)
	       let eq = mk_JMeq 
		 (lift (nargeqs + slift) appt)
		 (mkRel (nargeqs + slift))
		 (lift (nargeqs + nar) ty) 
		 (lift (nargeqs + nar) tm) 
	       in
	       let refl_eq = mk_JMeq_refl ty tm in
	       let previd, id = make_prime avoid appn in
		 (((Name (eq_id avoid previd), None, eq) :: argeqs) :: eqs, 
		 succ nargeqs, 
		 refl_eq :: refl_args,
		 pred slift, 
		 (((Name id, appb, appt) :: argsign') :: arsigns))
		   
	   | _ -> 
	       (* Non dependent inductive or not inductive, just use a regular equality *)
	       let (name, b, typ) = match arsign with [x] -> x | _ -> assert(false) in
	       let previd, id = make_prime avoid name in
	       let arsign' = (Name id, b, typ) in
(* 	       let _ = trace (str "Working on arg: " ++ my_print_rel_context *)
(* 				env [arsign']) *)
(* 	       in *)
	       let tomatch_ty = type_of_tomatch ty in
	       let eq = 
		 mk_eq (lift nar tomatch_ty)
		   (mkRel slift) (lift nar tm)
(* 		 mk_eq (lift (neqs + nar) tomatch_ty)  *)
(* 		   (mkRel (neqs + slift)) (lift (neqs + nar) tm)  *)
	       in
		 ([(Name (eq_id avoid previd), None, eq)] :: eqs, succ neqs, 
		  (mk_eq_refl tomatch_ty tm) :: refl_args,
		  pred slift, (arsign' :: []) :: arsigns))
      ([], 0, [], nar, []) tomatchs arsign
  in 
  let arsign'' = List.rev arsign' in
    assert(slift = 0); (* we must have folded over all elements of the arity signature *)
(*     begin try  *)
(*       List.iter  *)
(* 	(fun arsign -> *)
(* 	   trace (str "old arity signature: " ++ my_print_rel_context env arsign)) *)
(* 	arsign; *)
      List.iter
	(fun c ->
	   trace (str "new arity signature: " ++ my_print_rel_context env c))
	(arsign'');
(*     with _ -> trace (str "error in arity signature printing") *)
(*     end; *)
    let env' = push_rel_context (context_of_arsign arsign') env in
    let _eqsenv = push_rel_context (context_of_arsign eqs) env' in
      (try trace (str "Where env with eqs is: " ++ my_print_env _eqsenv);
	 trace (str "args: " ++ List.fold_left (fun acc x -> acc ++ my_print_constr env x)
		  (mt()) refls)
       with _ -> trace (str "error in equalities signature printing"));
      arsign'', allnames, nar, eqs, neqs, refls
      
(* 	       let len = List.length eqs in *)
(* 		 it_mkProd_wo_LetIn (lift (nar + len) pred) eqs, pred, len *)


(**************************************************************************)
(* Main entry of the matching compilation                                 *)
  
let liftn_rel_context n k sign =  
  let rec liftrec k = function
    | (na,c,t)::sign ->
	(na,Option.map (liftn n k) c,liftn n k t)::(liftrec (k-1) sign)
    | [] -> []
  in
    liftrec (k + rel_context_length sign) sign

let nf_evars_env evar_defs (env : env) : env = 
  let nf t = nf_isevar evar_defs t in
  let env0 : env = reset_context env in 
  let f e (na, b, t) e' : env =
    Environ.push_named (na, Option.map nf b, nf t) e'
  in
  let env' = Environ.fold_named_context f ~init:env0 env in
    Environ.fold_rel_context (fun e (na, b, t) e' -> Environ.push_rel (na, Option.map nf b, nf t) e')
     ~init:env' env
      
let compile_cases loc style (typing_fun, isevars) (tycon : Evarutil.type_constraint) env (predopt, tomatchl, eqns) =
  (* We build the matrix of patterns and right-hand-side *)
  let matx = matx_of_eqns env eqns in
     
  (* We build the vector of terms to match consistently with the *)
  (* constructors found in patterns *)
  let tomatchs = coerce_to_indtype typing_fun isevars env matx tomatchl in
(*   isevars := nf_evar_defs !isevars; *)
(*   let env = nf_evars_env !isevars (env : env) in *)
(*      trace (str "Evars : " ++ my_print_evardefs !isevars); *)
(*     trace (str "Env : " ++ my_print_env env); *)
  let _isdep = List.exists (fun (x, y) -> is_dependent_ind y) tomatchs in
    if predopt = None then
      let tomatchs, tomatchs_lets = abstract_tomatch env tomatchs in
      let tomatchs_len = List.length tomatchs_lets in
      let tycon = lift_tycon tomatchs_len tycon in
      let env = push_rel_context tomatchs_lets env in
      let len = List.length eqns in 
      let sign, allnames, signlen, eqs, neqs, args = 
	(* The arity signature *)
	let arsign = extract_arity_signatures env tomatchs (List.map snd tomatchl) in
	  (* Build the dependent arity signature, the equalities which makes
	     the first part of the predicate and their instantiations. *)
	  trace (str "Arity signatures : " ++ my_print_rel_context env (context_of_arsign arsign));
	let avoid = [] in
	  build_dependent_signature env (Evd.evars_of !isevars) avoid tomatchs arsign

      in
      let tycon_constr = 
	match valcon_of_tycon tycon with
	  | None -> mkExistential env isevars 
	  | Some t -> t
      in
      let lets, matx = 
	(* Type the rhs under the assumption of equations *)
	constrs_of_pats typing_fun tycon env isevars matx tomatchs sign neqs 
	  (eqs : rel_context list) (lift (signlen + neqs) tycon_constr) in
	
      let matx = List.rev matx in
      let _ = assert(len = List.length lets) in
      let env = push_rels lets env in
      let matx = List.map (fun eqn -> { eqn with rhs = { eqn.rhs with rhs_env = env } }) matx in
      let tomatchs = List.map (fun (x, y) -> lift len x, lift_tomatch_type len y) tomatchs in
      let args = List.rev_map (lift len) args in
      let sign = List.map (lift_rel_context len) sign in	
      let pred = it_mkProd_wo_LetIn (lift (signlen + neqs) tycon_constr) 
	(context_of_arsign eqs) in

      let pred = liftn len (succ signlen) pred in
(* 	it_mkProd_wo_LetIn (lift (len + signlen + neqs) tycon_constr) (liftn_rel_context len signlen eqs) in*) 
      (* We build the elimination predicate if any and check its consistency *)
      (* with the type of arguments to match *)
      let _signenv = List.fold_right push_rels sign env in
(* 	trace (str "Using predicate: " ++ my_print_constr signenv pred ++ str " in env: " ++ my_print_env signenv ++ str " len is " ++ int len); *)

      let pred =
	(* prepare_predicate_from_tycon loc typing_fun isevars env tomatchs eqs allnames signlen sign tycon in *)
	build_initial_predicate true allnames pred in
	(* We push the initial terms to match and push their alias to rhs' envs *)
	(* names of aliases will be recovered from patterns (hence Anonymous here) *)
      let initial_pushed = List.map (fun tm -> Pushed (tm,[])) tomatchs in
	
      let pb =
	{ env      = env;
	  isevars  = isevars;
	  pred     = Some pred;
	  tomatch  = initial_pushed;
	  history  = start_history (List.length initial_pushed);
	  mat      = matx;
	  caseloc  = loc;
	  casestyle= style;
	  typing_function = typing_fun } in
	
      let j = compile pb in
	(* We check for unused patterns *)
	List.iter (check_unused_pattern env) matx;
	let body = it_mkLambda_or_LetIn (applistc j.uj_val args) lets in
	let j = 
	  { uj_val = it_mkLambda_or_LetIn body tomatchs_lets;
	    uj_type = lift (-tomatchs_len) (nf_isevar !isevars tycon_constr); }
	in j
(* 	  inh_conv_coerce_to_tycon loc env isevars j tycon0 *)
    else
      (* We build the elimination predicate if any and check its consistency *)
      (* with the type of arguments to match *)
      let tmsign = List.map snd tomatchl in
      let pred = prepare_predicate_from_rettyp loc typing_fun isevars env tomatchs tmsign tycon predopt in
	
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
	      casestyle= style;
	      typing_function = typing_fun } in
	    
	  let j = compile pb in
	  (* We check for unused patterns *)
	  List.iter (check_unused_pattern env) matx;
	    inh_conv_coerce_to_tycon loc env isevars j tycon	  

end
  
