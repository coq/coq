(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Nameops
open Namegen
open Term
open Termops
open Indtypes
open Environ
open Pretype_errors
open Type_errors
open Typeclasses_errors
open Indrec
open Cases
open Logic
open Printer
open Evd

(* This simplifies the typing context of Cases clauses *)
(* hope it does not disturb other typing contexts *)
let contract env lc =
  let l = ref [] in
  let contract_context (na,c,t) env =
    match c with
      | Some c' when isRel c' ->
          l := (Vars.substl !l c') :: !l;
          env
      | _ ->
          let t' = Vars.substl !l t in
          let c' = Option.map (Vars.substl !l) c in
          let na' = named_hd env t' na in
          l := (mkRel 1) :: List.map (Vars.lift 1) !l;
          push_rel (na',c',t') env in
  let env = process_rel_context contract_context env in
  (env, List.map (Vars.substl !l) lc)

let contract2 env a b = match contract env [a;b] with
  | env, [a;b] -> env,a,b | _ -> assert false

let contract3 env a b c = match contract env [a;b;c] with
  | env, [a;b;c] -> env,a,b,c | _ -> assert false

let contract4 env a b c d = match contract env [a;b;c;d] with
  | env, [a;b;c;d] -> (env,a,b,c),d | _ -> assert false

let contract1_vect env a v =
  match contract env (a :: Array.to_list v) with
  | env, a::l -> env,a,Array.of_list l
  | _ -> assert false

let rec contract3' env a b c = function
  | OccurCheck (evk,d) -> let x,d = contract4 env a b c d in x,OccurCheck(evk,d)
  | NotClean ((evk,args),env',d) ->
      let env',d,args = contract1_vect env' d args in
      contract3 env a b c,NotClean((evk,args),env',d)
  | ConversionFailed (env',t1,t2) ->
      let (env',t1,t2) = contract2 env' t1 t2 in
      contract3 env a b c, ConversionFailed (env',t1,t2)
  | NotSameArgSize | NotSameHead | NoCanonicalStructure
  | MetaOccurInBody _ | InstanceNotSameType _
  | UnifUnivInconsistency _ as x -> contract3 env a b c, x
  | CannotSolveConstraint ((pb,env,t,u),x) ->
      let env,t,u = contract2 env t u in
      let y,x = contract3' env a b c x in
      y,CannotSolveConstraint ((pb,env,t,u),x)

(** Printers *)

let pr_lconstr c = quote (pr_lconstr c)
let pr_lconstr_env e s c = quote (pr_lconstr_env e s c)
let pr_ljudge_env e s c = let v,t = pr_ljudge_env e s c in (quote v,quote t)

(** A canonisation procedure for constr such that comparing there
    externalisation catches more equalities *)
let canonize_constr c =
  (* replaces all the names in binders by [dn] ("default name"),
     ensures that [alpha]-equivalent terms will have the same
     externalisation. *)
  let dn = Name.Anonymous in
  let rec canonize_binders c =
    match Term.kind_of_term c with
    | Prod (_,t,b) -> mkProd(dn,t,b)
    | Lambda (_,t,b) -> mkLambda(dn,t,b)
    | LetIn (_,u,t,b) -> mkLetIn(dn,u,t,b)
    | _ -> Term.map_constr canonize_binders c
  in
  canonize_binders c

(** Tries to realize when the two terms, albeit different are printed the same. *)
let display_eq ~flags env sigma t1 t2 =
  (* terms are canonized, then their externalisation is compared syntactically *)
  let open Constrextern in
  let t1 = canonize_constr t1 in
  let t2 = canonize_constr t2 in
  let ct1 = Flags.with_options flags (fun () -> extern_constr false env sigma t1) () in
  let ct2 = Flags.with_options flags (fun () -> extern_constr false env sigma t2) () in
  Constrexpr_ops.constr_expr_eq ct1 ct2

(** This function adds some explicit printing flags if the two arguments are
    printed alike. *)
let rec pr_explicit_aux env sigma t1 t2 = function
| [] ->
  (** no specified flags: default. *)
  (quote (Printer.pr_lconstr_env env sigma t1), quote (Printer.pr_lconstr_env env sigma t2))
| flags :: rem ->
  let equal = display_eq ~flags env sigma t1 t2 in
  if equal then
    (** The two terms are the same from the user point of view *)
    pr_explicit_aux env sigma t1 t2 rem
  else
    let open Constrextern in
    let ct1 = Flags.with_options flags (fun () -> extern_constr false env sigma t1) ()
    in
    let ct2 = Flags.with_options flags (fun () -> extern_constr false env sigma t2) ()
    in
    quote (Ppconstr.pr_lconstr_expr ct1), quote (Ppconstr.pr_lconstr_expr ct2)

let explicit_flags =
  let open Constrextern in
  [ []; (** First, try with the current flags *)
    [print_implicits]; (** Then with implicit *)
    [print_universes]; (** Then with universes *)
    [print_universes; print_implicits]; (** With universes AND implicits *)
    [print_implicits; print_coercions; print_no_symbol]; (** Then more! *)
    [print_universes; print_implicits; print_coercions; print_no_symbol] (** and more! *) ]

let pr_explicit env sigma t1 t2 = pr_explicit_aux env sigma t1 t2 explicit_flags

let pr_db env i =
  try
    match lookup_rel i env with
        Name id, _, _ -> pr_id id
      | Anonymous, _, _ -> str "<>"
  with Not_found -> str "UNBOUND_REL_" ++ int i

let explain_unbound_rel env sigma n =
  let pe = pr_ne_context_of (str "In environment") env sigma in
  str "Unbound reference: " ++ pe ++
  str "The reference " ++ int n ++ str " is free."

let explain_unbound_var env v =
  let var = pr_id v in
  str "No such section variable or assumption: " ++ var ++ str "."

let explain_not_type env sigma j =
  let j = Evarutil.j_nf_evar sigma j in
  let pe = pr_ne_context_of (str "In environment") env sigma in
  let pc,pt = pr_ljudge_env env sigma j in
  pe ++ str "The term" ++ brk(1,1) ++ pc ++ spc () ++
  str "has type" ++ spc () ++ pt ++ spc () ++
  str "which should be Set, Prop or Type."

let explain_bad_assumption env sigma j =
  let pe = pr_ne_context_of (str "In environment") env sigma in
  let pc,pt = pr_ljudge_env env sigma j in
  pe ++ str "Cannot declare a variable or hypothesis over the term" ++
  brk(1,1) ++ pc ++ spc () ++ str "of type" ++ spc () ++ pt ++ spc () ++
  str "because this term is not a type."

let explain_reference_variables id c =
  (* c is intended to be a global reference *)
  let pc = pr_global (Globnames.global_of_constr c) in
  pc ++ strbrk " depends on the variable " ++ pr_id id ++
  strbrk " which is not declared in the context."

let rec pr_disjunction pr = function
  | [a] -> pr  a
  | [a;b] -> pr a ++ str " or" ++ spc () ++ pr b
  | a::l -> pr a ++ str "," ++ spc () ++ pr_disjunction pr l
  | [] -> assert false

let pr_puniverses f env (c,u) = 
  f env c ++ 
  (if Flags.is_universe_polymorphism () && not (Univ.Instance.is_empty u) then
    str"(*" ++ Univ.Instance.pr Universes.pr_with_global_universes u ++ str"*)"
  else mt())

let explain_elim_arity env sigma ind sorts c pj okinds =
  let env = make_all_name_different env in
  let pi = pr_inductive env (fst ind) in
  let pc = pr_lconstr_env env sigma c in
  let msg = match okinds with
  | Some(kp,ki,explanation) ->
      let pki = pr_sort_family ki in
      let pkp = pr_sort_family kp in
      let explanation =	match explanation with
	| NonInformativeToInformative ->
          "proofs can be eliminated only to build proofs"
	| StrongEliminationOnNonSmallType ->
          "strong elimination on non-small inductive types leads to paradoxes"
	| WrongArity ->
	  "wrong arity" in
      let ppar = pr_disjunction (fun s -> quote (pr_sort_family s)) sorts in
      let ppt = pr_lconstr_env env sigma ((strip_prod_assum pj.uj_type)) in
      hov 0
	(str "the return type has sort" ++ spc () ++ ppt ++ spc () ++
	 str "while it" ++ spc () ++ str "should be " ++ ppar ++ str ".") ++
      fnl () ++
      hov 0
	(str "Elimination of an inductive object of sort " ++
	 pki ++ brk(1,0) ++
         str "is not allowed on a predicate in sort " ++ pkp ++ fnl () ++
         str "because" ++ spc () ++ str explanation ++ str ".")
  | None ->
      str "ill-formed elimination predicate."
  in
  hov 0 (
    str "Incorrect elimination of" ++ spc () ++ pc ++ spc () ++
    str "in the inductive type" ++ spc () ++ quote pi ++ str ":") ++
  fnl () ++ msg

let explain_case_not_inductive env sigma cj =
  let cj = Evarutil.j_nf_evar sigma cj in
  let env = make_all_name_different env in
  let pc = pr_lconstr_env env sigma cj.uj_val in
  let pct = pr_lconstr_env env sigma cj.uj_type in
    match kind_of_term cj.uj_type with
      | Evar _ ->
	  str "Cannot infer a type for this expression."
      | _ ->
	  str "The term" ++ brk(1,1) ++ pc ++ spc () ++
	  str "has type" ++ brk(1,1) ++ pct ++ spc () ++
	  str "which is not a (co-)inductive type."

let explain_number_branches env sigma cj expn =
  let cj = Evarutil.j_nf_evar sigma cj in
  let env = make_all_name_different env in
  let pc = pr_lconstr_env env sigma cj.uj_val in
  let pct = pr_lconstr_env env sigma cj.uj_type in
  str "Matching on term" ++ brk(1,1) ++ pc ++ spc () ++
  str "of type" ++ brk(1,1) ++ pct ++ spc () ++
  str "expects " ++  int expn ++ str " branches."

let explain_ill_formed_branch env sigma c ci actty expty =
  let simp t = Reduction.nf_betaiota env (Evarutil.nf_evar sigma t) in
  let c = Evarutil.nf_evar sigma c in
  let env = make_all_name_different env in
  let pc = pr_lconstr_env env sigma c in
  let pa, pe = pr_explicit env sigma (simp actty) (simp expty) in
  strbrk "In pattern-matching on term" ++ brk(1,1) ++ pc ++
  spc () ++ strbrk "the branch for constructor" ++ spc () ++
  quote (pr_puniverses pr_constructor env ci) ++
  spc () ++ str "has type" ++ brk(1,1) ++ pa ++ spc () ++
  str "which should be" ++ brk(1,1) ++ pe ++ str "."

let explain_generalization env sigma (name,var) j =
  let pe = pr_ne_context_of (str "In environment") env sigma in
  let pv = pr_ltype_env env sigma var in
  let (pc,pt) = pr_ljudge_env (push_rel_assum (name,var) env) sigma j in
  pe ++ str "Cannot generalize" ++ brk(1,1) ++ pv ++ spc () ++
  str "over" ++ brk(1,1) ++ pc ++ str "," ++ spc () ++
  str "it has type" ++ spc () ++ pt ++
  spc () ++ str "which should be Set, Prop or Type."

let rec explain_unification_error env sigma p1 p2 = function
  | None -> mt()
  | Some e ->
     let rec aux p1 p2 = function
     | OccurCheck (evk,rhs) ->
        let rhs = Evarutil.nf_evar sigma rhs in
        [str "cannot define " ++ quote (pr_existential_key sigma evk) ++
	strbrk " with term " ++ pr_lconstr_env env sigma rhs ++
        strbrk " that would depend on itself"]
     | NotClean ((evk,args),env,c) ->
        let c = Evarutil.nf_evar sigma c in
        let args = Array.map (Evarutil.nf_evar sigma) args in
        [str "cannot instantiate " ++ quote (pr_existential_key sigma evk)
        ++ strbrk " because " ++ pr_lconstr_env env sigma c ++
	strbrk " is not in its scope" ++
        (if Array.is_empty args then mt() else
         strbrk ": available arguments are " ++
         pr_sequence (pr_lconstr_env env sigma) (List.rev (Array.to_list args)))]
     | NotSameArgSize | NotSameHead | NoCanonicalStructure ->
        (* Error speaks from itself *) []
     | ConversionFailed (env,t1,t2) ->
        if Term.eq_constr t1 p1 && Term.eq_constr t2 p2 then [] else
        let env = make_all_name_different env in
        let t1 = Evarutil.nf_evar sigma t1 in
        let t2 = Evarutil.nf_evar sigma t2 in
        if not (Term.eq_constr t1 p1) || not (Term.eq_constr t2 p2) then
          let t1, t2 = pr_explicit env sigma t1 t2 in
          [str "cannot unify " ++ t1 ++ strbrk " and " ++ t2]
        else []
     | MetaOccurInBody evk ->
        [str "instance for " ++ quote (pr_existential_key sigma evk) ++
	strbrk " refers to a metavariable - please report your example"]
     | InstanceNotSameType (evk,env,t,u) ->
        let t, u = pr_explicit env sigma t u in
        [str "unable to find a well-typed instantiation for " ++
        quote (pr_existential_key sigma evk) ++
        strbrk ": cannot ensure that " ++
        t ++ strbrk " is a subtype of " ++ u]
     | UnifUnivInconsistency p ->
        if !Constrextern.print_universes then
	  [str "universe inconsistency: " ++
          Univ.explain_universe_inconsistency Universes.pr_with_global_universes p]
	else
          [str "universe inconsistency"]
     | CannotSolveConstraint ((pb,env,t,u),e) ->
        let t = Evarutil.nf_evar sigma t in
        let u = Evarutil.nf_evar sigma u in
        (strbrk "cannot satisfy constraint " ++ pr_lconstr_env env sigma t ++
        str " == " ++ pr_lconstr_env env sigma u)
        :: aux t u e
     in
     match aux p1 p2 e with
     | [] -> mt ()
     | l -> spc () ++ str "(" ++
            prlist_with_sep pr_semicolon (fun x -> x) l ++ str ")"

let explain_actual_type env sigma j t reason =
  let env = make_all_name_different env in
  let j = Evarutil.j_nf_betaiotaevar sigma j in
  let t = Reductionops.nf_betaiota sigma t in
  (** Actually print *)
  let pe = pr_ne_context_of (str "In environment") env sigma in
  let pc = pr_lconstr_env env sigma (Environ.j_val j) in
  let (pt, pct) = pr_explicit env sigma t (Environ.j_type j) in
  let ppreason = explain_unification_error env sigma j.uj_type t reason in
  pe ++
  hov 0 (
  str "The term" ++ brk(1,1) ++ pc ++ spc () ++
  str "has type" ++ brk(1,1) ++ pct ++ spc () ++
  str "while it is expected to have type" ++ brk(1,1) ++ pt ++
  ppreason ++ str ".")

let explain_cant_apply_bad_type env sigma (n,exptyp,actualtyp) rator randl =
  let randl = Evarutil.jv_nf_betaiotaevar sigma randl in
  let exptyp = Evarutil.nf_evar sigma exptyp in
  let actualtyp = Reductionops.nf_betaiota sigma actualtyp in
  let rator = Evarutil.j_nf_evar sigma rator in
  let env = make_all_name_different env in
  let actualtyp, exptyp = pr_explicit env sigma actualtyp exptyp in
  let nargs = Array.length randl in
(*  let pe = pr_ne_context_of (str "in environment") env sigma in*)
  let pr,prt = pr_ljudge_env env sigma rator in
  let term_string1 = str (String.plural nargs "term") in
  let term_string2 =
    if nargs>1 then str "The " ++ pr_nth n ++ str " term" else str "This term"
  in
  let appl = prvect_with_sep fnl
	       (fun c ->
		  let pc,pct = pr_ljudge_env env sigma c in
		  hov 2 (pc ++ spc () ++ str ": " ++ pct)) randl
  in
  str "Illegal application: " ++ (* pe ++ *) fnl () ++
  str "The term" ++ brk(1,1) ++ pr ++ spc () ++
  str "of type" ++ brk(1,1) ++ prt ++ spc () ++
  str "cannot be applied to the " ++ term_string1 ++ fnl () ++
  str " " ++ v 0 appl ++ fnl () ++ term_string2 ++ str " has type" ++
  brk(1,1) ++ actualtyp ++ spc () ++
  str "which should be coercible to" ++ brk(1,1) ++
  exptyp ++ str "."

let explain_cant_apply_not_functional env sigma rator randl =
  let randl = Evarutil.jv_nf_evar sigma randl in
  let rator = Evarutil.j_nf_evar sigma rator in
  let env = make_all_name_different env in
  let nargs = Array.length randl in
(*  let pe = pr_ne_context_of (str "in environment") env sigma in*)
  let pr = pr_lconstr_env env sigma rator.uj_val in
  let prt = pr_lconstr_env env sigma rator.uj_type in
  let appl = prvect_with_sep fnl
	       (fun c ->
		  let pc = pr_lconstr_env env sigma c.uj_val in
		  let pct = pr_lconstr_env env sigma c.uj_type in
		  hov 2 (pc ++ spc () ++ str ": " ++ pct)) randl
  in
  str "Illegal application (Non-functional construction): " ++
  (* pe ++ *) fnl () ++
  str "The expression" ++ brk(1,1) ++ pr ++ spc () ++
  str "of type" ++ brk(1,1) ++ prt ++ spc () ++
  str "cannot be applied to the " ++ str (String.plural nargs "term") ++
  fnl () ++ str " " ++ v 0 appl

let explain_unexpected_type env sigma actual_type expected_type =
  let actual_type = Evarutil.nf_evar sigma actual_type in
  let expected_type = Evarutil.nf_evar sigma expected_type in
  let pract, prexp = pr_explicit env sigma actual_type expected_type in
  str "Found type" ++ spc () ++ pract ++ spc () ++
  str "where" ++ spc () ++ prexp ++ str " was expected."

let explain_not_product env sigma c =
  let c = Evarutil.nf_evar sigma c in
  let pr = pr_lconstr_env env sigma c in
  str "The type of this term is a product" ++ spc () ++
  str "while it is expected to be" ++
  (if is_Type c then str " a sort" else (brk(1,1) ++ pr)) ++ str "."

(* TODO: use the names *)
(* (co)fixpoints *)
let explain_ill_formed_rec_body env sigma err names i fixenv vdefj =
  let prt_name i =
    match names.(i) with
        Name id -> str "Recursive definition of " ++ pr_id id
      | Anonymous -> str "The " ++ pr_nth i ++ str " definition" in

  let st = match err with

  (* Fixpoint guard errors *)
  | NotEnoughAbstractionInFixBody ->
      str "Not enough abstractions in the definition"
  | RecursionNotOnInductiveType c ->
      str "Recursive definition on" ++ spc () ++ pr_lconstr_env env sigma c ++
      spc () ++ str "which should be an inductive type"
  | RecursionOnIllegalTerm(j,(arg_env, arg),le,lt) ->
      let arg_env = make_all_name_different arg_env in
      let called =
        match names.(j) with
            Name id -> pr_id id
          | Anonymous -> str "the " ++ pr_nth i ++ str " definition" in
      let pr_db x = quote (pr_db env x) in
      let vars =
        match (lt,le) with
            ([],[]) -> assert false
          | ([],[x]) -> str "a subterm of " ++ pr_db x
          | ([],_) -> str "a subterm of the following variables: " ++
              pr_sequence pr_db le
          | ([x],_) -> pr_db x
          | _ ->
              str "one of the following variables: " ++
              pr_sequence pr_db lt in
      str "Recursive call to " ++ called ++ spc () ++
      strbrk "has principal argument equal to" ++ spc () ++
      pr_lconstr_env arg_env sigma arg ++ strbrk " instead of " ++ vars

  | NotEnoughArgumentsForFixCall j ->
      let called =
        match names.(j) with
            Name id -> pr_id id
          | Anonymous -> str "the " ++ pr_nth i ++ str " definition" in
     str "Recursive call to " ++ called ++ str " has not enough arguments"

  (* CoFixpoint guard errors *)
  | CodomainNotInductiveType c ->
      str "The codomain is" ++ spc () ++ pr_lconstr_env env sigma c ++ spc () ++
      str "which should be a coinductive type"
  | NestedRecursiveOccurrences ->
      str "Nested recursive occurrences"
  | UnguardedRecursiveCall c ->
      str "Unguarded recursive call in" ++ spc () ++ pr_lconstr_env env sigma c
  | RecCallInTypeOfAbstraction c ->
      str "Recursive call forbidden in the domain of an abstraction:" ++
      spc () ++ pr_lconstr_env env sigma c
  | RecCallInNonRecArgOfConstructor c ->
      str "Recursive call on a non-recursive argument of constructor" ++
      spc () ++ pr_lconstr_env env sigma c
  | RecCallInTypeOfDef c ->
      str "Recursive call forbidden in the type of a recursive definition" ++
      spc () ++ pr_lconstr_env env sigma c
  | RecCallInCaseFun c ->
      str "Invalid recursive call in a branch of" ++
      spc () ++ pr_lconstr_env env sigma c
  | RecCallInCaseArg c ->
      str "Invalid recursive call in the argument of \"match\" in" ++ spc () ++
      pr_lconstr_env env sigma c
  | RecCallInCasePred c ->
      str "Invalid recursive call in the \"return\" clause of \"match\" in" ++
      spc () ++ pr_lconstr_env env sigma c
  | NotGuardedForm c ->
      str "Sub-expression " ++ pr_lconstr_env env sigma c ++
      strbrk " not in guarded form (should be a constructor," ++
      strbrk " an abstraction, a match, a cofix or a recursive call)"
  | ReturnPredicateNotCoInductive c ->
     str "The return clause of the following pattern matching should be" ++
     strbrk " a coinductive type:" ++
     spc () ++ pr_lconstr_env env sigma c
  in
  prt_name i ++ str " is ill-formed." ++ fnl () ++
  pr_ne_context_of (str "In environment") env sigma ++
  st ++ str "." ++ fnl () ++
  (try (* May fail with unresolved globals. *)
      let fixenv = make_all_name_different fixenv in
      let pvd = pr_lconstr_env fixenv sigma vdefj.(i).uj_val in
	str"Recursive definition is:" ++ spc () ++ pvd ++ str "."
    with e when Errors.noncritical e -> mt ())

let explain_ill_typed_rec_body env sigma i names vdefj vargs =
  let vdefj = Evarutil.jv_nf_evar sigma vdefj in
  let vargs = Array.map (Evarutil.nf_evar sigma) vargs in
  let env = make_all_name_different env in
  let pvd = pr_lconstr_env env sigma vdefj.(i).uj_val in
  let pvdt, pv = pr_explicit env sigma vdefj.(i).uj_type vargs.(i) in
  str "The " ++
  (match vdefj with [|_|] -> mt () | _ -> pr_nth (i+1) ++ spc ()) ++
  str "recursive definition" ++ spc () ++ pvd ++ spc () ++
  str "has type" ++ spc () ++ pvdt ++ spc () ++
  str "while it should be" ++ spc () ++ pv ++ str "."

let explain_cant_find_case_type env sigma c =
  let c = Evarutil.nf_evar sigma c in
  let env = make_all_name_different env in
  let pe = pr_lconstr_env env sigma c in
  str "Cannot infer type of pattern-matching on" ++ ws 1 ++ pe ++ str "."

let explain_occur_check env sigma ev rhs =
  let rhs = Evarutil.nf_evar sigma rhs in
  let env = make_all_name_different env in
  let pt = pr_lconstr_env env sigma rhs in
  str "Cannot define " ++ pr_existential_key sigma ev ++ str " with term" ++
  brk(1,1) ++ pt ++ spc () ++ str "that would depend on itself."

let pr_trailing_ne_context_of env sigma =
  if List.is_empty (Environ.rel_context env) &&
    List.is_empty (Environ.named_context env)
  then str "."
  else (str " in environment:"++ pr_context_unlimited env sigma)

let rec explain_evar_kind env sigma evk ty = function
  | Evar_kinds.QuestionMark _ ->
      strbrk "this placeholder of type " ++ ty
  | Evar_kinds.CasesType false ->
      strbrk "the type of this pattern-matching problem"
  | Evar_kinds.CasesType true ->
      strbrk "a subterm of type " ++ ty ++
      strbrk " in the type of this pattern-matching problem"
  | Evar_kinds.BinderType (Name id) ->
      strbrk "the type of " ++ Nameops.pr_id id
  | Evar_kinds.BinderType Anonymous ->
      strbrk "the type of this anonymous binder"
  | Evar_kinds.ImplicitArg (c,(n,ido),b) ->
      let id = Option.get ido in
      strbrk "the implicit parameter " ++ pr_id id ++ spc () ++ str "of" ++
      spc () ++ Nametab.pr_global_env Id.Set.empty c ++
      strbrk " whose type is " ++ ty
  | Evar_kinds.InternalHole -> strbrk "an internal placeholder of type " ++ ty
  | Evar_kinds.TomatchTypeParameter (tyi,n) ->
      strbrk "the " ++ pr_nth n ++
      strbrk " argument of the inductive type (" ++ pr_inductive env tyi ++
      strbrk ") of this term"
  | Evar_kinds.GoalEvar ->
      strbrk "an existential variable of type " ++ ty
  | Evar_kinds.ImpossibleCase ->
      strbrk "the type of an impossible pattern-matching clause"
  | Evar_kinds.MatchingVar _ ->
      assert false
  | Evar_kinds.VarInstance id ->
      strbrk "an instance of type " ++ ty ++
      str " for the variable " ++ pr_id id
  | Evar_kinds.SubEvar evk' ->
      let evi = Evd.find sigma evk' in
      let pc = match evi.evar_body with
      | Evar_defined c -> pr_lconstr_env env sigma (Evarutil.nf_evar sigma c)
      | Evar_empty -> assert false in
      let ty' = Evarutil.nf_evar sigma evi.evar_concl in
      pr_existential_key sigma evk ++ str " of type " ++ ty ++
      str " in the partial instance " ++ pc ++
      str " found for " ++ explain_evar_kind env sigma evk'
      (pr_lconstr_env env sigma ty') (snd evi.evar_source)

let explain_typeclass_resolution env sigma evi k =
  match Typeclasses.class_of_constr evi.evar_concl with
  | Some _ ->
    let env = Evd.evar_filtered_env evi in
      fnl () ++ str "Could not find an instance for " ++
      pr_lconstr_env env sigma evi.evar_concl ++
      pr_trailing_ne_context_of env sigma
  | _ -> mt()

let explain_placeholder_kind env sigma c e =
  match e with
  | Some (SeveralInstancesFound n) ->
      strbrk " (several distinct possible type class instances found)"
  | None ->
      match Typeclasses.class_of_constr c with
      | Some _ -> strbrk " (no type class instance found)"
      | _ -> mt ()

let explain_unsolvable_implicit env sigma evk explain =
  let evi = Evarutil.nf_evar_info sigma (Evd.find_undefined sigma evk) in
  let env = Evd.evar_filtered_env evi in
  let type_of_hole = pr_lconstr_env env sigma evi.evar_concl in
  let pe = pr_trailing_ne_context_of env sigma in
  strbrk "Cannot infer " ++
  explain_evar_kind env sigma evk type_of_hole (snd evi.evar_source) ++
  explain_placeholder_kind env sigma evi.evar_concl explain ++ pe

let explain_var_not_found env id =
  str "The variable" ++ spc () ++ pr_id id ++
  spc () ++ str "was not found" ++
  spc () ++ str "in the current" ++ spc () ++ str "environment" ++ str "."

let explain_wrong_case_info env (ind,u) ci =
  let pi = pr_inductive (Global.env()) ind in
  if eq_ind ci.ci_ind ind then
    str "Pattern-matching expression on an object of inductive type" ++
    spc () ++ pi ++ spc () ++ str "has invalid information."
  else
    let pc = pr_inductive (Global.env()) ci.ci_ind in
    str "A term of inductive type" ++ spc () ++ pi ++ spc () ++
    str "was given to a pattern-matching expression on the inductive type" ++
    spc () ++ pc ++ str "."

let explain_cannot_unify env sigma m n e =
  let env = make_all_name_different env in
  let m = Evarutil.nf_evar sigma m in
  let n = Evarutil.nf_evar sigma n in
  let pm, pn = pr_explicit env sigma m n in
  let ppreason = explain_unification_error env sigma m n e in
  let pe = pr_ne_context_of (str "In environment") env sigma in
  pe ++ str "Unable to unify" ++ brk(1,1) ++ pm ++ spc () ++
  str "with" ++ brk(1,1) ++ pn ++ ppreason ++ str "."

let explain_cannot_unify_local env sigma m n subn =
  let pm = pr_lconstr_env env sigma m in
  let pn = pr_lconstr_env env sigma n in
  let psubn = pr_lconstr_env env sigma subn in
    str "Unable to unify" ++ brk(1,1) ++ pm ++ spc () ++
      str "with" ++ brk(1,1) ++ pn ++ spc () ++ str "as" ++ brk(1,1) ++
      psubn ++ str " contains local variables."

let explain_refiner_cannot_generalize env sigma ty =
  str "Cannot find a well-typed generalisation of the goal with type: " ++
  pr_lconstr_env env sigma ty ++ str "."

let explain_no_occurrence_found env sigma c id =
  str "Found no subterm matching " ++ pr_lconstr_env env sigma c ++
  str " in " ++
    (match id with
      | Some id -> pr_id id
      | None -> str"the current goal") ++ str "."

let explain_cannot_unify_binding_type env sigma m n =
  let pm = pr_lconstr_env env sigma m in
  let pn = pr_lconstr_env env sigma n in
  str "This binding has type" ++ brk(1,1) ++ pm ++ spc () ++
  str "which should be unifiable with" ++ brk(1,1) ++ pn ++ str "."

let explain_cannot_find_well_typed_abstraction env sigma p l e =
  str "Abstracting over the " ++
  str (String.plural (List.length l) "term") ++ spc () ++
  hov 0 (pr_enum (pr_lconstr_env env sigma) l) ++ spc () ++
  str "leads to a term" ++ spc () ++ pr_lconstr_goal_style_env env sigma p ++
  spc () ++ str "which is ill-typed." ++
  (match e with None -> mt () | Some e -> fnl () ++ str "Reason is: " ++ e)

let explain_wrong_abstraction_type env sigma na abs expected result =
  let ppname = match na with Name id -> pr_id id ++ spc () | _ -> mt () in
  str "Cannot instantiate metavariable " ++ ppname ++ strbrk "of type " ++
  pr_lconstr_env env sigma expected ++ strbrk " with abstraction " ++
  pr_lconstr_env env sigma abs ++ strbrk " of incompatible type " ++
  pr_lconstr_env env sigma result ++ str "."

let explain_abstraction_over_meta _ m n =
  strbrk "Too complex unification problem: cannot find a solution for both " ++
  pr_name m ++ spc () ++ str "and " ++ pr_name n ++ str "."

let explain_non_linear_unification env sigma m t =
  strbrk "Cannot unambiguously instantiate " ++
  pr_name m ++ str ":" ++
  strbrk " which would require to abstract twice on " ++
  pr_lconstr_env env sigma t ++ str "."

let explain_unsatisfied_constraints env sigma cst =
  strbrk "Unsatisfied constraints: " ++ 
    Univ.pr_constraints (Evd.pr_evd_level sigma) cst ++ 
    spc () ++ str "(maybe a bugged tactic)."

let explain_type_error env sigma err =
  let env = make_all_name_different env in
  match err with
  | UnboundRel n ->
      explain_unbound_rel env sigma n
  | UnboundVar v ->
      explain_unbound_var env v
  | NotAType j ->
      explain_not_type env sigma j
  | BadAssumption c ->
      explain_bad_assumption env sigma c
  | ReferenceVariables (id,c) ->
      explain_reference_variables id c
  | ElimArity (ind, aritylst, c, pj, okinds) ->
      explain_elim_arity env sigma ind aritylst c pj okinds
  | CaseNotInductive cj ->
      explain_case_not_inductive env sigma cj
  | NumberBranches (cj, n) ->
      explain_number_branches env sigma cj n
  | IllFormedBranch (c, i, actty, expty) ->
      explain_ill_formed_branch env sigma c i actty expty
  | Generalization (nvar, c) ->
      explain_generalization env sigma nvar c
  | ActualType (j, pt) ->
      explain_actual_type env sigma j pt None
  | CantApplyBadType (t, rator, randl) ->
      explain_cant_apply_bad_type env sigma t rator randl
  | CantApplyNonFunctional (rator, randl) ->
      explain_cant_apply_not_functional env sigma rator randl
  | IllFormedRecBody (err, lna, i, fixenv, vdefj) ->
      explain_ill_formed_rec_body env sigma err lna i fixenv vdefj
  | IllTypedRecBody (i, lna, vdefj, vargs) ->
     explain_ill_typed_rec_body env sigma i lna vdefj vargs
  | WrongCaseInfo (ind,ci) ->
      explain_wrong_case_info env ind ci
  | UnsatisfiedConstraints cst ->
      explain_unsatisfied_constraints env sigma cst

let pr_position (cl,pos) =
  let clpos = match cl with
    | None -> str " of the goal"
    | Some (id,Locus.InHyp) -> str " of hypothesis " ++ pr_id id
    | Some (id,Locus.InHypTypeOnly) -> str " of the type of hypothesis " ++ pr_id id
    | Some (id,Locus.InHypValueOnly) -> str " of the body of hypothesis " ++ pr_id id in
  int pos ++ clpos

let explain_cannot_unify_occurrences env sigma nested ((cl2,pos2),t2) ((cl1,pos1),t1) e =
  if nested then
    str "Found nested occurrences of the pattern at positions " ++
    int pos1 ++ strbrk " and " ++ pr_position (cl2,pos2) ++ str "."
  else
    let ppreason = match e with None -> mt() | Some (c1,c2,e) -> explain_unification_error env sigma c1 c2 (Some e) in
    str "Found incompatible occurrences of the pattern" ++ str ":" ++
    spc () ++ str "Matched term " ++ pr_lconstr_env env sigma t2 ++
    strbrk " at position " ++ pr_position (cl2,pos2) ++
    strbrk " is not compatible with matched term " ++
    pr_lconstr_env env sigma t1 ++ strbrk " at position " ++
    pr_position (cl1,pos1) ++ ppreason ++ str "."

let pr_constraints printenv env sigma evars cstrs =
  let (ev, evi) = Evar.Map.choose evars in
    if Evar.Map.for_all (fun ev' evi' ->
      eq_named_context_val evi.evar_hyps evi'.evar_hyps) evars
    then
      let l = Evar.Map.bindings evars in
      let env' = reset_with_named_context evi.evar_hyps env in
      let pe =
        if printenv then
          pr_ne_context_of (str "In environment:") env' sigma
        else mt ()
      in
      let evs =
        prlist
        (fun (ev, evi) -> fnl () ++ pr_existential_key sigma ev ++
            str " : " ++ pr_lconstr_env env' sigma evi.evar_concl) l
      in
      h 0 (pe ++ evs ++ pr_evar_constraints cstrs)
    else
      let filter evk _ = Evar.Map.mem evk evars in
      pr_evar_map_filter ~with_univs:false filter sigma

let explain_unsatisfiable_constraints env sigma constr comp =
  let (_, constraints) = Evd.extract_all_conv_pbs sigma in
  let undef = Evd.undefined_map (Evarutil.nf_evar_map_undefined sigma) in
  (** Only keep evars that are subject to resolution and members of the given
     component. *)
  let is_kept evk evi = match comp with
  | None -> Typeclasses.is_resolvable evi
  | Some comp -> Typeclasses.is_resolvable evi && Evar.Set.mem evk comp
  in
  let undef = 
    let m = Evar.Map.filter is_kept undef in
      if Evar.Map.is_empty m then undef
      else m
  in
  match constr with
  | None ->
    str "Unable to satisfy the following constraints:" ++ fnl () ++
    pr_constraints true env sigma undef constraints
  | Some (ev, k) ->
    let cstr =
      let remaining = Evar.Map.remove ev undef in
      if not (Evar.Map.is_empty remaining) then
        str "With the following constraints:" ++ fnl () ++
          pr_constraints false env sigma remaining constraints
      else mt ()
    in
    let info = Evar.Map.find ev undef in
    explain_typeclass_resolution env sigma info k ++ fnl () ++ cstr

let explain_pretype_error env sigma err =
  let env = Evarutil.env_nf_betaiotaevar sigma env in
  let env = make_all_name_different env in
  match err with
  | CantFindCaseType c -> explain_cant_find_case_type env sigma c
  | ActualTypeNotCoercible (j,t,e) ->
    let {uj_val = c; uj_type = actty} = j in
    let (env, c, actty, expty), e = contract3' env c actty t e in
    let j = {uj_val = c; uj_type = actty} in
    explain_actual_type env sigma j t (Some e)
  | UnifOccurCheck (ev,rhs) -> explain_occur_check env sigma ev rhs
  | UnsolvableImplicit (evk,exp) -> explain_unsolvable_implicit env sigma evk exp
  | VarNotFound id -> explain_var_not_found env id
  | UnexpectedType (actual,expect) ->
    let env, actual, expect = contract2 env actual expect in
    explain_unexpected_type env sigma actual expect
  | NotProduct c -> explain_not_product env sigma c
  | CannotUnify (m,n,e) ->
    let env, m, n = contract2 env m n in
    explain_cannot_unify env sigma m n e
  | CannotUnifyLocal (m,n,sn) -> explain_cannot_unify_local env sigma m n sn
  | CannotGeneralize ty -> explain_refiner_cannot_generalize env sigma ty
  | NoOccurrenceFound (c, id) -> explain_no_occurrence_found env sigma c id
  | CannotUnifyBindingType (m,n) -> explain_cannot_unify_binding_type env sigma m n
  | CannotFindWellTypedAbstraction (p,l,e) ->
      explain_cannot_find_well_typed_abstraction env sigma p l
        (Option.map (fun (env',e) -> explain_type_error env' sigma e) e)
  | WrongAbstractionType (n,a,t,u) ->
      explain_wrong_abstraction_type env sigma n a t u
  | AbstractionOverMeta (m,n) -> explain_abstraction_over_meta env m n
  | NonLinearUnification (m,c) -> explain_non_linear_unification env sigma m c
  | TypingError t -> explain_type_error env sigma t
  | CannotUnifyOccurrences (b,c1,c2,e) -> explain_cannot_unify_occurrences env sigma b c1 c2 e
  | UnsatisfiableConstraints (c,comp) -> explain_unsatisfiable_constraints env sigma c comp
(* Module errors *)

open Modops

let explain_not_match_error = function
  | InductiveFieldExpected _ ->
    strbrk "an inductive definition is expected"
  | DefinitionFieldExpected ->
    strbrk "a definition is expected"
  | ModuleFieldExpected ->
    strbrk "a module is expected"
  | ModuleTypeFieldExpected ->
    strbrk "a module type is expected"
  | NotConvertibleInductiveField id | NotConvertibleConstructorField id ->
    str "types given to " ++ str (Id.to_string id) ++ str " differ"
  | NotConvertibleBodyField ->
    str "the body of definitions differs"
  | NotConvertibleTypeField (env, typ1, typ2) ->
    str "expected type" ++ spc ()  ++
    quote (Printer.safe_pr_lconstr_env env Evd.empty typ2) ++ spc () ++
    str "but found type" ++ spc () ++
    quote (Printer.safe_pr_lconstr_env env Evd.empty typ1)
  | NotSameConstructorNamesField ->
    str "constructor names differ"
  | NotSameInductiveNameInBlockField ->
    str "inductive types names differ"
  | FiniteInductiveFieldExpected isfinite ->
    str "type is expected to be " ++
    str (if isfinite then "coinductive" else "inductive")
  | InductiveNumbersFieldExpected n ->
    str "number of inductive types differs"
  | InductiveParamsNumberField n ->
    str "inductive type has not the right number of parameters"
  | RecordFieldExpected isrecord ->
    str "type is expected " ++ str (if isrecord then "" else "not ") ++
    str "to be a record"
  | RecordProjectionsExpected nal ->
    (if List.length nal >= 2 then str "expected projection names are "
     else str "expected projection name is ") ++
    pr_enum (function Name id -> str (Id.to_string id) | _ -> str "_") nal
  | NotEqualInductiveAliases ->
    str "Aliases to inductive types do not match"
  | NoTypeConstraintExpected ->
    strbrk "a definition whose type is constrained can only be subtype " ++
    strbrk "of a definition whose type is itself constrained"
  | PolymorphicStatusExpected b ->
    let status b = if b then str"polymorphic" else str"monomorphic" in
      str "a " ++ status b ++ str" declaration was expected, but a " ++ 
	status (not b) ++ str" declaration was found"
  | IncompatibleInstances -> 
    str"polymorphic universe instances do not match"
  | IncompatibleUniverses incon ->
    str"the universe constraints are inconsistent: " ++
      Univ.explain_universe_inconsistency Universes.pr_with_global_universes incon
  | IncompatiblePolymorphism (env, t1, t2) ->
    str "conversion of polymorphic values generates additional constraints: " ++
      quote (Printer.safe_pr_lconstr_env env Evd.empty t1) ++ spc () ++
      str "compared to " ++ spc () ++
      quote (Printer.safe_pr_lconstr_env env Evd.empty t2)
  | IncompatibleConstraints cst ->
    str " the expected (polymorphic) constraints do not imply " ++
      quote (Univ.pr_constraints (Evd.pr_evd_level Evd.empty) cst)

let explain_signature_mismatch l spec why =
  str "Signature components for label " ++ str (Label.to_string l) ++
  str " do not match:" ++ spc () ++ explain_not_match_error why ++ str "."

let explain_label_already_declared l =
  str ("The label "^Label.to_string l^" is already declared.")

let explain_application_to_not_path _ =
  str "Application of modules is restricted to paths."

let explain_not_a_functor () =
  str "Application of a non-functor."

let explain_is_a_functor () =
  str "Illegal use of a functor."

let explain_incompatible_module_types mexpr1 mexpr2 =
  str "Incompatible module types."

let explain_not_equal_module_paths mp1 mp2 =
  str "Non equal modules."

let explain_no_such_label l =
  str "No such label " ++ str (Label.to_string l) ++ str "."

let explain_incompatible_labels l l' =
  str "Opening and closing labels are not the same: " ++
  str (Label.to_string l) ++ str " <> " ++ str (Label.to_string l') ++ str "!"

let explain_not_a_module s =
  quote (str s) ++ str " is not a module."

let explain_not_a_module_type s =
  quote (str s) ++ str " is not a module type."

let explain_not_a_constant l =
  quote (Label.print l) ++ str " is not a constant."

let explain_incorrect_label_constraint l =
  str "Incorrect constraint for label " ++
  quote (Label.print l) ++ str "."

let explain_generative_module_expected l =
  str "The module " ++ str (Label.to_string l) ++ str " is not generative." ++
  strbrk " Only components of generative modules can be changed" ++
  strbrk " using the \"with\" construct."

let explain_label_missing l s =
  str "The field " ++ str (Label.to_string l) ++ str " is missing in "
  ++ str s ++ str "."

let explain_higher_order_include () =
  str "You cannot Include a higher-order structure."

let explain_module_error = function
  | SignatureMismatch (l,spec,err) -> explain_signature_mismatch l spec err
  | LabelAlreadyDeclared l -> explain_label_already_declared l
  | ApplicationToNotPath mexpr -> explain_application_to_not_path mexpr
  | NotAFunctor -> explain_not_a_functor ()
  | IsAFunctor -> explain_is_a_functor ()
  | IncompatibleModuleTypes (m1,m2) -> explain_incompatible_module_types m1 m2
  | NotEqualModulePaths (mp1,mp2) -> explain_not_equal_module_paths mp1 mp2
  | NoSuchLabel l -> explain_no_such_label l
  | IncompatibleLabels (l1,l2) -> explain_incompatible_labels l1 l2
  | NotAModule s -> explain_not_a_module s
  | NotAModuleType s -> explain_not_a_module_type s
  | NotAConstant l -> explain_not_a_constant l
  | IncorrectWithConstraint l -> explain_incorrect_label_constraint l
  | GenerativeModuleExpected l -> explain_generative_module_expected l
  | LabelMissing (l,s) -> explain_label_missing l s
  | HigherOrderInclude -> explain_higher_order_include ()

(* Module internalization errors *)

(*
let explain_declaration_not_path _ =
  str "Declaration is not a path."

*)

let explain_not_module_nor_modtype s =
  quote (str s) ++ str " is not a module or module type."

let explain_incorrect_with_in_module () =
  str "The syntax \"with\" is not allowed for modules."

let explain_incorrect_module_application () =
  str "Illegal application to a module type."

open Modintern

let explain_module_internalization_error = function
  | NotAModuleNorModtype s -> explain_not_module_nor_modtype s
  | IncorrectWithInModule -> explain_incorrect_with_in_module ()
  | IncorrectModuleApplication -> explain_incorrect_module_application ()

(* Typeclass errors *)

let explain_not_a_class env c =
  pr_constr_env env Evd.empty c ++ str" is not a declared type class."

let explain_unbound_method env cid id =
  str "Unbound method name " ++ Nameops.pr_id (snd id) ++ spc () ++
  str"of class" ++ spc () ++ pr_global cid ++ str "."

let pr_constr_exprs exprs =
  hv 0 (List.fold_right
	 (fun d pps -> ws 2 ++ Ppconstr.pr_constr_expr d ++ pps)
         exprs (mt ()))

let explain_mismatched_contexts env c i j =
  str"Mismatched contexts while declaring instance: " ++ brk (1,1) ++
    hov 1 (str"Expected:" ++ brk (1, 1) ++ pr_rel_context env Evd.empty j) ++
    fnl () ++ brk (1,1) ++
    hov 1 (str"Found:" ++ brk (1, 1) ++ pr_constr_exprs i)

let explain_typeclass_error env = function
  | NotAClass c -> explain_not_a_class env c
  | UnboundMethod (cid, id) -> explain_unbound_method env cid id
  | MismatchedContextInstance (c,i,j) -> explain_mismatched_contexts env c i j

(* Refiner errors *)

let explain_refiner_bad_type arg ty conclty =
  str "Refiner was given an argument" ++ brk(1,1) ++
  pr_lconstr arg ++ spc () ++
  str "of type" ++ brk(1,1) ++ pr_lconstr ty ++ spc () ++
  str "instead of" ++ brk(1,1) ++ pr_lconstr conclty ++ str "."

let explain_refiner_unresolved_bindings l =
  str "Unable to find an instance for the " ++
  str (String.plural (List.length l) "variable") ++ spc () ++
  prlist_with_sep pr_comma pr_name l ++ str"."

let explain_refiner_cannot_apply t harg =
  str "In refiner, a term of type" ++ brk(1,1) ++
  pr_lconstr t ++ spc () ++ str "could not be applied to" ++ brk(1,1) ++
  pr_lconstr harg ++ str "."

let explain_refiner_not_well_typed c =
  str "The term " ++ pr_lconstr c ++ str " is not well-typed."

let explain_intro_needs_product () =
  str "Introduction tactics needs products."

let explain_does_not_occur_in c hyp =
  str "The term" ++ spc () ++ pr_lconstr c ++ spc () ++
  str "does not occur in" ++ spc () ++ pr_id hyp ++ str "."

let explain_non_linear_proof c =
  str "Cannot refine with term" ++ brk(1,1) ++ pr_lconstr c ++
  spc () ++ str "because a metavariable has several occurrences."

let explain_meta_in_type c =
  str "In refiner, a meta appears in the type " ++ brk(1,1) ++ pr_lconstr c ++
  str " of another meta"

let explain_no_such_hyp id =
  str "No such hypothesis: " ++ pr_id id

let explain_refiner_error = function
  | BadType (arg,ty,conclty) -> explain_refiner_bad_type arg ty conclty
  | UnresolvedBindings t -> explain_refiner_unresolved_bindings t
  | CannotApply (t,harg) -> explain_refiner_cannot_apply t harg
  | NotWellTyped c -> explain_refiner_not_well_typed c
  | IntroNeedsProduct -> explain_intro_needs_product ()
  | DoesNotOccurIn (c,hyp) -> explain_does_not_occur_in c hyp
  | NonLinearProof c -> explain_non_linear_proof c
  | MetaInType c -> explain_meta_in_type c
  | NoSuchHyp id -> explain_no_such_hyp id

(* Inductive errors *)

let error_non_strictly_positive env c v =
  let pc = pr_lconstr_env env Evd.empty c in
  let pv = pr_lconstr_env env Evd.empty v in
  str "Non strictly positive occurrence of " ++ pv ++ str " in" ++
  brk(1,1) ++ pc ++ str "."

let error_ill_formed_inductive env c v =
  let pc = pr_lconstr_env env Evd.empty c in
  let pv = pr_lconstr_env env Evd.empty v in
  str "Not enough arguments applied to the " ++ pv ++
  str " in" ++ brk(1,1) ++ pc ++ str "."

let error_ill_formed_constructor env id c v nparams nargs =
  let pv = pr_lconstr_env env Evd.empty v in
  let atomic = Int.equal (nb_prod c) 0 in
  str "The type of constructor" ++ brk(1,1) ++ pr_id id ++ brk(1,1) ++
  str "is not valid;" ++ brk(1,1) ++
  strbrk (if atomic then "it must be " else "its conclusion must be ") ++
  pv ++
  (* warning: because of implicit arguments it is difficult to say which
     parameters must be explicitly given *)
  (if not (Int.equal nparams 0) then
    strbrk " applied to its " ++ str (String.plural nparams "parameter")
  else
    mt()) ++
  (if not (Int.equal nargs 0) then
     str (if not (Int.equal nparams 0) then " and" else " applied") ++
     strbrk " to some " ++ str (String.plural nargs "argument")
   else
     mt()) ++ str "."

let pr_ltype_using_barendregt_convention_env env c =
  (* Use goal_concl_style as an approximation of Barendregt's convention (?) *)
  quote (pr_goal_concl_style_env env Evd.empty c)

let error_bad_ind_parameters env c n v1 v2  =
  let pc = pr_ltype_using_barendregt_convention_env env c in
  let pv1 = pr_lconstr_env env Evd.empty v1 in
  let pv2 = pr_lconstr_env env Evd.empty v2 in
  str "Last occurrence of " ++ pv2 ++ str " must have " ++ pv1 ++
  str " as " ++ pr_nth n ++ str " argument in " ++ brk(1,1) ++ pc ++ str "."

let error_same_names_types id =
  str "The name" ++ spc () ++ pr_id id ++ spc () ++
  str "is used more than once."

let error_same_names_constructors id =
  str "The constructor name" ++ spc () ++ pr_id id ++ spc () ++
  str "is used more than once."

let error_same_names_overlap idl =
  strbrk "The following names are used both as type names and constructor " ++
  str "names:" ++ spc () ++
  prlist_with_sep pr_comma pr_id idl ++ str "."

let error_not_an_arity env c =
  str "The type" ++ spc () ++ pr_lconstr_env env Evd.empty c ++ spc () ++
  str "is not an arity."

let error_bad_entry () =
  str "Bad inductive definition."

let error_large_non_prop_inductive_not_in_type () =
  str "Large non-propositional inductive types must be in Type."

(* Recursion schemes errors *)

let error_not_allowed_case_analysis isrec kind i =
  str (if isrec then "Induction" else "Case analysis") ++
  strbrk " on sort " ++ pr_sort Evd.empty kind ++
  strbrk " is not allowed for inductive definition " ++
  pr_inductive (Global.env()) (fst i) ++ str "."

let error_not_mutual_in_scheme ind ind' =
  if eq_ind ind ind' then
    str "The inductive type " ++ pr_inductive (Global.env()) ind ++
    str " occurs twice."
  else
    str "The inductive types " ++ pr_inductive (Global.env()) ind ++ spc () ++
    str "and" ++ spc () ++ pr_inductive (Global.env()) ind' ++ spc () ++
    str "are not mutually defined."

(* Inductive constructions errors *)

let explain_inductive_error = function
  | NonPos (env,c,v) -> error_non_strictly_positive env c v
  | NotEnoughArgs (env,c,v) -> error_ill_formed_inductive env c v
  | NotConstructor (env,id,c,v,n,m) ->
      error_ill_formed_constructor env id c v n m
  | NonPar (env,c,n,v1,v2) -> error_bad_ind_parameters env c n v1 v2
  | SameNamesTypes id -> error_same_names_types id
  | SameNamesConstructors id -> error_same_names_constructors id
  | SameNamesOverlap idl -> error_same_names_overlap idl
  | NotAnArity (env, c) -> error_not_an_arity env c
  | BadEntry -> error_bad_entry ()
  | LargeNonPropInductiveNotInType ->
      error_large_non_prop_inductive_not_in_type ()

(* Recursion schemes errors *)

let explain_recursion_scheme_error = function
  | NotAllowedCaseAnalysis (isrec,k,i) ->
      error_not_allowed_case_analysis isrec k i
  | NotMutualInScheme (ind,ind')-> error_not_mutual_in_scheme ind ind'

(* Pattern-matching errors *)

let explain_bad_pattern env sigma cstr ty =
  let env = make_all_name_different env in
  let pt = pr_lconstr_env env sigma ty in
  let pc = pr_constructor env cstr in
  str "Found the constructor " ++ pc ++ brk(1,1) ++
  str "while matching a term of type " ++ pt ++ brk(1,1) ++
  str "which is not an inductive type."

let explain_bad_constructor env cstr ind =
  let pi = pr_inductive env ind in
(*  let pc = pr_constructor env cstr in*)
  let pt = pr_inductive env (inductive_of_constructor cstr) in
  str "Found a constructor of inductive type " ++ pt ++ brk(1,1) ++
  str "while a constructor of " ++ pi ++ brk(1,1) ++
  str "is expected."

let decline_string n s =
  if Int.equal n 0 then "no "^s^"s"
  else if Int.equal n 1 then "1 "^s
  else (string_of_int n^" "^s^"s")

let explain_wrong_numarg_constructor env cstr n =
  str "The constructor " ++ pr_constructor env cstr ++
  str " (in type " ++ pr_inductive env (inductive_of_constructor cstr) ++
  str ") expects " ++ str (decline_string n "argument") ++ str "."

let explain_wrong_numarg_inductive env ind n =
  str "The inductive type " ++ pr_inductive env ind ++
  str " expects " ++ str (decline_string n "argument") ++ str "."

let explain_unused_clause env pats =
(* Without localisation
  let s = if List.length pats > 1 then "s" else "" in
  (str ("Unused clause with pattern"^s) ++ spc () ++
    hov 0 (pr_sequence pr_cases_pattern pats) ++ str ")")
*)
  str "This clause is redundant."

let explain_non_exhaustive env pats =
  str "Non exhaustive pattern-matching: no clause found for " ++
  str (String.plural (List.length pats) "pattern") ++
  spc () ++ hov 0 (pr_sequence pr_cases_pattern pats)

let explain_cannot_infer_predicate env sigma typs =
  let env = make_all_name_different env in
  let pr_branch (cstr,typ) =
    let cstr,_ = decompose_app cstr in
    str "For " ++ pr_lconstr_env env sigma cstr ++ str ": " ++ pr_lconstr_env env sigma typ
  in
  str "Unable to unify the types found in the branches:" ++
  spc () ++ hov 0 (prlist_with_sep fnl pr_branch (Array.to_list typs))

let explain_pattern_matching_error env sigma = function
  | BadPattern (c,t) ->
      explain_bad_pattern env sigma c t
  | BadConstructor (c,ind) ->
      explain_bad_constructor env c ind
  | WrongNumargConstructor (c,n) ->
      explain_wrong_numarg_constructor env c n
  | WrongNumargInductive (c,n) ->
      explain_wrong_numarg_inductive env c n
  | UnusedClause tms ->
      explain_unused_clause env tms
  | NonExhaustive tms ->
      explain_non_exhaustive env tms
  | CannotInferPredicate typs ->
      explain_cannot_infer_predicate env sigma typs

let explain_reduction_tactic_error = function
  | Tacred.InvalidAbstraction (env,sigma,c,(env',e)) ->
      str "The abstracted term" ++ spc () ++
      quote (pr_goal_concl_style_env env sigma c) ++
      spc () ++ str "is not well typed." ++ fnl () ++
      explain_type_error env' Evd.empty e

let is_defined_ltac trace =
  let rec aux = function
  | (_, Proof_type.LtacNameCall f) :: tail ->
      not (Tacenv.is_ltac_for_ml_tactic f)
  | (_, Proof_type.LtacAtomCall _) :: tail ->
      false
  | _ :: tail -> aux tail
  | [] -> false in
  aux (List.rev trace)

let explain_ltac_call_trace last trace loc =
  let calls = last :: List.rev_map snd trace in
  let pr_call ck = match ck with
  | Proof_type.LtacNotationCall kn -> quote (KerName.print kn)
  | Proof_type.LtacNameCall cst -> quote (Pptactic.pr_ltac_constant cst)
  | Proof_type.LtacMLCall t ->
      quote (Pptactic.pr_glob_tactic (Global.env()) t)
  | Proof_type.LtacVarCall (id,t) ->
      quote (Nameops.pr_id id) ++ strbrk " (bound to " ++
        Pptactic.pr_glob_tactic (Global.env()) t ++ str ")"
  | Proof_type.LtacAtomCall te ->
      quote (Pptactic.pr_glob_tactic (Global.env())
              (Tacexpr.TacAtom (Loc.ghost,te)))
  | Proof_type.LtacConstrInterp (c, { Pretyping.ltac_constrs = vars }) ->
      quote (pr_glob_constr_env (Global.env()) c) ++
        (if not (Id.Map.is_empty vars) then
          strbrk " (with " ++
            prlist_with_sep pr_comma
            (fun (id,c) ->
                pr_id id ++ str ":=" ++ Printer.pr_lconstr_under_binders c)
            (List.rev (Id.Map.bindings vars)) ++ str ")"
        else mt())
  in
  match calls with
  | [] -> mt ()
  | _ ->
    let kind_of_last_call = match List.last calls with
    | Proof_type.LtacConstrInterp _ -> ", last term evaluation failed."
    | _ -> ", last call failed."
    in
    hov 0 (str "In nested Ltac calls to " ++
           pr_enum pr_call calls ++ strbrk kind_of_last_call)

let skip_extensions trace =
  let rec aux = function
  | (_,Proof_type.LtacNameCall f as tac) :: _ 
      when Tacenv.is_ltac_for_ml_tactic f -> [tac]
  | (_,(Proof_type.LtacNotationCall _ | Proof_type.LtacMLCall _) as tac)
      :: _ -> [tac]
  | t :: tail -> t :: aux tail
  | [] -> [] in
  List.rev (aux (List.rev trace))

let extract_ltac_trace trace eloc =
  let trace = skip_extensions trace in
  let (loc,c),tail = List.sep_last trace in
  if is_defined_ltac trace then
    (* We entered a user-defined tactic,
       we display the trace with location of the call *)
    let msg = hov 0 (explain_ltac_call_trace c tail eloc ++ fnl()) in
    Some msg, loc
  else
    (* We entered a primitive tactic, we don't display trace but
       report on the finest location *)
    let best_loc =
      if not (Loc.is_ghost eloc) then eloc else
        (* trace is with innermost call coming first *)
        let rec aux = function
        | (loc,_)::tail when not (Loc.is_ghost loc) -> loc
        | _::tail -> aux tail
        | [] -> Loc.ghost in
        aux trace in
    None, best_loc
