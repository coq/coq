(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Names
open Nameops
open Namegen
open Constr
open Context
open Termops
open Environ
open Pretype_errors
open Type_errors
open Typeclasses_errors
open Indrec
open Cases
open Logic
open Printer
open Evd
open Context.Rel.Declaration

module RelDecl = Context.Rel.Declaration

(* This simplifies the typing context of Cases clauses *)
(* hope it does not disturb other typing contexts *)
let contract env sigma lc =
  let open EConstr in
  let l = ref [] in
  let contract_context decl env =
    match decl with
      | LocalDef (_,c',_) when isRel sigma c' ->
          l := (Vars.substl !l c') :: !l;
          env
      | _ ->
          let t = Vars.substl !l (RelDecl.get_type decl) in
          let decl = decl |> RelDecl.map_name (named_hd env sigma t) |> RelDecl.map_value (Vars.substl !l) |> RelDecl.set_type t in
          l := (mkRel 1) :: List.map (Vars.lift 1) !l;
          push_rel decl env
  in
  let env = process_rel_context contract_context env in
  (env, List.map (Vars.substl !l) lc)

let contract2 env sigma a b = match contract env sigma [a;b] with
  | env, [a;b] -> env,a,b | _ -> assert false

let contract3 env sigma a b c = match contract env sigma [a;b;c] with
  | env, [a;b;c] -> env,a,b,c | _ -> assert false

let contract4 env sigma a b c d = match contract env sigma [a;b;c;d] with
  | env, [a;b;c;d] -> (env,a,b,c),d | _ -> assert false

let contract1 env sigma a v =
  match contract env sigma (a :: v) with
  | env, a::l -> env,a,l
  | _ -> assert false

let rec contract3' env sigma a b c = function
  | OccurCheck (evk,d) ->
    let x,d = contract4 env sigma a b c d in x,OccurCheck(evk, d)
  | NotClean ((evk,args),env',d) ->
      let env',d,args = contract1 env' sigma d args in
      contract3 env sigma a b c,NotClean((evk,args),env',d)
  | ConversionFailed (env',t1,t2) ->
      let (env',t1,t2) = contract2 env' sigma t1 t2 in
      contract3 env sigma a b c, ConversionFailed (env',t1,t2)
  | IncompatibleInstances (env',ev,t1,t2) ->
      let (env',ev,t1,t2) = contract3 env' sigma (EConstr.mkEvar ev) t1 t2 in
      contract3 env sigma a b c, IncompatibleInstances (env',EConstr.destEvar sigma ev,t1,t2)
  | NotSameArgSize | NotSameHead | NoCanonicalStructure | MetaOccurInBody _
  | InstanceNotSameType _ | InstanceNotFunctionalType _ | ProblemBeyondCapabilities
  | UnifUnivInconsistency _ as x -> contract3 env sigma a b c, x
  | CannotSolveConstraint ((pb,env',t,u),x) ->
      let env',t,u = contract2 env' sigma t u in
      let y,x = contract3' env sigma a b c x in
      y,CannotSolveConstraint ((pb,env',t,u),x)

(** Ad-hoc reductions *)

let j_nf_betaiotaevar env sigma j =
  { uj_val = j.uj_val;
    uj_type = Reductionops.nf_betaiota env sigma j.uj_type }

let jv_nf_betaiotaevar env sigma jl =
  Array.Smart.map (fun j -> j_nf_betaiotaevar env sigma j) jl

(** Printers *)

let pr_lconstr_env e s c = quote (pr_lconstr_env e s c)
let pr_leconstr_env e s c = quote (pr_leconstr_env e s c)
let pr_ljudge_env e s c = let v,t = pr_ljudge_env e s c in (quote v,quote t)

(** A canonisation procedure for constr such that comparing there
    externalisation catches more equalities *)
let canonize_constr sigma c =
  (* replaces all the names in binders by [dn] ("default name"),
     ensures that [alpha]-equivalent terms will have the same
     externalisation. *)
  let open EConstr in
  let dn = Name.Anonymous in
  let rec canonize_binders c =
    match EConstr.kind sigma c with
    | Prod (x,t,b) -> mkProd({x with binder_name=dn},t,b)
    | Lambda (x,t,b) -> mkLambda({x with binder_name=dn},t,b)
    | LetIn (x,u,t,b) -> mkLetIn({x with binder_name=dn},u,t,b)
    | _ -> EConstr.map sigma canonize_binders c
  in
  canonize_binders c

let rec display_expr_eq c1 c2 =
  let open Constrexpr in
  match CAst.(c1.v, c2.v) with
  | (CHole _ | CEvar _), _ | _, (CEvar _ | CHole _) -> true
  | _ ->
    Constrexpr_ops.constr_expr_eq_gen display_expr_eq c1 c2

(** Tries to realize when the two terms, albeit different are printed the same. *)
let display_eq ~flags env sigma t1 t2 =
  (* terms are canonized, then their externalisation is compared syntactically *)
  let open Constrextern in
  let t1 = canonize_constr sigma t1 in
  let t2 = canonize_constr sigma t2 in
  let ct1 = Flags.with_options flags (fun () -> extern_constr env sigma t1) () in
  let ct2 = Flags.with_options flags (fun () -> extern_constr env sigma t2) () in
  display_expr_eq ct1 ct2

(** This function adds some explicit printing flags if the two arguments are
    printed alike. *)
let rec pr_explicit_aux env sigma t1 t2 = function
| [] ->
  (* no specified flags: default. *)
  Printer.pr_leconstr_env env sigma t1, Printer.pr_leconstr_env env sigma t2
| flags :: rem ->
  let equal = display_eq ~flags env sigma t1 t2 in
  if equal then
    (* The two terms are the same from the user point of view *)
    pr_explicit_aux env sigma t1 t2 rem
  else
    let open Constrextern in
    let ct1 = Flags.with_options flags (fun () -> extern_constr env sigma t1) ()
    in
    let ct2 = Flags.with_options flags (fun () -> extern_constr env sigma t2) ()
    in
    Ppconstr.pr_lconstr_expr env sigma ct1, Ppconstr.pr_lconstr_expr env sigma ct2

let explicit_flags =
  let open Constrextern in
  [ []; (* First, try with the current flags *)
    [print_implicits]; (* Then with implicit *)
    [print_universes]; (* Then with universes *)
    [print_universes; print_implicits]; (* With universes AND implicits *)
    [print_implicits; print_coercions; print_no_symbol]; (* Then more! *)
    [print_universes; print_implicits; print_coercions; print_no_symbol] (* and more! *) ]

let with_diffs pm pn =
  if not (Proof_diffs.show_diffs ()) then pm, pn else
  try
    let tokenize_string = Proof_diffs.tokenize_string in
    Pp_diff.diff_pp ~tokenize_string pm pn
  with Pp_diff.Diff_Failure msg ->
    begin
      try ignore(Sys.getenv("HIDEDIFFFAILUREMSG"))
      with Not_found -> Proof_diffs.notify_proof_diff_failure msg
    end;
    pm, pn

let pr_explicit env sigma t1 t2 =
  let p1, p2 = pr_explicit_aux env sigma t1 t2 explicit_flags in
  let p1, p2 = with_diffs p1 p2 in
  quote p1, quote p2

let pr_db env i =
  try
    match env |> lookup_rel i |> get_name with
      | Name id -> Id.print id
      | Anonymous -> str "<>"
  with Not_found -> str "UNBOUND_REL_" ++ int i

let explain_unbound_rel env sigma n =
  let pe = pr_ne_context_of (str "In environment") env sigma in
  str "Unbound reference: " ++ pe ++
  str "The reference " ++ int n ++ str " is free."

let explain_unbound_var env v =
  let var = Id.print v in
  str "No such section variable or assumption: " ++ var ++ str "."

let explain_not_type env sigma j =
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

let explain_reference_variables sigma id c =
  pr_global c ++ strbrk " depends on the variable " ++ Id.print id ++
  strbrk " which is not declared in the context."

let rec pr_disjunction pr = function
  | [a] -> pr  a
  | [a;b] -> pr a ++ str " or" ++ spc () ++ pr b
  | a::l -> pr a ++ str "," ++ spc () ++ pr_disjunction pr l
  | [] -> assert false

let explain_elim_arity env sigma ind c pj okinds =
  let open EConstr in
  let env = make_all_name_different env sigma in
  let pi = pr_inductive env (fst ind) in
  let pc = pr_leconstr_env env sigma c in
  let msg = match okinds with
  | Some(sorts,kp,ki,explanation) ->
      let sorts = Inductiveops.sorts_below sorts in
      let pki = Sorts.pr_sort_family ki in
      let pkp = Sorts.pr_sort_family kp in
      let explanation =	match explanation with
        | NonInformativeToInformative ->
          "proofs can be eliminated only to build proofs"
        | StrongEliminationOnNonSmallType ->
          "strong elimination on non-small inductive types leads to paradoxes"
        | WrongArity ->
          "wrong arity" in
      let ppar = pr_disjunction (fun s -> quote (Sorts.pr_sort_family s)) sorts in
      let ppt = pr_leconstr_env env sigma (snd (decompose_prod_assum sigma pj.uj_type)) in
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
  let env = make_all_name_different env sigma in
  let pc = pr_leconstr_env env sigma cj.uj_val in
  let pct = pr_leconstr_env env sigma cj.uj_type in
    match EConstr.kind sigma cj.uj_type with
      | Evar _ ->
          str "Cannot infer a type for this expression."
      | _ ->
          str "The term" ++ brk(1,1) ++ pc ++ spc () ++
          str "has type" ++ brk(1,1) ++ pct ++ spc () ++
          str "which is not a (co-)inductive type."

let explain_number_branches env sigma cj expn =
  let env = make_all_name_different env sigma in
  let pc = pr_leconstr_env env sigma cj.uj_val in
  let pct = pr_leconstr_env env sigma cj.uj_type in
  str "Matching on term" ++ brk(1,1) ++ pc ++ spc () ++
  str "of type" ++ brk(1,1) ++ pct ++ spc () ++
  str "expects " ++  int expn ++ str " branches."

let explain_ill_formed_branch env sigma c ci actty expty =
  let simp t = Reductionops.nf_betaiota env sigma t in
  let env = make_all_name_different env sigma in
  let pc = pr_leconstr_env env sigma c in
  let pa, pe = pr_explicit env sigma (simp actty) (simp expty) in
  strbrk "In pattern-matching on term" ++ brk(1,1) ++ pc ++
  spc () ++ strbrk "the branch for constructor" ++ spc () ++
  quote (pr_pconstructor env sigma ci) ++
  spc () ++ str "has type" ++ brk(1,1) ++ pa ++ spc () ++
  str "which should be" ++ brk(1,1) ++ pe ++ str "."

let explain_generalization env sigma (name,var) j =
  let pe = pr_ne_context_of (str "In environment") env sigma in
  let pv = pr_letype_env env sigma var in
  let (pc,pt) = pr_ljudge_env (push_rel_assum (make_annot name Sorts.Relevant,var) env) sigma j in
  pe ++ str "Cannot generalize" ++ brk(1,1) ++ pv ++ spc () ++
  str "over" ++ brk(1,1) ++ pc ++ str "," ++ spc () ++
  str "it has type" ++ spc () ++ pt ++
  spc () ++ str "which should be Set, Prop or Type."

let explain_unification_error env sigma p1 p2 = function
  | None -> mt()
  | Some e ->
     let rec aux p1 p2 = function
     | OccurCheck (evk,rhs) ->
        [str "cannot define " ++ quote (pr_existential_key env sigma evk) ++
        strbrk " with term " ++ pr_leconstr_env env sigma rhs ++
        strbrk " that would depend on itself"]
     | NotClean ((evk,args),env,c) ->
        let env = make_all_name_different env sigma in
        [str "cannot instantiate " ++ quote (pr_existential_key env sigma evk)
        ++ strbrk " because " ++ pr_leconstr_env env sigma c ++
        strbrk " is not in its scope" ++
        (if List.is_empty args then mt() else
         strbrk ": available arguments are " ++
         pr_sequence (pr_leconstr_env env sigma) (List.rev args))]
     | NotSameArgSize | NotSameHead | NoCanonicalStructure ->
        (* Error speaks from itself *) []
     | ConversionFailed (env,t1,t2) ->
        let t1 = Reductionops.nf_betaiota env sigma t1 in
        let t2 = Reductionops.nf_betaiota env sigma t2 in
        if EConstr.eq_constr sigma t1 p1 && EConstr.eq_constr sigma t2 p2 then [] else
        let env = make_all_name_different env sigma in
        if not (EConstr.eq_constr sigma t1 p1) || not (EConstr.eq_constr sigma t2 p2) then
          let t1, t2 = pr_explicit env sigma t1 t2 in
          [str "cannot unify " ++ t1 ++ strbrk " and " ++ t2]
        else []
     | IncompatibleInstances (env,ev,t1,t2) ->
        let env = make_all_name_different env sigma in
        let ev = pr_leconstr_env env sigma (EConstr.mkEvar ev) in
        let t1 = Reductionops.nf_betaiota env sigma t1 in
        let t2 = Reductionops.nf_betaiota env sigma t2 in
        let t1, t2 = pr_explicit env sigma t1 t2 in
        [ev ++ strbrk " has otherwise to unify with " ++ t1 ++ str " which is incompatible with " ++ t2]
     | MetaOccurInBody evk ->
        [str "instance for " ++ quote (pr_existential_key env sigma evk) ++
        strbrk " refers to a metavariable - please report your example" ++
        strbrk "at " ++ str Coq_config.wwwbugtracker ++ str "."]
     | InstanceNotSameType (evk,env,t,u) ->
        let t, u = pr_explicit env sigma t u in
        [str "unable to find a well-typed instantiation for " ++
        quote (pr_existential_key env sigma evk) ++
        strbrk ": cannot ensure that " ++
        t ++ strbrk " is a subtype of " ++ u]
     | InstanceNotFunctionalType (evk,env,f,u) ->
        let env = make_all_name_different env sigma in
        let f = pr_leconstr_env env sigma f in
        let u = pr_leconstr_env env sigma u in
        [str "unable to find a well-typed instantiation for " ++
        quote (pr_existential_key env sigma evk) ++
        strbrk ": " ++ f ++
        strbrk " is expected to have a functional type but it has type " ++ u]
     | UnifUnivInconsistency p ->
       [str "universe inconsistency: " ++
        UGraph.explain_universe_inconsistency (Termops.pr_evd_level sigma) p]
     | CannotSolveConstraint ((pb,env,t,u),e) ->
        let env = make_all_name_different env sigma in
        (strbrk "cannot satisfy constraint " ++ pr_leconstr_env env sigma t ++
        str " == " ++ pr_leconstr_env env sigma u)
        :: aux t u e
     | ProblemBeyondCapabilities ->
        []
     in
     match aux p1 p2 e with
     | [] -> mt ()
     | l -> spc () ++ str "(" ++
            prlist_with_sep pr_semicolon (fun x -> x) l ++ str ")"

let explain_actual_type env sigma j t reason =
  let env = make_all_name_different env sigma in
  let j = j_nf_betaiotaevar env sigma j in
  let t = Reductionops.nf_betaiota env sigma t in
  (* Actually print *)
  let pe = pr_ne_context_of (str "In environment") env sigma in
  let pc = pr_leconstr_env env sigma (Environ.j_val j) in
  let (pt, pct) = pr_explicit env sigma t (Environ.j_type j) in
  let ppreason = explain_unification_error env sigma j.uj_type t reason in
  pe ++
  hov 0 (
  str "The term" ++ brk(1,1) ++ pc ++ spc () ++
  str "has type" ++ brk(1,1) ++ pct ++ spc () ++
  str "while it is expected to have type" ++ brk(1,1) ++ pt ++
  ppreason ++ str ".")

let explain_incorrect_primitive env sigma j exp =
  let env = make_all_name_different env sigma in
  let {uj_val=p;uj_type=t} = j in
  let t = Reductionops.nf_betaiota env sigma t in
  let exp = Reductionops.nf_betaiota env sigma exp in
  (* Actually print *)
  let pe = pr_ne_context_of (str "In environment") env sigma in
  let (pt, pct) = pr_explicit env sigma exp t in
  pe ++
  hov 0 (
  str "The primitive" ++ brk(1,1) ++ str (CPrimitives.op_or_type_to_string p) ++ spc () ++
  str "has type" ++ brk(1,1) ++ pct ++ spc () ++
  str "while it is expected to have type" ++ brk(1,1) ++ pt ++ str ".")

let explain_cant_apply_bad_type env sigma (n,exptyp,actualtyp) rator randl =
  let randl = jv_nf_betaiotaevar env sigma randl in
  let actualtyp = Reductionops.nf_betaiota env sigma actualtyp in
  let env = make_all_name_different env sigma in
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
  let env = make_all_name_different env sigma in
  let nargs = Array.length randl in
(*  let pe = pr_ne_context_of (str "in environment") env sigma in*)
  let pr = pr_leconstr_env env sigma rator.uj_val in
  let prt = pr_leconstr_env env sigma rator.uj_type in
  let appl = prvect_with_sep fnl
               (fun c ->
                  let pc = pr_leconstr_env env sigma c.uj_val in
                  let pct = pr_leconstr_env env sigma c.uj_type in
                  hov 2 (pc ++ spc () ++ str ": " ++ pct)) randl
  in
  str "Illegal application (Non-functional construction): " ++
  (* pe ++ *) fnl () ++
  str "The expression" ++ brk(1,1) ++ pr ++ spc () ++
  str "of type" ++ brk(1,1) ++ prt ++ spc () ++
  str "cannot be applied to the " ++ str (String.plural nargs "term") ++
  fnl () ++ str " " ++ v 0 appl

let explain_unexpected_type env sigma actual_type expected_type e =
  let pract, prexp = pr_explicit env sigma actual_type expected_type in
  str "Found type" ++ spc () ++ pract ++ spc () ++
  str "where" ++ spc () ++ prexp ++ str " was expected" ++
  explain_unification_error env sigma actual_type expected_type (Some e) ++ str"."

let explain_not_product env sigma c =
  let pr = pr_econstr_env env sigma c in
  str "The type of this term is a product" ++ spc () ++
  str "while it is expected to be" ++
  (if EConstr.isType sigma c then str " a sort" else (brk(1,1) ++ pr)) ++ str "."

let explain_ill_formed_fix_body env sigma names i = function
  (* Fixpoint guard errors *)
  | NotEnoughAbstractionInFixBody ->
      str "Not enough abstractions in the definition"
  | RecursionNotOnInductiveType c ->
      str "Recursive definition on" ++ spc () ++ pr_leconstr_env env sigma c ++
      spc () ++ str "which should be a recursive inductive type"
  | RecursionOnIllegalTerm(j,(arg_env, arg),le_lt) ->
      let arg_env = make_all_name_different arg_env sigma in
      let called =
        match names.(j).binder_name with
            Name id -> Id.print id
          | Anonymous -> str "the " ++ pr_nth i ++ str " definition" in
      let pr_db x = quote (pr_db env x) in
      let vars =
        match Lazy.force le_lt with
            ([],[]) -> assert false
          | ([x],[]) -> str "a subterm of " ++ pr_db x
          | (le,[]) -> str "a subterm of the following variables: " ++
              pr_sequence pr_db le
          | (_,[x]) -> pr_db x
          | (_,lt) ->
              str "one of the following variables: " ++
              pr_sequence pr_db lt in
      str "Recursive call to " ++ called ++ spc () ++
      strbrk "has principal argument equal to" ++ spc () ++
      pr_leconstr_env arg_env sigma arg ++ strbrk " instead of " ++ vars
  | NotEnoughArgumentsForFixCall j ->
      let called =
        match names.(j).binder_name with
            Name id -> Id.print id
          | Anonymous -> str "the " ++ pr_nth i ++ str " definition" in
     str "Recursive call to " ++ called ++ str " has not enough arguments"
  | FixpointOnIrrelevantInductive ->
    strbrk "Fixpoints on proof irrelevant inductive types should produce proof irrelevant values"

let explain_ill_formed_cofix_body env sigma = function
  (* CoFixpoint guard errors *)
  | CodomainNotInductiveType c ->
      str "The codomain is" ++ spc () ++ pr_leconstr_env env sigma c ++ spc () ++
      str "which should be a coinductive type"
  | NestedRecursiveOccurrences ->
      str "Nested recursive occurrences"
  | UnguardedRecursiveCall c ->
      str "Unguarded recursive call in" ++ spc () ++ pr_leconstr_env env sigma c
  | RecCallInTypeOfAbstraction c ->
      str "Recursive call forbidden in the domain of an abstraction:" ++
      spc () ++ pr_leconstr_env env sigma c
  | RecCallInNonRecArgOfConstructor c ->
      str "Recursive call on a non-recursive argument of constructor" ++
      spc () ++ pr_leconstr_env env sigma c
  | RecCallInTypeOfDef c ->
      str "Recursive call forbidden in the type of a recursive definition" ++
      spc () ++ pr_leconstr_env env sigma c
  | RecCallInCaseFun c ->
      str "Invalid recursive call in a branch of" ++
      spc () ++ pr_leconstr_env env sigma c
  | RecCallInCaseArg c ->
      str "Invalid recursive call in the argument of \"match\" in" ++ spc () ++
      pr_leconstr_env env sigma c
  | RecCallInCasePred c ->
      str "Invalid recursive call in the \"return\" clause of \"match\" in" ++
      spc () ++ pr_leconstr_env env sigma c
  | NotGuardedForm c ->
      str "Sub-expression " ++ pr_leconstr_env env sigma c ++
      strbrk " not in guarded form (should be a constructor," ++
      strbrk " an abstraction, a match, a cofix or a recursive call)"
  | ReturnPredicateNotCoInductive c ->
     str "The return clause of the following pattern matching should be" ++
     strbrk " a coinductive type:" ++
     spc () ++ pr_leconstr_env env sigma c

(* TODO: use the names *)
(* (co)fixpoints *)
let explain_ill_formed_rec_body env sigma err names i fixenv vdefj =
  let prt_name i =
    match names.(i).binder_name with
        Name id -> str "Recursive definition of " ++ Id.print id
      | Anonymous -> str "The " ++ pr_nth i ++ str " definition" in
  let st = match err with
    | FixGuardError err -> explain_ill_formed_fix_body env sigma names i err
    | CoFixGuardError  err -> explain_ill_formed_cofix_body env sigma err
  in
  prt_name i ++ str " is ill-formed." ++ fnl () ++
  pr_ne_context_of (str "In environment") env sigma ++
  st ++ str "." ++ fnl () ++
  (try (* May fail with unresolved globals. *)
      let fixenv = make_all_name_different fixenv sigma in
      let pvd = pr_leconstr_env fixenv sigma vdefj.(i).uj_val in
        str"Recursive definition is:" ++ spc () ++ pvd ++ str "."
    with e when CErrors.noncritical e -> mt ())

let explain_ill_typed_rec_body env sigma i names vdefj vargs =
  let env = make_all_name_different env sigma in
  let pvd = pr_leconstr_env env sigma vdefj.(i).uj_val in
  let pvdt, pv = pr_explicit env sigma vdefj.(i).uj_type vargs.(i) in
  str "The " ++
  (match vdefj with [|_|] -> mt () | _ -> pr_nth (i+1) ++ spc ()) ++
  str "recursive definition" ++ spc () ++ pvd ++ spc () ++
  str "has type" ++ spc () ++ pvdt ++ spc () ++
  str "while it should be" ++ spc () ++ pv ++ str "."

let explain_cant_find_case_type env sigma c =
  let env = make_all_name_different env sigma in
  let pe = pr_leconstr_env env sigma c in
  str "Cannot infer the return type of pattern-matching on" ++ ws 1 ++
    pe ++ str "."

let explain_occur_check env sigma ev rhs =
  let env = make_all_name_different env sigma in
  let pt = pr_leconstr_env env sigma rhs in
  str "Cannot define " ++ pr_existential_key env sigma ev ++ str " with term" ++
  brk(1,1) ++ pt ++ spc () ++ str "that would depend on itself."

let pr_trailing_ne_context_of env sigma =
  if List.is_empty (Environ.rel_context env) &&
    List.is_empty (Environ.named_context env)
  then str "."
  else (strbrk " in environment:" ++ pr_context_unlimited env sigma)

let rec explain_evar_kind env sigma evk ty =
    let open Evar_kinds in
    function
  | Evar_kinds.NamedHole id ->
      strbrk "the existential variable named " ++ Id.print id
  | Evar_kinds.QuestionMark {qm_record_field=None} ->
      strbrk "this placeholder of type " ++ ty
  | Evar_kinds.QuestionMark {qm_record_field=Some {fieldname; recordname}} ->
          str "field " ++ (Printer.pr_constant env fieldname) ++ str " of record " ++ (Printer.pr_inductive env recordname)
  | Evar_kinds.CasesType false ->
      strbrk "the type of this pattern-matching problem"
  | Evar_kinds.CasesType true ->
      strbrk "a subterm of type " ++ ty ++
      strbrk " in the type of this pattern-matching problem"
  | Evar_kinds.BinderType (Name id) ->
      strbrk "the type of " ++ Id.print id
  | Evar_kinds.BinderType Anonymous ->
      strbrk "the type of this anonymous binder"
  | Evar_kinds.EvarType (ido,evk) ->
      let pp = match ido with
        | Some id -> str "?" ++ Id.print id
        | None ->
          try pr_existential_key env sigma evk
          with (* defined *) Not_found -> strbrk "an internal placeholder" in
      strbrk "the type of " ++ pp
  | Evar_kinds.ImplicitArg (c,(n,ido),b) ->
      let id = Option.get ido in
      strbrk "the implicit parameter " ++ Id.print id ++ spc () ++ str "of" ++
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
      str " for the variable " ++ Id.print id
  | Evar_kinds.SubEvar (where,evk') ->
      let rec find_source evk =
        let evi = Evd.find sigma evk in
        match snd evi.evar_source with
        | Evar_kinds.SubEvar (_,evk) -> find_source evk
        | src -> evi,src in
      let evi,src = find_source evk' in
      let pc = match evi.evar_body with
      | Evar_defined c -> pr_leconstr_env env sigma c
      | Evar_empty -> assert false in
      let ty' = evi.evar_concl in
      pr_existential_key env sigma evk ++
      strbrk " in the partial instance " ++ pc ++
      strbrk " found for " ++
      explain_evar_kind env sigma evk
      (pr_leconstr_env env sigma ty') src

let explain_typeclass_resolution env sigma evi k =
  match Typeclasses.class_of_constr env sigma evi.evar_concl with
  | Some _ ->
    let env = Evd.evar_filtered_env env evi in
      fnl () ++ str "Could not find an instance for " ++
      pr_leconstr_env env sigma evi.evar_concl ++
      pr_trailing_ne_context_of env sigma
  | _ -> mt()

let explain_placeholder_kind env sigma c e =
  match e with
  | Some (SeveralInstancesFound n) ->
      strbrk " (several distinct possible type class instances found)"
  | None ->
      match Typeclasses.class_of_constr env sigma c with
      | Some _ -> strbrk " (no type class instance found)"
      | _ -> mt ()

let explain_unsolvable_implicit env sigma evk explain =
  let evi = Evarutil.nf_evar_info sigma (Evd.find_undefined sigma evk) in
  let env = Evd.evar_filtered_env env evi in
  let type_of_hole = pr_leconstr_env env sigma evi.evar_concl in
  let pe = pr_trailing_ne_context_of env sigma in
  strbrk "Cannot infer " ++
  explain_evar_kind env sigma evk type_of_hole (snd evi.evar_source) ++
  explain_placeholder_kind env sigma evi.evar_concl explain ++ pe

let explain_var_not_found env id =
  str "The variable" ++ spc () ++ Id.print id ++
  spc () ++ str "was not found" ++
  spc () ++ str "in the current" ++ spc () ++ str "environment" ++ str "."


let explain_evar_not_found env sigma id =
  let undef = Evar.Map.domain (Evd.undefined_map sigma) in
  let all_undef_evars = Evar.Set.elements undef in
  let f ev = Id.equal id (Termops.evar_suggested_name (Global.env ()) sigma ev) in
  if List.exists f all_undef_evars then
    (* The name is used for printing but is not user-given *)
    str "?" ++ Id.print id ++
    strbrk " is a generated name. Only user-given names for existential variables" ++
    strbrk " can be referenced. To give a user name to an existential variable," ++
    strbrk " introduce it with the ?[name] syntax."
  else
    str "Unknown existential variable."

let explain_wrong_case_info env (ind,u) ci =
  let pi = pr_inductive env ind in
  if Ind.CanOrd.equal ci.ci_ind ind then
    str "Pattern-matching expression on an object of inductive type" ++
    spc () ++ pi ++ spc () ++ str "has invalid information."
  else
    let pc = pr_inductive env ci.ci_ind in
    str "A term of inductive type" ++ spc () ++ pi ++ spc () ++
    str "was given to a pattern-matching expression on the inductive type" ++
    spc () ++ pc ++ str "."

let explain_cannot_unify env sigma m n e =
  let env = make_all_name_different env sigma in
  let pm, pn = pr_explicit env sigma m n in
  let ppreason = explain_unification_error env sigma m n e in
  let pe = pr_ne_context_of (str "In environment") env sigma in
  pe ++ str "Unable to unify" ++ brk(1,1) ++ pm ++ spc () ++
  str "with" ++ brk(1,1) ++ pn ++ ppreason ++ str "."

let explain_cannot_unify_local env sigma m n subn =
  let pm = pr_leconstr_env env sigma m in
  let pn = pr_leconstr_env env sigma n in
  let psubn = pr_leconstr_env env sigma subn in
    str "Unable to unify" ++ brk(1,1) ++ pm ++ spc () ++
      str "with" ++ brk(1,1) ++ pn ++ spc () ++ str "as" ++ brk(1,1) ++
      psubn ++ str " contains local variables."

let explain_refiner_cannot_generalize env sigma ty =
  str "Cannot find a well-typed generalisation of the goal with type: " ++
  pr_leconstr_env env sigma ty ++ str "."

let explain_no_occurrence_found env sigma c id =
  str "Found no subterm matching " ++ pr_leconstr_env env sigma c ++
  str " in " ++
    (match id with
      | Some id -> Id.print id
      | None -> str"the current goal") ++ str "."

let explain_cannot_unify_binding_type env sigma m n =
  let pm = pr_leconstr_env env sigma m in
  let pn = pr_leconstr_env env sigma n in
  str "This binding has type" ++ brk(1,1) ++ pm ++ spc () ++
  str "which should be unifiable with" ++ brk(1,1) ++ pn ++ str "."

let explain_cannot_find_well_typed_abstraction env sigma p l e =
  str "Abstracting over the " ++
  str (String.plural (List.length l) "term") ++ spc () ++
  hov 0 (pr_enum (fun c -> pr_leconstr_env env sigma c) l) ++ spc () ++
  str "leads to a term" ++ spc () ++ pr_letype_env ~goal_concl_style:true env sigma p ++
  spc () ++ str "which is ill-typed." ++
  (match e with None -> mt () | Some e -> fnl () ++ str "Reason is: " ++ e)

let explain_wrong_abstraction_type env sigma na abs expected result =
  let ppname = match na with Name id -> Id.print id ++ spc () | _ -> mt () in
  str "Cannot instantiate metavariable " ++ ppname ++ strbrk "of type " ++
  pr_leconstr_env env sigma expected ++ strbrk " with abstraction " ++
  pr_leconstr_env env sigma abs ++ strbrk " of incompatible type " ++
  pr_leconstr_env env sigma result ++ str "."

let explain_abstraction_over_meta _ m n =
  strbrk "Too complex unification problem: cannot find a solution for both " ++
  Name.print m ++ spc () ++ str "and " ++ Name.print n ++ str "."

let explain_non_linear_unification env sigma m t =
  strbrk "Cannot unambiguously instantiate " ++
  Name.print m ++ str ":" ++
  strbrk " which would require to abstract twice on " ++
  pr_leconstr_env env sigma t ++ str "."

let explain_unsatisfied_constraints env sigma cst =
  strbrk "Unsatisfied constraints: " ++
    Univ.pr_constraints (Termops.pr_evd_level sigma) cst ++
    spc () ++ str "(maybe a bugged tactic)."

let explain_undeclared_universe env sigma l =
  strbrk "Undeclared universe: " ++
    Termops.pr_evd_level sigma l ++
    spc () ++ str "(maybe a bugged tactic)."

let explain_disallowed_sprop () =
  Pp.(strbrk "SProp is disallowed because the "
      ++ str "\"Allow StrictProp\""
      ++ strbrk " flag is off.")

let explain_bad_relevance env =
  strbrk "Bad relevance (maybe a bugged tactic)."

let explain_bad_invert env =
  strbrk "Bad case inversion (maybe a bugged tactic)."

let explain_bad_variance env sigma ~lev ~expected ~actual =
  str "Incorrect variance for universe " ++ Termops.pr_evd_level sigma lev ++
  str": expected " ++ Univ.Variance.pr expected ++
  str " but cannot be less restrictive than " ++ Univ.Variance.pr actual ++ str "."

let explain_type_error env sigma err =
  let env = make_all_name_different env sigma in
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
      explain_reference_variables sigma id c
  | ElimArity (ind, c, pj, okinds) ->
      explain_elim_arity env sigma ind c pj okinds
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
  | IncorrectPrimitive (j, t) ->
    explain_incorrect_primitive env sigma j t
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
  | UndeclaredUniverse l ->
     explain_undeclared_universe env sigma l
  | DisallowedSProp -> explain_disallowed_sprop ()
  | BadRelevance -> explain_bad_relevance env
  | BadInvert -> explain_bad_invert env
  | BadVariance {lev;expected;actual} -> explain_bad_variance env sigma ~lev ~expected ~actual

let pr_position (cl,pos) =
  let clpos = match cl with
    | None -> str " of the goal"
    | Some (id,Locus.InHyp) -> str " of hypothesis " ++ Id.print id
    | Some (id,Locus.InHypTypeOnly) -> str " of the type of hypothesis " ++ Id.print id
    | Some (id,Locus.InHypValueOnly) -> str " of the body of hypothesis " ++ Id.print id in
  int pos ++ clpos

let explain_cannot_unify_occurrences env sigma nested ((cl2,pos2),t2) ((cl1,pos1),t1) e =
  if nested then
    str "Found nested occurrences of the pattern at positions " ++
    int pos1 ++ strbrk " and " ++ pr_position (cl2,pos2) ++ str "."
  else
    let ppreason = match e with
    | None -> mt()
    | Some (c1,c2,e) ->
      explain_unification_error env sigma c1 c2 (Some e)
    in
    str "Found incompatible occurrences of the pattern" ++ str ":" ++
    spc () ++ str "Matched term " ++ pr_leconstr_env env sigma t2 ++
    strbrk " at position " ++ pr_position (cl2,pos2) ++
    strbrk " is not compatible with matched term " ++
    pr_leconstr_env env sigma t1 ++ strbrk " at position " ++
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
        (fun (ev, evi) -> fnl () ++ pr_existential_key (Global.env ()) sigma ev ++
            str " : " ++ pr_leconstr_env env' sigma evi.evar_concl ++ fnl ()) l
      in
      h (pe ++ evs ++ pr_evar_constraints sigma cstrs)
    else
      let filter evk _ = Evar.Map.mem evk evars in
      pr_evar_map_filter ~with_univs:false filter env sigma

let explain_unsatisfiable_constraints env sigma constr comp =
  let (_, constraints) = Evd.extract_all_conv_pbs sigma in
  let tcs = Evd.get_typeclass_evars sigma in
  let undef = Evd.undefined_map sigma in
  (* Only keep evars that are subject to resolution and members of the given
     component. *)
  let is_kept evk _ = match comp with
  | None -> Evar.Set.mem evk tcs
  | Some comp -> Evar.Set.mem evk tcs && Evar.Set.mem evk comp
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

let rec explain_pretype_error env sigma err =
  let env = Evardefine.env_nf_betaiotaevar sigma env in
  let env = make_all_name_different env sigma in
  match err with
  | CantFindCaseType c -> explain_cant_find_case_type env sigma c
  | ActualTypeNotCoercible (j,t,e) ->
    let {uj_val = c; uj_type = actty} = j in
    let (env, c, actty, expty), e = contract3' env sigma c actty t e in
    let j = {uj_val = c; uj_type = actty} in
    explain_actual_type env sigma j expty (Some e)
  | UnifOccurCheck (ev,rhs) -> explain_occur_check env sigma ev rhs
  | UnsolvableImplicit (evk,exp) -> explain_unsolvable_implicit env sigma evk exp
  | VarNotFound id -> explain_var_not_found env id
  | EvarNotFound id -> explain_evar_not_found env sigma id
  | UnexpectedType (actual,expect,e) ->
    let env, actual, expect = contract2 env sigma actual expect in
    explain_unexpected_type env sigma actual expect e
  | NotProduct c -> explain_not_product env sigma c
  | CannotUnify (m,n,e) ->
    let env, m, n = contract2 env sigma m n in
    explain_cannot_unify env sigma m n e
  | CannotUnifyLocal (m,n,sn) -> explain_cannot_unify_local env sigma m n sn
  | CannotGeneralize ty -> explain_refiner_cannot_generalize env sigma ty
  | NoOccurrenceFound (c, id) -> explain_no_occurrence_found env sigma c id
  | CannotUnifyBindingType (m,n) -> explain_cannot_unify_binding_type env sigma m n
  | CannotFindWellTypedAbstraction (p,l,e) ->
      explain_cannot_find_well_typed_abstraction env sigma p l
        (Option.map (fun (env',e) -> explain_pretype_error env' sigma e) e)
  | WrongAbstractionType (n,a,t,u) ->
      explain_wrong_abstraction_type env sigma n a t u
  | AbstractionOverMeta (m,n) -> explain_abstraction_over_meta env m n
  | NonLinearUnification (m,c) -> explain_non_linear_unification env sigma m c
  | TypingError t -> explain_type_error env sigma t
  | CannotUnifyOccurrences (b,c1,c2,e) -> explain_cannot_unify_occurrences env sigma b c1 c2 e
  | UnsatisfiableConstraints (c,comp) -> explain_unsatisfiable_constraints env sigma c comp
  | DisallowedSProp -> explain_disallowed_sprop ()

(* Module errors *)

let pr_modpath mp =
  Libnames.pr_qualid (Nametab.shortest_qualid_of_module mp)

let pr_modtype_subpath upper mp =
  let rec aux mp =
    try
      let (dir,id) = Libnames.repr_qualid (Nametab.shortest_qualid_of_modtype mp) in
      Libnames.add_dirpath_suffix dir id, []
    with Not_found ->
      match mp with
      | MPdot (mp',id) -> let mp, suff = aux mp' in mp, Label.to_id id::suff
      | _ -> assert false
  in
  let mp, suff = aux mp in
  (if suff = [] then mt ()
   else str (if upper then "Module " else "module ") ++ DirPath.print (DirPath.make suff) ++ str " of ") ++
  DirPath.print mp

open Modops

let explain_not_match_error = function
  | InductiveFieldExpected _ ->
    strbrk "an inductive definition is expected"
  | DefinitionFieldExpected ->
    strbrk "a definition is expected. Hint: you can rename the \
            inductive or constructor and add a definition mapping the \
            old name to the new name"
  | ModuleFieldExpected ->
    strbrk "a module is expected"
  | ModuleTypeFieldExpected ->
    strbrk "a module type is expected"
  | NotConvertibleInductiveField id | NotConvertibleConstructorField id ->
    str "types given to " ++ Id.print id ++ str " differ"
  | NotConvertibleBodyField ->
    str "the body of definitions differs"
  | NotConvertibleTypeField (env, typ1, typ2) ->
    str "expected type" ++ spc ()  ++
    quote (Printer.safe_pr_lconstr_env env (Evd.from_env env) typ2) ++ spc () ++
    str "but found type" ++ spc () ++
    quote (Printer.safe_pr_lconstr_env env (Evd.from_env env) typ1)
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
    pr_enum (function Name id -> Id.print id | _ -> str "_") nal
  | NotEqualInductiveAliases ->
    str "Aliases to inductive types do not match"
  | CumulativeStatusExpected b ->
    let status b = if b then str"cumulative" else str"non-cumulative" in
      str "a " ++ status b ++ str" declaration was expected, but a " ++
        status (not b) ++ str" declaration was found"
  | PolymorphicStatusExpected b ->
    let status b = if b then str"polymorphic" else str"monomorphic" in
      str "a " ++ status b ++ str" declaration was expected, but a " ++
        status (not b) ++ str" declaration was found"
  | IncompatibleUniverses incon ->
    str"the universe constraints are inconsistent: " ++
      UGraph.explain_universe_inconsistency UnivNames.(pr_with_global_universes empty_binders) incon
  | IncompatiblePolymorphism (env, t1, t2) ->
    str "conversion of polymorphic values generates additional constraints: " ++
      quote (Printer.safe_pr_lconstr_env env (Evd.from_env env) t1) ++ spc () ++
      str "compared to " ++ spc () ++
      quote (Printer.safe_pr_lconstr_env env (Evd.from_env env) t2)
  | IncompatibleConstraints { got; expect } ->
      let open Univ in
    let pr_auctx auctx =
      let sigma = Evd.from_ctx
          (UState.of_binders
             (Printer.universe_binders_with_opt_names auctx None))
      in
      let uctx = AbstractContext.repr auctx in
      Printer.pr_universe_instance_constraints sigma
        (UContext.instance uctx)
        (UContext.constraints uctx)
    in
    str "incompatible polymorphic binders: got" ++ spc () ++ h (pr_auctx got) ++ spc() ++
    str "but expected" ++ spc() ++ h (pr_auctx expect) ++
    (if not (Int.equal (AbstractContext.size got) (AbstractContext.size expect)) then mt() else
       fnl() ++ str "(incompatible constraints)")
  | IncompatibleVariance ->
    str "incompatible variance information"

let explain_signature_mismatch l spec why =
  str "Signature components for field " ++ Label.print l ++
  str " do not match:" ++ spc () ++ explain_not_match_error why ++ str "."

let explain_label_already_declared l =
  str "The label " ++ Label.print l ++ str " is already declared."

let explain_not_a_functor () =
  str "Application of a non-functor."

let explain_is_a_functor mp =
  pr_modtype_subpath true mp ++ str " not expected to be a functor."

let explain_incompatible_module_types mexpr1 mexpr2 =
  let open Declarations in
  let rec get_arg = function
  | NoFunctor _ -> 0
  | MoreFunctor (_, _, ty) -> succ (get_arg ty)
  in
  let len1 = get_arg mexpr1.mod_type in
  let len2 = get_arg mexpr2.mod_type in
  if len1 <> len2 then
    str "Incompatible module types: module expects " ++ int len2 ++
      str " arguments, found " ++ int len1 ++ str "."
  else str "Incompatible module types."

let explain_not_equal_module_paths mp1 mp2 =
  str "Module " ++ pr_modpath mp1 ++ strbrk " is not equal to " ++ pr_modpath mp2 ++ str "."

let explain_no_such_label l mp =
  str "No field named " ++ Label.print l ++ str " in " ++ pr_modtype_subpath false mp ++ str "."

let explain_not_a_module_label l =
  Label.print l ++ str " is not the name of a module field."

let explain_not_a_constant l =
  quote (Label.print l) ++ str " is not a constant."

let explain_incorrect_label_constraint l =
  str "Incorrect constraint for label " ++
  quote (Label.print l) ++ str "."

let explain_generative_module_expected l =
  str "The module " ++ Label.print l ++ str " is not generative." ++
  strbrk " Only components of generative modules can be changed" ++
  strbrk " using the \"with\" construct."

let explain_label_missing l s =
  str "The field " ++ Label.print l ++ str " is missing in "
  ++ str s ++ str "."

let explain_include_restricted_functor mp =
  str "Cannot include the functor " ++ pr_modpath mp ++
  strbrk " since it has a restricted signature. " ++
  strbrk "You may name first an instance of this functor, and include it."

let explain_module_error = function
  | SignatureMismatch (l,spec,err) -> explain_signature_mismatch l spec err
  | LabelAlreadyDeclared l -> explain_label_already_declared l
  | NotAFunctor -> explain_not_a_functor ()
  | IsAFunctor mp -> explain_is_a_functor mp
  | IncompatibleModuleTypes (m1,m2) -> explain_incompatible_module_types m1 m2
  | NotEqualModulePaths (mp1,mp2) -> explain_not_equal_module_paths mp1 mp2
  | NoSuchLabel (l,mp) -> explain_no_such_label l mp
  | NotAModuleLabel l -> explain_not_a_module_label l
  | NotAConstant l -> explain_not_a_constant l
  | IncorrectWithConstraint l -> explain_incorrect_label_constraint l
  | GenerativeModuleExpected l -> explain_generative_module_expected l
  | LabelMissing (l,s) -> explain_label_missing l s
  | IncludeRestrictedFunctor mp -> explain_include_restricted_functor mp

(* Module internalization errors *)

(*
let explain_declaration_not_path _ =
  str "Declaration is not a path."

*)

let explain_not_module_nor_modtype qid =
  Libnames.pr_qualid qid ++ str " is not a module or module type."

let explain_not_a_module qid =
  Libnames.pr_qualid qid ++ str " is not a module."

let explain_not_a_module_type qid =
  Libnames.pr_qualid qid ++ str " is not a module type."

let explain_incorrect_with_in_module () =
  str "The syntax \"with\" is not allowed for modules."

let explain_incorrect_module_application () =
  str "Illegal application to a module type."

let explain_module_internalization_error = let open Modintern in function
  | NotAModuleNorModtype qid -> explain_not_module_nor_modtype qid
  | NotAModule qid -> explain_not_a_module qid
  | NotAModuleType qid -> explain_not_a_module_type qid
  | IncorrectWithInModule -> explain_incorrect_with_in_module ()
  | IncorrectModuleApplication -> explain_incorrect_module_application ()

(* Typeclass errors *)

let explain_not_a_class env sigma c =
  pr_econstr_env env sigma c ++ str" is not a declared type class."

let explain_unbound_method env sigma cid { CAst.v = id } =
  str "Unbound method name " ++ Id.print (id) ++ spc () ++
  str"of class" ++ spc () ++ pr_global cid ++ str "."

let explain_typeclass_error env sigma = function
  | NotAClass c -> explain_not_a_class env sigma c
  | UnboundMethod (cid, id) -> explain_unbound_method env sigma cid id

(* Refiner errors *)

let explain_refiner_bad_type env sigma arg ty conclty =
  let pm, pn = with_diffs (pr_lconstr_env env sigma ty) (pr_leconstr_env env sigma conclty) in
  str "Refiner was given an argument" ++ brk(1,1) ++
  pr_lconstr_env env sigma arg ++ spc () ++
  str "of type" ++ brk(1,1) ++ pm ++ spc () ++
  str "instead of" ++ brk(1,1) ++ pn ++ str "."

let explain_refiner_unresolved_bindings l =
  str "Unable to find an instance for the " ++
  str (String.plural (List.length l) "variable") ++ spc () ++
  prlist_with_sep pr_comma Name.print l ++ str"."

let explain_refiner_cannot_apply env sigma t harg =
  str "In refiner, a term of type" ++ brk(1,1) ++
  pr_lconstr_env env sigma t ++ spc () ++ str "could not be applied to" ++ brk(1,1) ++
  pr_lconstr_env env sigma harg ++ str "."

let explain_intro_needs_product () =
  str "Introduction tactics needs products."

let explain_non_linear_proof env sigma c =
  str "Cannot refine with term" ++ brk(1,1) ++ pr_lconstr_env env sigma c ++
  spc () ++ str "because a metavariable has several occurrences."

let explain_meta_in_type env sigma c =
  str "In refiner, a meta appears in the type " ++ brk(1,1) ++ pr_leconstr_env env sigma c ++
  str " of another meta"

let explain_no_such_hyp id =
  str "No such hypothesis: " ++ Id.print id

let explain_refiner_error env sigma = function
  | BadType (arg,ty,conclty) -> explain_refiner_bad_type env sigma arg ty conclty
  | UnresolvedBindings t -> explain_refiner_unresolved_bindings t
  | CannotApply (t,harg) -> explain_refiner_cannot_apply env sigma t harg
  | IntroNeedsProduct -> explain_intro_needs_product ()
  | NonLinearProof c -> explain_non_linear_proof env sigma c
  | MetaInType c -> explain_meta_in_type env sigma c
  | NoSuchHyp id -> explain_no_such_hyp id

(* Inductive errors *)

let error_non_strictly_positive env c v =
  let pc = pr_lconstr_env env (Evd.from_env env) c in
  let pv = pr_lconstr_env env (Evd.from_env env) v in
  str "Non strictly positive occurrence of " ++ pv ++ str " in" ++
  brk(1,1) ++ pc ++ str "."

let error_ill_formed_inductive env c v =
  let pc = pr_lconstr_env env (Evd.from_env env) c in
  let pv = pr_lconstr_env env (Evd.from_env env) v in
  str "Not enough arguments applied to the " ++ pv ++
  str " in" ++ brk(1,1) ++ pc ++ str "."

let error_ill_formed_constructor env id c v nparams nargs =
  let pv = pr_lconstr_env env (Evd.from_env env) v in
  let atomic = Int.equal (nb_prod Evd.empty (EConstr.of_constr c)) (* FIXME *) 0 in
  str "The type of constructor" ++ brk(1,1) ++ Id.print id ++ brk(1,1) ++
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
  quote (pr_ltype_env ~goal_concl_style:true env (Evd.from_env env) c)

let error_bad_ind_parameters env c n v1 v2  =
  let pc = pr_ltype_using_barendregt_convention_env env c in
  let pv1 = pr_lconstr_env env (Evd.from_env env) v1 in
  let pv2 = pr_lconstr_env env (Evd.from_env env) v2 in
  str "Last occurrence of " ++ pv2 ++ str " must have " ++ pv1 ++
  str " as " ++ pr_nth n ++ str " argument in" ++ brk(1,1) ++ pc ++ str "."

let error_same_names_types id =
  str "The name" ++ spc () ++ Id.print id ++ spc () ++
  str "is used more than once."

let error_same_names_constructors id =
  str "The constructor name" ++ spc () ++ Id.print id ++ spc () ++
  str "is used more than once."

let error_same_names_overlap idl =
  strbrk "The following names are used both as type names and constructor " ++
  str "names:" ++ spc () ++
  prlist_with_sep pr_comma Id.print idl ++ str "."

let error_not_an_arity env c =
  str "The type" ++ spc () ++ pr_lconstr_env env (Evd.from_env env) c ++ spc () ++
  str "is not an arity."

let error_bad_entry () =
  str "Bad inductive definition."

let error_large_non_prop_inductive_not_in_type () =
  str "Large non-propositional inductive types must be in Type."

let error_inductive_missing_constraints (us,ind_univ) =
  str "Missing universe constraint declared for inductive type:" ++ spc()
  ++ v 0 (prlist_with_sep spc (fun u ->
      hov 0 (Printer.pr_sort Evd.empty u ++ str " <= " ++ Printer.pr_sort Evd.empty ind_univ))
      us)

(* Recursion schemes errors *)

let error_not_allowed_case_analysis env isrec kind i =
  str (if isrec then "Induction" else "Case analysis") ++
  strbrk " on sort " ++ pr_sort Evd.empty kind ++
  strbrk " is not allowed for inductive definition " ++
  pr_inductive env (fst i) ++ str "."

let error_not_allowed_dependent_analysis env isrec i =
  str "Dependent " ++ str (if isrec then "induction" else "case analysis") ++
  strbrk " is not allowed for inductive definition " ++
  pr_inductive env i ++ str "."

let error_not_mutual_in_scheme env ind ind' =
  if Ind.CanOrd.equal ind ind' then
    str "The inductive type " ++ pr_inductive env ind ++
    str " occurs twice."
  else
    str "The inductive types " ++ pr_inductive env ind ++ spc () ++
    str "and" ++ spc () ++ pr_inductive env ind' ++ spc () ++
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
  | MissingConstraints csts -> error_inductive_missing_constraints csts

(* Primitive errors *)

let explain_incompatible_prim_declarations (type a) (act:a Primred.action_kind) (x:a) (y:a) =
  let open Primred in
  let env = Global.env() in
  (* The newer constant/inductive (either coming from Primitive or a
     Require) may be absent from the nametab as the error got raised
     while adding it to the safe_env. In that case we can't use
     nametab printing.

     There are still cases where the constant/inductive is added
     separately from its retroknowledge (using Register), so we still
     try nametab based printing. *)
  match act with
  | IncompatTypes typ ->
    let px = try pr_constant env x with Not_found -> Constant.print x in
    str "Cannot declare " ++ px ++ str " as primitive " ++ str (CPrimitives.prim_type_to_string typ) ++
    str ": " ++ pr_constant env y ++ str " is already declared."
  | IncompatInd ind ->
    let px = try pr_inductive env x with Not_found -> MutInd.print (fst x) in
    str "Cannot declare " ++ px ++ str " as primitive " ++ str (CPrimitives.prim_ind_to_string ind) ++
    str ": " ++ pr_inductive env y ++ str " is already declared."

(* Recursion schemes errors *)

let explain_recursion_scheme_error env = function
  | NotAllowedCaseAnalysis (isrec,k,i) ->
      error_not_allowed_case_analysis env isrec k i
  | NotMutualInScheme (ind,ind')-> error_not_mutual_in_scheme env ind ind'
  | NotAllowedDependentAnalysis (isrec, i) ->
     error_not_allowed_dependent_analysis env isrec i

(* Pattern-matching errors *)

let explain_bad_pattern env sigma cstr ty =
  let env = make_all_name_different env sigma in
  let pt = pr_leconstr_env env sigma ty in
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
  if Int.equal n 0 then str "no " ++ str s ++ str "s"
  else if Int.equal n 1 then str "1 " ++ str s
  else (int n ++ str " " ++ str s ++ str "s")

let explain_wrong_numarg_pattern expanded nargs expected_nassums expected_ndecls pp =
  (if expanded then
    strbrk "Once notations are expanded, the resulting "
  else
    strbrk "The ") ++ pp ++
  strbrk " is expected to be applied to " ++ decline_string expected_nassums "argument" ++
  (if expected_nassums = expected_ndecls then mt () else
     strbrk " (or " ++ decline_string expected_ndecls "argument" ++
     strbrk " when including variables for local definitions)") ++
  strbrk " while it is actually applied to " ++
  decline_string nargs "argument" ++ str "."

let explain_wrong_numarg_constructor env cstr expanded nargs expected_nassums expected_ndecls =
  let pp =
    strbrk "constructor " ++ pr_constructor env cstr ++
    strbrk " (in type " ++ pr_inductive env (inductive_of_constructor cstr) ++
    strbrk ")" in
  explain_wrong_numarg_pattern expanded nargs expected_nassums expected_ndecls pp

let explain_wrong_numarg_inductive env ind expanded nargs expected_nassums expected_ndecls =
  let pp = strbrk "inductive type " ++ pr_inductive env ind in
  explain_wrong_numarg_pattern expanded nargs expected_nassums expected_ndecls pp

let explain_unused_clause env pats =
  str "Pattern \"" ++ hov 0 (prlist_with_sep pr_comma pr_cases_pattern pats) ++ strbrk "\" is redundant in this clause."

let explain_non_exhaustive env pats =
  str "Non exhaustive pattern-matching: no clause found for " ++
  str (String.plural (List.length pats) "pattern") ++
  spc () ++ hov 0 (prlist_with_sep pr_comma pr_cases_pattern pats)

let explain_cannot_infer_predicate env sigma typs =
  let typs = Array.to_list typs in
  let env = make_all_name_different env sigma in
  let pr_branch (cstr,typ) =
    let cstr,_ = EConstr.decompose_app sigma cstr in
    str "For " ++ pr_leconstr_env env sigma cstr ++ str ": " ++ pr_leconstr_env env sigma typ
  in
  str "Unable to unify the types found in the branches:" ++
  spc () ++ hov 0 (prlist_with_sep fnl pr_branch typs)

let explain_pattern_matching_error env sigma = function
  | BadPattern (c,t) ->
      explain_bad_pattern env sigma c t
  | BadConstructor (c,ind) ->
      explain_bad_constructor env c ind
  | WrongNumargConstructor {cstr; expanded; nargs; expected_nassums; expected_ndecls} ->
      explain_wrong_numarg_constructor env cstr expanded nargs expected_nassums expected_ndecls
  | WrongNumargInductive {ind; expanded; nargs; expected_nassums; expected_ndecls} ->
      explain_wrong_numarg_inductive env ind expanded nargs expected_nassums expected_ndecls
  | UnusedClause tms ->
      explain_unused_clause env tms
  | NonExhaustive tms ->
      explain_non_exhaustive env tms
  | CannotInferPredicate typs ->
      explain_cannot_infer_predicate env sigma typs

let explain_reduction_tactic_error = function
  | Tacred.InvalidAbstraction (env,sigma,c,(env',e)) ->
      let e = map_ptype_error EConstr.of_constr e in
      str "The abstracted term" ++ spc () ++
      quote (pr_letype_env ~goal_concl_style:true env sigma c) ++
      spc () ++ str "is not well typed." ++ fnl () ++
      explain_type_error env' (Evd.from_env env') e

let explain_prim_token_notation_error kind env sigma = function
  | Notation.UnexpectedTerm c ->
    (strbrk "Unexpected term " ++
     pr_constr_env env sigma c ++
     strbrk (" while parsing a "^kind^" notation."))
  | Notation.UnexpectedNonOptionTerm c ->
    (strbrk "Unexpected non-option term " ++
     pr_constr_env env sigma c ++
     strbrk (" while parsing a "^kind^" notation."))

(** Registration of generic errors
    Nota: explain_exn does NOT end with a newline anymore!
*)

exception Unhandled

let wrap_unhandled f e =
  try Some (f e)
  with Unhandled -> None

let explain_exn_default = function
  (* Basic interaction exceptions *)
  | Stream.Error txt -> hov 0 (str "Syntax error: " ++ str txt ++ str ".")
  | CLexer.Error.E err -> hov 0 (str (CLexer.Error.to_string err))
  | Sys_error msg -> hov 0 (str "System error: " ++ quote (str msg))
  | Out_of_memory -> hov 0 (str "Out of memory.")
  | Stack_overflow -> hov 0 (str "Stack overflow.")
  | CErrors.Timeout -> hov 0 (str "Timeout!")
  | Sys.Break -> hov 0 (str "User interrupt.")
  (* Otherwise, not handled here *)
  | _ -> raise Unhandled

let _ = CErrors.register_handler (wrap_unhandled explain_exn_default)

let rec vernac_interp_error_handler = function
  | UGraph.UniverseInconsistency i ->
    str "Universe inconsistency." ++ spc() ++
    UGraph.explain_universe_inconsistency UnivNames.(pr_with_global_universes empty_binders) i ++ str "."
  | TypeError(ctx,te) ->
    let te = map_ptype_error EConstr.of_constr te in
    explain_type_error ctx Evd.empty te
  | PretypeError(ctx,sigma,te) ->
    explain_pretype_error ctx sigma te
  | Notation.PrimTokenNotationError(kind,ctx,sigma,te) ->
    explain_prim_token_notation_error kind ctx sigma te
  | Typeclasses_errors.TypeClassError(env, sigma, te) ->
    explain_typeclass_error env sigma te
  | InductiveError e ->
    explain_inductive_error e
  | Primred.IncompatibleDeclarations (act,x,y) ->
    explain_incompatible_prim_declarations act x y
  | Modops.ModuleTypingError e ->
    explain_module_error e
  | Modintern.ModuleInternalizationError e ->
    explain_module_internalization_error e
  | RecursionSchemeError (env,e) ->
    explain_recursion_scheme_error env e
  | Cases.PatternMatchingError (env,sigma,e) ->
    explain_pattern_matching_error env sigma e
  | Tacred.ReductionTacticError e ->
    explain_reduction_tactic_error e
  | Logic.RefinerError (env, sigma, e) ->
    explain_refiner_error env sigma e
  | Nametab.GlobalizationError q ->
    str "The reference" ++ spc () ++ Libnames.pr_qualid q ++
    spc () ++ str "was not found" ++
    spc () ++ str "in the current" ++ spc () ++ str "environment."
  | Tacticals.FailError (i,s) ->
    let s = Lazy.force s in
    str "Tactic failure" ++
    (if Pp.ismt s then s else str ": " ++ s) ++
    if Int.equal i 0 then str "." else str " (level " ++ int i ++ str")."
  | Logic_monad.TacticFailure e ->
    vernac_interp_error_handler e
  | _ ->
    raise Unhandled

let _ = CErrors.register_handler (wrap_unhandled vernac_interp_error_handler)
