(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Constr
open Termops
open EConstr
open Inductiveops
open Constr_matching
open Rocqlib
open Declarations
open Context.Rel.Declaration

module RelDecl = Context.Rel.Declaration

(* I implemented the following functions which test whether a term t
   is an inductive but non-recursive type, a general conjunction, a
   general disjunction, or a type with no constructors.

   They are more general than matching with or_term, and_term, etc,
   since they do not depend on the name of the type. Hence, they
   also work on ad-hoc disjunctions introduced by the user.

  -- Eduardo (6/8/97). *)

type 'a matching_function = Environ.env -> Evd.evar_map -> EConstr.constr -> 'a option

type testing_function  = Environ.env -> Evd.evar_map -> EConstr.constr -> bool

let mkmeta n = Nameops.make_ident "X" (Some n)
let meta1 = mkmeta 1
let meta2 = mkmeta 2

let match_with_non_recursive_type env sigma t =
  match EConstr.kind sigma t with
    | App _ ->
        let (hdapp,args) = decompose_app_list sigma t in
        (match EConstr.kind sigma hdapp with
           | Ind (ind,u) ->
               if (Environ.lookup_mind (fst ind) env).mind_finite == CoFinite then
                 Some (hdapp,args)
               else
                 None
           | _ -> None)
    | _ -> None

let is_non_recursive_type env sigma t = Option.has_some (match_with_non_recursive_type env sigma t)

(* Test dependencies *)

(* NB: we consider also the let-in case in the following function,
   since they may appear in types of inductive constructors (see #2629) *)

let rec has_nodep_prod_after n env sigma c =
  match EConstr.kind sigma c with
    | Prod (_,_,b) | LetIn (_,_,_,b) ->
        ( n>0 || Vars.noccurn sigma 1 b)
        && (has_nodep_prod_after (n-1) env sigma b)
    | _            -> true

let has_nodep_prod env sigma c = has_nodep_prod_after 0 env sigma c

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

(* whd_beta normalize the types of arguments in a product *)
let rec whd_beta_prod env sigma c = match EConstr.kind sigma c with
  | Prod (n,t,c) -> mkProd (n,Reductionops.whd_beta env sigma t,whd_beta_prod env sigma c)
  | LetIn (n,d,t,c) -> mkLetIn (n,d,t,whd_beta_prod env sigma c)
  | _ -> c

let match_with_one_constructor env sigma style onlybinary allow_rec t =
  let (hdapp,args) = decompose_app_list sigma t in
  let res = match EConstr.kind sigma hdapp with
  | Ind ind ->
      let (mib,mip) = Inductive.lookup_mind_specif env (fst ind) in
      if Int.equal (Array.length mip.mind_consnames) 1
        && (allow_rec || not (mis_is_recursive env (fst ind, mib, mip)))
        && (Int.equal mip.mind_nrealargs 0)
      then
        if is_strict_conjunction style (* strict conjunction *) then
          let (ctx, _) = mip.mind_nf_lc.(0) in
          let ctx = List.skipn (Context.Rel.length mib.mind_params_ctxt) (List.rev ctx) in
          if
            (* Constructor has a type of the form
              c : forall (a_0 ... a_n : Type) (x_0 : A_0) ... (x_n : A_n). T **)
            List.for_all
              (fun decl -> let c = RelDecl.get_type decl in
                           is_local_assum decl &&
                           Constr.isRel c &&
                           Int.equal (Constr.destRel c) mib.mind_nparams) ctx
          then
            Some (hdapp,args)
          else None
        else
          let ctx, cty = mip.mind_nf_lc.(0) in
          let cty = EConstr.of_constr (Term.it_mkProd_or_LetIn cty ctx) in
          let ctyp = whd_beta_prod env sigma
            (Termops.prod_applist_decls sigma (Context.Rel.length mib.mind_params_ctxt) cty args) in
          let cargs = List.map RelDecl.get_type (EConstr.prod_decls sigma ctyp) in
          if not (is_lax_conjunction style) || has_nodep_prod env sigma ctyp then
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

let match_with_conjunction ?(strict=false) ?(onlybinary=false) env sigma t =
  match_with_one_constructor env sigma (Some strict) onlybinary false t

let match_with_record env sigma t =
  match_with_one_constructor env sigma None false false t

let is_conjunction ?(strict=false) ?(onlybinary=false) env sigma t =
  Option.has_some (match_with_conjunction env sigma ~strict ~onlybinary t)

let is_record env sigma t =
  Option.has_some (match_with_record env sigma t)

let match_with_tuple env sigma t =
  let t = match_with_one_constructor env sigma None false true t in
  Option.map (fun (hd,l) ->
    let ind, _ = destInd sigma hd in
    let (mib,mip) = Inductive.lookup_mind_specif env ind in
    let isrec = mis_is_recursive env (ind, mib, mip) in
    (hd,l,isrec)) t

let is_tuple env sigma t =
  Option.has_some (match_with_tuple env sigma t)

(* A general disjunction type is a non-recursive with-no-indices inductive
   type with of which all constructors have a single argument;
   it is strict if it has the form
   "Inductive I A1 ... An := C1 (_:A1) | ... | Cn : (_:An)" *)

let test_strict_disjunction (mib, mip) =
  let n = List.length mib.mind_params_ctxt in
  let check i (ctx, _) = match List.skipn n (List.rev ctx) with
  | [LocalAssum (_, c)] -> Constr.isRel c && Int.equal (Constr.destRel c) (n - i)
  | _ -> false
  in
  Array.for_all_i check 0 mip.mind_nf_lc

let match_with_disjunction ?(strict=false) ?(onlybinary=false) env sigma t =
  let (hdapp,args) = decompose_app_list sigma t in
  let res = match EConstr.kind sigma hdapp with
  | Ind (ind,u)  ->
      let car = constructors_nrealargs env ind in
      let (mib,mip) = Inductive.lookup_mind_specif env ind in
      if Array.for_all (fun ar -> Int.equal ar 1) car
      && not (mis_is_recursive env (ind, mib, mip))
      && (Int.equal mip.mind_nrealargs 0)
      then
        if strict then
          if test_strict_disjunction (mib, mip) then
            Some (hdapp,args)
          else
            None
        else
          let map (ctx, cty) =
            let ar = EConstr.of_constr (Term.it_mkProd_or_LetIn cty ctx) in
            pi2 (destProd sigma (prod_applist sigma ar args))
          in
          let cargs = Array.map map mip.mind_nf_lc in
          Some (hdapp,Array.to_list cargs)
      else
        None
  | _ -> None in
  match res with
  | Some (hdapp,args) when not onlybinary -> res
  | Some (hdapp,[_; _]) -> res
  | _ -> None

let is_disjunction ?(strict=false) ?(onlybinary=false) env sigma t =
  Option.has_some (match_with_disjunction ~strict ~onlybinary env sigma t)

(* An empty type is an inductive type, possible with indices, that has no
   constructors *)

let match_with_empty_type env sigma t =
  let (hdapp,args) = decompose_app sigma t in
  match EConstr.kind sigma hdapp with
    | Ind (ind, _) ->
        let (mib,mip) = Inductive.lookup_mind_specif env ind in
        let nconstr = Array.length mip.mind_consnames in
        if Int.equal nconstr 0 then Some hdapp else None
    | _ ->  None

let is_empty_type env sigma t = Option.has_some (match_with_empty_type env sigma t)

(* This filters inductive types with one constructor with no arguments;
   Parameters and indices are allowed *)

let match_with_unit_or_eq_type env sigma t =
  let (hdapp,args) = decompose_app sigma t in
  match EConstr.kind sigma hdapp with
    | Ind (ind , _) ->
        let (mib,mip) = Inductive.lookup_mind_specif env ind in
        let nconstr = Array.length mip.mind_consnames in
        if Int.equal nconstr 1 && Int.equal mip.mind_consnrealargs.(0) 0 then
          Some hdapp
        else
          None
    | _ -> None

let is_unit_or_eq_type env sigma t = Option.has_some (match_with_unit_or_eq_type env sigma t)

(* A unit type is an inductive type with no indices but possibly
   (useless) parameters, and that has no arguments in its unique
   constructor *)

let is_unit_type env sigma t =
  match match_with_conjunction env sigma t with
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

open Pattern

let mkPRel n = PRel n
let mkPApp f args = PApp (f, Array.of_list args)
let mkPHole = PMeta None
let mkPProd id c1 c2 = PProd (Name (Id.of_string id), c1, c2)
let mkPArrow c1 c2 = PProd (Anonymous, c1, c2)
let mkPPatVar id = PMeta (Some (Id.of_string id))
let mkPRef r = PRef (lib_ref r)
let mkPAppRef r args = mkPApp (mkPRef r) args

(** forall x : _, _ x x *)
let rocq_refl_leibniz1_pattern =
  mkPProd "x" mkPHole (mkPApp mkPHole [mkPRel 1; mkPRel 1])

(** forall A:_, forall x:A, _ A x x *)
let rocq_refl_leibniz2_pattern =
  mkPProd "A" mkPHole (mkPProd "x" (mkPRel 1)
    (mkPApp mkPHole [mkPRel 2; mkPRel 1; mkPRel 1]))

(** forall A:_, forall x:A, _ A x A x *)
let rocq_refl_jm_pattern       =
  mkPProd "A" mkPHole (mkPProd "x" (mkPRel 1)
    (mkPApp mkPHole [mkPRel 2; mkPRel 1; mkPRel 2; mkPRel 1]))

let match_with_equation env sigma t =
  if not (isApp sigma t) then raise NoEquationFound;
  let (hdapp,args) = destApp sigma t in
  match EConstr.kind sigma hdapp with
  | Ind (ind,u) ->
    (try
      let gr = GlobRef.IndRef ind in
       if Rocqlib.check_ref "core.eq.type" gr then
         Some (build_rocq_eq_data()),hdapp,
         PolymorphicLeibnizEq(args.(0),args.(1),args.(2))
       else if Rocqlib.check_ref "core.identity.type" gr then
         Some (build_rocq_identity_data()),hdapp,
         PolymorphicLeibnizEq(args.(0),args.(1),args.(2))
       else if Rocqlib.check_ref "core.JMeq.type" gr then
         Some (build_rocq_jmeq_data()),hdapp,
         HeterogenousEq(args.(0),args.(1),args.(2),args.(3))
       else
         let (mib,mip) = Inductive.lookup_mind_specif env ind in
         let constr_types = mip.mind_nf_lc in
         let nconstr = Array.length mip.mind_consnames in
         if Int.equal nconstr 1 then
           let (ctx, cty) = constr_types.(0) in
           let cty = EConstr.of_constr (Term.it_mkProd_or_LetIn cty ctx) in
           if is_matching env sigma rocq_refl_leibniz1_pattern cty then
             None, hdapp, MonomorphicLeibnizEq(args.(0),args.(1))
           else if is_matching env sigma rocq_refl_leibniz2_pattern cty then
             None, hdapp, PolymorphicLeibnizEq(args.(0),args.(1),args.(2))
           else if is_matching env sigma rocq_refl_jm_pattern cty then
             None, hdapp, HeterogenousEq(args.(0),args.(1),args.(2),args.(3))
           else raise NoEquationFound
         else raise NoEquationFound
     with UserError _ ->
       raise NoEquationFound)
  | _ -> raise NoEquationFound

(* Note: An "equality type" is any type with a single argument-free
   constructor: it captures eq, eq_dep, JMeq, eq_true, etc. but also
   True/unit which is the degenerate equality type (isomorphic to ()=());
   in particular, True/unit are provable by "reflexivity" *)

let is_inductive_equality env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let nconstr = Array.length mip.mind_consnames in
  Int.equal nconstr 1 && Int.equal (constructor_nrealargs env (ind,1)) 0

let match_with_equality_type env sigma t =
  let (hdapp,args) = decompose_app_list sigma t in
  match EConstr.kind sigma hdapp with
  | Ind (ind,_) when is_inductive_equality env ind -> Some (hdapp,args)
  | _ -> None

let is_equality_type env sigma t = Option.has_some (match_with_equality_type env sigma t)

(* Arrows/Implication/Negation *)

(** X1 -> X2 **)
let rocq_arrow_pattern = mkPArrow (mkPPatVar "X1") (mkPPatVar "X2")

let match_arrow_pattern env sigma t =
  let result = matches env sigma rocq_arrow_pattern t in
  match Id.Map.bindings result with
    | [(m1,arg);(m2,mind)] ->
      assert (Id.equal m1 meta1 && Id.equal m2 meta2); (arg, mind)
    | _ -> anomaly (Pp.str "Incorrect pattern matching.")

let match_with_imp_term env sigma c =
  match EConstr.kind sigma c with
    | Prod (_,a,b) when Vars.noccurn sigma 1 b -> Some (a,b)
    | _              -> None

let is_imp_term env sigma c = Option.has_some (match_with_imp_term env sigma c)

let match_with_nottype env sigma t =
  try
    let (arg,mind) = match_arrow_pattern env sigma t in
    if is_empty_type env sigma mind then Some (mind,arg) else None
  with PatternMatchingFailure -> None

let is_nottype env sigma t = Option.has_some (match_with_nottype env sigma t)

(* Forall *)

let match_with_forall_term env sigma c =
  match EConstr.kind sigma c with
    | Prod (nam,a,b) -> Some (nam,a,b)
    | _            -> None

let is_forall_term env sigma c = Option.has_some (match_with_forall_term env sigma c)

let match_with_nodep_ind env sigma t =
  let (hdapp,args) = decompose_app_list sigma t in
  match EConstr.kind sigma hdapp with
  | Ind (ind, _)  ->
     let (mib,mip) = Inductive.lookup_mind_specif env ind in
     if Array.length (mib.mind_packets)>1 then None else
       let nodep_constr (ctx, cty) =
        let c = EConstr.of_constr (Term.it_mkProd_or_LetIn cty ctx) in
         has_nodep_prod_after (Context.Rel.length mib.mind_params_ctxt) env sigma c in
       if Array.for_all nodep_constr mip.mind_nf_lc then
         let params=
           if Int.equal mip.mind_nrealargs 0 then args else
             fst (List.chop mib.mind_nparams args) in
         Some (hdapp,params,mip.mind_nrealargs)
       else
         None
  | _ -> None

let is_nodep_ind env sigma t = Option.has_some (match_with_nodep_ind env sigma t)

let match_with_sigma_type env sigma t =
  let (hdapp,args) = decompose_app_list sigma t in
  match EConstr.kind sigma hdapp with
  | Ind (ind, _) ->
     let (mib,mip) = Inductive.lookup_mind_specif env ind in
     if Int.equal (Array.length (mib.mind_packets)) 1
        && (Int.equal mip.mind_nrealargs 0)
        && (Int.equal (Array.length mip.mind_consnames)1)
        && has_nodep_prod_after (Context.Rel.length mib.mind_params_ctxt + 1) env sigma
             (let (ctx, cty) = mip.mind_nf_lc.(0) in EConstr.of_constr (Term.it_mkProd_or_LetIn cty ctx))
     then
       (*allowing only 1 existential*)
       Some (hdapp,args)
     else
       None
  | _ -> None

let is_sigma_type env sigma t = Option.has_some (match_with_sigma_type env sigma t)

(***** Destructing patterns bound to some theory *)

let rec first_match matcher = function
  | [] -> raise PatternMatchingFailure
  | (pat,check,build_set)::l when check () ->
      (try (build_set (),matcher pat)
       with PatternMatchingFailure -> first_match matcher l)
  | _::l -> first_match matcher l

(*** Equality *)

let match_eq env sigma eqn (ref, hetero) =
  let ref =
    try Lazy.force ref
    with e when CErrors.noncritical e -> raise PatternMatchingFailure
  in
  match EConstr.kind sigma eqn with
  | App (c, [|t; x; y|]) ->
    if not hetero && isRefX env sigma ref c then PolymorphicLeibnizEq (t, x, y)
    else raise PatternMatchingFailure
  | App (c, [|t; x; t'; x'|]) ->
    if hetero && isRefX env sigma ref c then HeterogenousEq (t, x, t', x')
    else raise PatternMatchingFailure
  | _ -> raise PatternMatchingFailure

let no_check () = true
let check_jmeq_loaded () = has_ref "core.JMeq.type"

let equalities =
  [(lazy(lib_ref "core.eq.type"), false), no_check, build_rocq_eq_data;
   (lazy(lib_ref "core.JMeq.type"), true), check_jmeq_loaded, build_rocq_jmeq_data;
   (lazy(lib_ref "core.identity.type"), false), no_check, build_rocq_identity_data]

let find_eq_data env sigma eqn = (* fails with PatternMatchingFailure *)
  let d,k = first_match (match_eq env sigma eqn) equalities in
  let hd,u = destInd sigma (fst (destApp sigma eqn)) in
    d,u,k

let extract_eq_args env sigma = function
  | MonomorphicLeibnizEq (e1,e2) ->
      let t = Retyping.get_type_of env sigma e1 in (t,e1,e2)
  | PolymorphicLeibnizEq (t,e1,e2) -> (t,e1,e2)
  | HeterogenousEq (t1,e1,t2,e2) ->
      if Reductionops.is_conv env sigma t1 t2 then (t1,e1,e2)
      else raise PatternMatchingFailure

let find_eq_data_decompose env sigma eqn =
  let (lbeq,u,eq_args) = find_eq_data env sigma eqn in
  (lbeq,u,extract_eq_args env sigma eq_args)

let find_this_eq_data_decompose env sigma eqn =
  let (lbeq,u,eq_args) =
    try (*first_match (match_eq eqn) inversible_equalities*)
      find_eq_data env sigma eqn
    with PatternMatchingFailure ->
      user_err  (str "No primitive equality found.") in
  let eq_args =
    try extract_eq_args env sigma eq_args
    with PatternMatchingFailure ->
      user_err Pp.(str "Don't know what to do with JMeq on arguments not of same type.") in
  (lbeq,u,eq_args)

(*** Sigma-types *)

let match_sigma_data env sigma ex =
  match EConstr.kind sigma ex with
  | App (f, [| a; p; car; cdr |]) when is_lib_ref env sigma "core.sig.intro" f ->
      build_sigma (), (snd (destConstruct sigma f), a, p, car, cdr)
  | App (f, [| a; p; car; cdr |]) when is_lib_ref env sigma "core.sigT.intro" f ->
    build_sigma_type (), (snd (destConstruct sigma f), a, p, car, cdr)
  | _ -> raise PatternMatchingFailure

let find_sigma_data_decompose env ex = (* fails with PatternMatchingFailure *)
  match_sigma_data env ex

(* Pattern "(sig ?1 ?2)" *)
let rocq_sig_pattern =
  lazy (mkPAppRef "core.sig.type" [mkPPatVar "X1"; mkPPatVar "X2"])

let match_sigma env sigma t =
  match Id.Map.bindings (matches env sigma (Lazy.force rocq_sig_pattern) t) with
    | [(_,a); (_,p)] -> (a,p)
    | _ -> anomaly (Pp.str "Unexpected pattern.")

let is_matching_sigma env sigma t = is_matching env sigma (Lazy.force rocq_sig_pattern) t

(*** Decidable equalities *)

(* The expected form of the goal for the tactic Decide Equality *)

(* Pattern "{<?1>x=y}+{~(<?1>x=y)}" *)
(* i.e. "(sumbool (eq ?1 x y) ~(eq ?1 x y))" *)

let rocq_eqdec ~sum ~rev =
  lazy (
    let eqn = mkPAppRef "core.eq.type" (List.map mkPPatVar ["X1"; "X2"; "X3"]) in
    let args = [eqn; mkPAppRef "core.not.type" [eqn]] in
    let args = if rev then List.rev args else args in
    mkPAppRef sum args
  )

let sumbool_type = "core.sumbool.type"
let or_type = "core.or.type"

(** [{ ?X2 = ?X3 :> ?X1 } + { ~ ?X2 = ?X3 :> ?X1 }] *)
let rocq_eqdec_inf_pattern = rocq_eqdec ~sum:sumbool_type ~rev:false

(** [{ ~ ?X2 = ?X3 :> ?X1 } + { ?X2 = ?X3 :> ?X1 }] *)
let rocq_eqdec_inf_rev_pattern = rocq_eqdec ~sum:sumbool_type ~rev:true

(** %rocq_or_ref (?X2 = ?X3 :> ?X1) (~ ?X2 = ?X3 :> ?X1) *)
let rocq_eqdec_pattern = rocq_eqdec ~sum:or_type ~rev:false

(** %rocq_or_ref (~ ?X2 = ?X3 :> ?X1) (?X2 = ?X3 :> ?X1) *)
let rocq_eqdec_rev_pattern = rocq_eqdec ~sum:or_type ~rev:true

let match_eqdec env sigma t =
  let eqonleft,op,subst =
    try true,sumbool_type,matches env sigma (Lazy.force rocq_eqdec_inf_pattern) t
    with PatternMatchingFailure ->
    try false,sumbool_type,matches env sigma (Lazy.force rocq_eqdec_inf_rev_pattern) t
    with PatternMatchingFailure ->
    try true,or_type,matches env sigma (Lazy.force rocq_eqdec_pattern) t
    with PatternMatchingFailure ->
        false,or_type,matches env sigma (Lazy.force rocq_eqdec_rev_pattern) t in
  match Id.Map.bindings subst with
  | [(_,typ);(_,c1);(_,c2)] ->
      eqonleft, lib_ref op, c1, c2, typ
  | _ -> anomaly (Pp.str "Unexpected pattern.")

(* Patterns "~ ?" and "? -> False" *)
let rocq_not_pattern = lazy (mkPAppRef "core.not.type" [mkPHole])
let rocq_imp_False_pattern = lazy (mkPArrow mkPHole (mkPRef "core.False.type"))

let is_matching_not env sigma t = is_matching env sigma (Lazy.force rocq_not_pattern) t
let is_matching_imp_False env sigma t = is_matching env sigma (Lazy.force rocq_imp_False_pattern) t

(* Remark: patterns that have references to the standard library must
   be evaluated lazily (i.e. at the time they are used, not a the time
   coqtop starts) *)

let is_homogeneous_relation ?loc env sigma rel =
  let relty = Retyping.get_type_of env sigma rel in
  let error () =
    user_err ?loc
      (Printer.pr_econstr_env env sigma rel ++ str " is not a homogeneous binary relation.")
  in
  let ctx, ar =
    try Reductionops.whd_decompose_prod_n env sigma 2 relty
    with Invalid_argument _ -> error () in
  match ctx, EConstr.kind sigma ar with
  | [(_,t); (_,u)], Sort s
    when Sorts.is_prop (ESorts.kind sigma s) && Reductionops.is_conv env sigma t u -> t
  | _, _ -> error ()
