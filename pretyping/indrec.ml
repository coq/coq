(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* File initially created by Christine Paulin, 1996 *)

(* This file builds various inductive schemes *)

open Pp
open CErrors
open Util
open Names
open Libnames
open Nameops
open Term
open Constr
open EConstr
open Context
open Vars
open Namegen
open Declarations
open Declareops
open Inductive
open Inductiveops
open Environ
open Reductionops
open Context.Rel.Declaration

type dep_flag = bool

(* Errors related to recursors building *)
type recursion_scheme_error =
  | NotAllowedCaseAnalysis of (*isrec:*) bool * Sorts.t * pinductive
  | NotMutualInScheme of inductive * inductive
  | NotAllowedDependentAnalysis of (*isrec:*) bool * inductive

exception RecursionSchemeError of env * recursion_scheme_error

let ident_hd env ids t na =
  let na = named_hd env (Evd.from_env env) t na in
  next_name_away na ids
let named_hd env t na = Name (ident_hd env Id.Set.empty t na)
let name_assumption env = function
| LocalAssum (na,t) -> LocalAssum (map_annot (named_hd env t) na, t)
| LocalDef (na,c,t) -> LocalDef (map_annot (named_hd env c) na, c, t)

let mkLambda_or_LetIn_name env d b = mkLambda_or_LetIn (name_assumption env d) b
let mkProd_or_LetIn_name env d b = mkProd_or_LetIn (name_assumption env d) b
let mkLambda_name env (n,a,b) = mkLambda_or_LetIn_name env (LocalAssum (n,a)) b
let mkProd_name env (n,a,b) = mkProd_or_LetIn_name env (LocalAssum (n,a)) b

module RelEnv =
struct
  type t = { env : Environ.env; avoid : Id.Set.t }

  let make env =
    let avoid = Id.Set.of_list (Termops.ids_of_rel_context (rel_context env)) in
    { env; avoid }

  let avoid_decl avoid decl = match get_name decl with
  | Anonymous -> avoid
  | Name id -> Id.Set.add id avoid

  let push_rel decl env =
    { env = EConstr.push_rel decl env.env; avoid = avoid_decl env.avoid decl }

  let push_rel_context ctx env =
    let avoid = List.fold_left avoid_decl env.avoid ctx in
    { env = EConstr.push_rel_context ctx env.env; avoid }

end

let (!!) env = env.RelEnv.env

let set_names env l =
  let ids = env.RelEnv.avoid in
  let fold d (ids, l) =
    let id = ident_hd !!env ids (get_type d) (get_name d) in
    (Id.Set.add id ids, set_name (Name id) d :: l)
  in
  snd (List.fold_right fold l (ids,[]))
let it_mkLambda_or_LetIn_name env b l = it_mkLambda_or_LetIn b (set_names env l)
let it_mkProd_or_LetIn_name env b l = it_mkProd_or_LetIn b (set_names env l)

let make_prod_dep dep env = if dep then mkProd_name env else mkProd
let make_name env s r =
  let id = next_ident_away (Id.of_string s) env.RelEnv.avoid in
  make_annot (Name id) r


(*******************************************)
(* Building curryfied elimination          *)
(*******************************************)

let check_privacy_block specif =
  if Inductive.is_private specif then
    user_err (str"case analysis on a private inductive type")

(**********************************************************************)
(* Building case analysis schemes *)
(* Christine Paulin, 1996 *)

type case_analysis = {
  case_params : EConstr.rel_context;
  case_pred : Name.t EConstr.binder_annot * EConstr.types;
  case_branches : EConstr.rel_context;
  case_arity : EConstr.rel_context;
  case_body : EConstr.t;
  case_type : EConstr.t;
}

let eval_case_analysis case =
  let open EConstr in
  let body = it_mkLambda_or_LetIn case.case_body case.case_arity in
  (* Expand let bindings in the type for backwards compatibility *)
  let bodyT = it_mkProd_wo_LetIn case.case_type case.case_arity in
  let body = it_mkLambda_or_LetIn body case.case_branches in
  let bodyT = it_mkProd_or_LetIn bodyT case.case_branches in
  let (nameP, typP) = case.case_pred in
  let body = mkLambda (nameP, typP, body) in
  let bodyT = mkProd (nameP, typP, bodyT) in
  let c = it_mkLambda_or_LetIn body case.case_params in
  let cT = it_mkProd_or_LetIn bodyT case.case_params in
  (c, cT)

(* [p] is the predicate and [cs] a constructor summary *)
let build_branch_type env sigma dep p cs =
  let open EConstr in
  let open EConstr.Vars in
  let base = mkApp (lift cs.cs_nargs p, cs.cs_concl_realargs) in
  if dep then
    Namegen.it_mkProd_or_LetIn_name env sigma
      (applist (base,[build_dependent_constructor cs]))
      cs.cs_args
  else
    it_mkProd_or_LetIn base cs.cs_args

let check_valid_elimination env sigma (ind, u as pind) ~dep s =
  let specif = Inductive.lookup_mind_specif env ind in
  let () =
    if dep && not (Inductiveops.has_dependent_elim specif) then
      raise (RecursionSchemeError (env, NotAllowedDependentAnalysis (false, ind)))
  in
  let () = check_privacy_block specif in
  match Inductiveops.make_allowed_elimination env sigma (specif,u) s with
  | Some sigma -> sigma
  | None ->
    let s = EConstr.ESorts.kind sigma s in
    let pind = on_snd EConstr.Unsafe.to_instance pind in
    raise
      (RecursionSchemeError
         (env, NotAllowedCaseAnalysis (false, s, pind)))

let mis_make_case_com dep env sigma (ind, u as pind) (mib, mip) s =
  let open EConstr in
  let sigma = check_valid_elimination env sigma pind ~dep s in
  let lnamespar = Vars.subst_instance_context u (of_rel_context mib.mind_params_ctxt) in
  let indf = make_ind_family(pind, Context.Rel.instance_list mkRel 0 lnamespar) in
  let constrs = get_constructors env indf in
  let projs = get_projections env ind in
  let relevance = Retyping.relevance_of_sort s in
  let ndepar = mip.mind_nrealdecls + 1 in

  (* Pas génant car env ne sert pas à typer mais juste à renommer les Anonym *)
  (* mais pas très joli ... (mais manque get_sort_of à ce niveau) *)
  let env = RelEnv.make env in
  let env' = RelEnv.push_rel_context lnamespar env in

  let typP = make_arity !!env' sigma dep indf s in
  let nameP = make_name env' "P" ERelevance.relevant in

  let rec get_branches env k accu =
    if Int.equal k (Array.length mip.mind_consnames) then accu
    else
      let cs = lift_constructor (k+1) constrs.(k) in
      let t = build_branch_type !!env sigma dep (mkRel (k+1)) cs in
      let namef = make_name env "f" relevance in
      let decl = LocalAssum (namef, t) in
      get_branches (RelEnv.push_rel decl env) (k + 1) (decl :: accu)
  in

  let env' = RelEnv.push_rel (LocalAssum (nameP,typP)) env' in
  let branches = get_branches env' 0 [] in

  let arity, body, bodyT =
    let env = RelEnv.push_rel_context branches env' in
    let nbprod = Array.length mip.mind_consnames + 1 in

    let indf' = lift_inductive_family nbprod indf in
    let arsign = get_arity !!env indf' in
    let r = Inductiveops.relevance_of_inductive_family !!env indf' in
    let depind = build_dependent_inductive !!env indf' in
    let deparsign = LocalAssum (make_annot Anonymous r,depind) :: arsign in

    let ci = make_case_info !!env (fst pind) RegularStyle in
    let pbody =
      mkApp
        (mkRel (ndepar + nbprod),
          if dep then Context.Rel.instance mkRel 0 deparsign
          else Context.Rel.instance mkRel 1 arsign) in
    let deparsign = set_names env deparsign in
    let pctx =
      if dep then deparsign
      else LocalAssum (make_annot Anonymous r, depind) :: List.tl deparsign
    in
    let obj, objT =
      match projs with
      | None ->
        let pms = Context.Rel.instance mkRel (ndepar + nbprod) lnamespar in
        let iv =
          if Typeops.should_invert_case !!env (ERelevance.kind sigma relevance) ci then
            CaseInvert { indices = Context.Rel.instance mkRel 1 arsign }
          else NoInvert
        in
        let ncons = Array.length mip.mind_consnames in
        let mk_branch i =
          (* we need that to get the generated names for the branch *)
          let ft = get_type (lookup_rel (ncons - i) !!env) in
          let (ctx, _) = EConstr.decompose_prod_decls sigma ft in
          let brnas = Array.of_list (List.rev_map get_annot ctx) in
          let n = mkRel (List.length ctx + ndepar + ncons - i) in
          let args = Context.Rel.instance mkRel 0 ctx in
          (brnas, mkApp (n, args))
        in
        let br = Array.init ncons mk_branch in
        let pnas = Array.of_list (List.rev_map get_annot pctx) in
        let obj = mkCase (ci, u, pms, ((pnas, liftn ndepar (ndepar + 1) pbody), relevance), iv, mkRel 1, br) in
        obj, pbody
      | Some ps ->
        let term =
          mkApp (mkRel 2,
                  Array.map
                    (fun (p,r) ->
                       let r = EConstr.Vars.subst_instance_relevance u (ERelevance.make r) in
                       mkProj (Projection.make p true, r, mkRel 1))
                    ps)
        in
        if dep then
          let ty = mkApp (mkRel 3, [| mkRel 1 |]) in
          mkCast (term, DEFAULTcast, ty), ty
        else
          term, mkRel 3
    in
    (deparsign, obj, objT)
  in
  let params = set_names env lnamespar in
  let case = {
    case_params = params;
    case_pred = (nameP, typP);
    case_branches = branches;
    case_arity = arity;
    case_body = body;
    case_type = bodyT;
  } in
  (sigma, case)

(* check if the type depends recursively on one of the inductive scheme *)

(**********************************************************************)
(* Building the recursive elimination *)
(* Christine Paulin, 1996 *)

(*
 * t is the type of the constructor co and recargs is the information on
 * the recursive calls. (It is assumed to be in form given by the user).
 * build the type of the corresponding branch of the recurrence principle
 * assuming f has this type, branch_rec gives also the term
 *   [x1]..[xk](f xi (F xi) ...) to be put in the corresponding branch of
 * the case operation
 * FPvect gives for each inductive definition if we want an elimination
 * on it with which predicate and which recursive function.
 *)

let type_rec_branch is_rec dep env sigma (vargs,depPvect,decP) (mind,tyi) cs recargs =
  let open EConstr in
  let make_prod = make_prod_dep dep in
  let nparams = List.length vargs in
  let process_pos env depK pk =
    let rec prec env i sign p =
      let p',largs = whd_allnolet_stack env sigma p in
      match kind sigma p' with
        | Prod (n,t,c) ->
            let d = LocalAssum (n,t) in
            make_prod env (n,t,prec (push_rel d env) (i+1) (d::sign) c)
        | LetIn (n,b,t,c) when List.is_empty largs ->
            let d = LocalDef (n,b,t) in
            mkLetIn (n,b,t,prec (push_rel d env) (i+1) (d::sign) c)
        | Ind (_,_) ->
            let realargs = List.skipn nparams largs in
            let base = applist (lift i pk,realargs) in
            if depK then
              Reductionops.beta_applist sigma
                (base, [applist (mkRel (i+1), Context.Rel.instance_list mkRel 0 sign)])
            else
              base
        | _ ->
           let t' = whd_all env sigma p in
           if EConstr.eq_constr sigma p' t' then assert false
           else prec env i sign t'
    in
    prec env 0 []
  in
  let rec process_constr env i c recargs nhyps li =
    if nhyps > 0 then match EConstr.kind sigma c with
      | Prod (n,t,c_0) ->
          let (optionpos,rest) =
            match recargs with
              | [] -> None,[]
              | ra::rest ->
                  (match dest_recarg ra with
                    | Mrec (RecArgInd (mind',j)) -> ((if is_rec && QMutInd.equal env mind mind' then depPvect.(j) else None),rest)
                    | Norec | Mrec (RecArgPrim _) -> (None,rest))
          in
          (match optionpos with
             | None ->
                 make_prod env
                   (n,t,
                    process_constr (push_rel (LocalAssum (n,t)) env) (i+1) c_0 rest
                      (nhyps-1) (i::li))
             | Some(dep',p) ->
                 let nP = lift (i+1+decP) p in
                 let env' = push_rel (LocalAssum (n,t)) env in
                 let t_0 = process_pos env' dep' nP (lift 1 t) in
                 let r_0 = Retyping.relevance_of_type env' sigma t_0 in
                 make_prod_dep (dep || dep') env
                   (n,t,
                    mkArrow t_0 r_0
                      (process_constr
                        (push_rel (LocalAssum (make_annot Anonymous n.binder_relevance,t_0)) env')
                         (i+2) (lift 1 c_0) rest (nhyps-1) (i::li))))
      | LetIn (n,b,t,c_0) ->
          mkLetIn (n,b,t,
                   process_constr
                     (push_rel (LocalDef (n,b,t)) env)
                     (i+1) c_0 recargs (nhyps-1) li)
      | _ -> assert false
    else
      if dep then
        let realargs = List.rev_map (fun k -> mkRel (i-k)) li in
        let params = List.map (lift i) vargs in
        let co = applist (mkConstructU cs.cs_cstr,params@realargs) in
        Reductionops.beta_applist sigma (c, [co])
      else c
  in
  let nhyps = List.length cs.cs_args in
  let nP = match depPvect.(tyi) with
    | Some(_,p) -> lift (nhyps+decP) p
    | _ -> assert false in
  let base = mkApp (nP,cs.cs_concl_realargs) in
  let c = it_mkProd_or_LetIn base cs.cs_args in
  process_constr env 0 c recargs nhyps []

let make_rec_branch_arg env sigma (nparrec,fvect,decF) mind f cstr recargs =
  let open EConstr in
  let process_pos env fk  =
    let rec prec env i hyps p =
      let p',largs = whd_allnolet_stack env sigma p in
      match kind sigma p' with
        | Prod (n,t,c) ->
            let d = LocalAssum (n,t) in
            mkLambda_name env (n,t,prec (push_rel d env) (i+1) (d::hyps) c)
        | LetIn (n,b,t,c) when List.is_empty largs ->
            let d = LocalDef (n,b,t) in
            mkLetIn (n,b,t,prec (push_rel d env) (i+1) (d::hyps) c)
        | Ind _ ->
            let realargs = List.skipn nparrec largs
            and arg = mkApp (mkRel (i+1), Context.Rel.instance mkRel 0 hyps) in
            applist(lift i fk,realargs@[arg])
        | _ ->
          let t' = whd_all env sigma p in
          if EConstr.eq_constr sigma t' p' then assert false
          else prec env i hyps t'
    in
    prec env 0 []
  in
  (* ici, cstrprods est la liste des produits du constructeur instantié *)
  let rec process_constr env i f = function
    | (LocalAssum (n,t) as d)::cprest, recarg::rest ->
        let optionpos =
          match dest_recarg recarg with
            | Norec | Mrec (RecArgPrim _) -> None
            | Mrec (RecArgInd (mind',i)) -> if QMutInd.equal env mind mind' then fvect.(i) else None
        in
        (match optionpos with
           | None ->
               let env' = push_rel d env in
               mkLambda_name env
                 (n,t,process_constr env' (i+1)
                    (whd_beta env' Evd.empty (applist (lift 1 f, [(mkRel 1)])))
                    (cprest,rest))
           | Some(_,f_0) ->
               let nF = lift (i+1+decF) f_0 in
               let env' = push_rel d env in
               let arg = process_pos env' nF (lift 1 t) in
               mkLambda_name env
                 (n,t,process_constr env' (i+1)
                    (whd_beta env' Evd.empty (applist (lift 1 f, [(mkRel 1); arg])))
                    (cprest,rest)))
    | (LocalDef (n,c,t) as d)::cprest, rest ->
        mkLetIn
          (n,c,t,
           process_constr (push_rel d env) (i+1) (lift 1 f)
             (cprest,rest))
    | [],[] -> f
    | _,[] | [],_ -> anomaly (Pp.str "process_constr.")

  in
  process_constr env 0 f (List.rev cstr.cs_args, Array.to_list recargs)

(* Main function *)
let mis_make_indrec env sigma ?(force_mutual=false) listdepkind mib u =
  let u = EConstr.Unsafe.to_instance u in
  let env = RelEnv.make env in
  let nparams = mib.mind_nparams in
  let nparrec = mib.mind_nparams_rec in
  let evdref = ref sigma in
  let lnonparrec,lnamesparrec = Inductive.inductive_nonrec_rec_paramdecls (mib,u) in
  let lnamesparrec = EConstr.of_rel_context lnamesparrec in
  let nrec = List.length listdepkind in
  let depPvec =
    Array.make mib.mind_ntypes (None : (bool * constr) option) in
  let _ =
    let rec
        assign k = function
          | [] -> ()
          | ((indi,u),mibi,mipi,dep,_)::rest ->
              (Array.set depPvec (snd indi) (Some(dep,mkRel k));
               assign (k-1) rest)
    in
      assign nrec listdepkind in
  let recargsvec =
    Array.map (fun mip -> Rtree.Kind.make mip.mind_recargs) mib.mind_packets in
  (* recarg information for non recursive parameters *)
  let rec recargparn l n =
    if Int.equal n 0 then l else recargparn (Rtree.Kind.make mk_norec::l) (n-1) in
  let recargpar = recargparn [] (nparams-nparrec) in
  let make_one_rec p =
    let makefix nbconstruct =
      let rec mrec i ln lrelevance ltyp ldef = function
        | ((indi,u),mibi,mipi,dep,target_sort)::rest ->
          let tyi = snd indi in
          let nctyi =
            Array.length mipi.mind_consnames in (* nb constructeurs du type*)

          (* arity in the context of the fixpoint, i.e.
               P1..P_nrec f1..f_nbconstruct *)
          let args = Context.Rel.instance_list mkRel (nrec+nbconstruct) lnamesparrec in
          let indf = make_ind_family((indi,u),args) in

          let arsign = get_arity !!env indf in
          let r = Inductiveops.relevance_of_inductive_family !!env indf in
          let depind = build_dependent_inductive !!env indf in
          let deparsign = LocalAssum (make_annot Anonymous r,depind)::arsign in

          let nonrecpar = Context.Rel.length lnonparrec in
          let larsign = Context.Rel.length deparsign in
          let ndepar = larsign - nonrecpar in
          let dect = larsign+nrec+nbconstruct in

            (* constructors in context of the Cases expr, i.e.
               P1..P_nrec f1..f_nbconstruct F_1..F_nrec a_1..a_nar x:I *)
            let args' = Context.Rel.instance_list mkRel (dect+nrec) lnamesparrec in
            let args'' = Context.Rel.instance_list mkRel ndepar lnonparrec in
            let indf' = make_ind_family((indi,u),args'@args'') in

            let branches =
              let constrs = get_constructors !!env indf' in
              let fi = Termops.rel_vect (dect-i-nctyi) nctyi in
              let vecfi = Array.map
                (fun f -> mkApp (EConstr.of_constr f, Context.Rel.instance mkRel ndepar lnonparrec))
                fi
              in
                Array.map3
                  (make_rec_branch_arg !!env !evdref
                      (nparrec,depPvec,larsign) (fst indi))
                  vecfi constrs (dest_subterms recargsvec.(tyi))
            in

            let j = (match depPvec.(tyi) with
              | Some (_,c) when isRel !evdref c -> destRel !evdref c
              | _ -> assert false)
            in

            (* Predicate in the context of the case *)

            let depind' = build_dependent_inductive !!env indf' in
            let arsign' = get_arity !!env indf' in
            let r = Inductiveops.relevance_of_inductive_family !!env indf' in
            let deparsign' = LocalAssum (make_annot Anonymous r,depind')::arsign' in

            let pargs =
              let nrpar = Context.Rel.instance_list mkRel (2*ndepar) lnonparrec
              and nrar = if dep then Context.Rel.instance_list mkRel 0 deparsign'
                else Context.Rel.instance_list mkRel 1 arsign'
              in nrpar@nrar

            in

            (* body of i-th component of the mutual fixpoint *)
            let target_relevance = Retyping.relevance_of_sort target_sort in
            let deftyi =
              let ci = make_case_info !!env indi RegularStyle in
              let concl = applist (mkRel (dect+j+ndepar),pargs) in
              let pred =
                it_mkLambda_or_LetIn_name env
                  ((if dep then mkLambda_name !!env else mkLambda)
                      (make_annot Anonymous r,depind',concl))
                  arsign'
              in
              let obj =
                let indty = find_rectype !!env sigma depind in
                Inductiveops.make_case_or_project !!env !evdref indty ci
                  (pred, target_relevance)
                  (EConstr.mkRel 1) branches
              in
                it_mkLambda_or_LetIn_name env obj
                  (lift_rel_context nrec deparsign)
            in

            (* type of i-th component of the mutual fixpoint *)

            let typtyi =
              let concl =
                let pargs = if dep then Context.Rel.instance mkRel 0 deparsign
                  else Context.Rel.instance mkRel 1 arsign
                in mkApp (mkRel (nbconstruct+ndepar+nonrecpar+j),pargs)
              in it_mkProd_or_LetIn_name env
                concl
                deparsign
            in
              mrec (i+nctyi) (Context.Rel.nhyps arsign ::ln) (target_relevance::lrelevance) (typtyi::ltyp)
                (deftyi::ldef) rest
        | [] ->
            let fixn = Array.of_list (List.rev ln) in
            let fixtyi = Array.of_list (List.rev ltyp) in
            let fixdef = Array.of_list (List.rev ldef) in
            let lrelevance = CArray.rev_of_list lrelevance in
            let names = Array.map (fun r -> make_annot (Name(Id.of_string "F")) r) lrelevance in
              mkFix ((fixn,p),(names,fixtyi,fixdef))
      in
        mrec 0 [] [] [] []
    in
    let rec make_branch env i = function
      | ((indi,u),mibi,mipi,dep,sfam)::rest ->
          let tyi = snd indi in
          let nconstr = Array.length mipi.mind_consnames in
          let rec onerec env j =
            if Int.equal j nconstr then
              make_branch env (i+j) rest
            else
              let recarg = Array.to_list (dest_subterms recargsvec.(tyi)).(j) in
              let recarg = recargpar@recarg in
              let vargs = Context.Rel.instance_list mkRel (nrec+i+j) lnamesparrec in
              let cs = get_constructor ((indi,u),mibi,mipi,vargs) (j+1) in
              let p_0 =
                type_rec_branch
                  true dep !!env !evdref (vargs,depPvec,i+j) indi cs recarg
              in
              let r_0 = Retyping.relevance_of_sort sfam in
              let namef = make_name env "f" r_0 in
                mkLambda (namef, p_0,
                  (onerec (RelEnv.push_rel (LocalAssum (namef,p_0)) env)) (j+1))
          in onerec env 0
      | [] ->
          makefix i listdepkind
    in
    let rec put_arity env i = function
      | ((indi,u),_,_,dep,s)::rest ->
          let indf = make_ind_family ((indi,u), Context.Rel.instance_list mkRel i lnamesparrec) in
          let typP = make_arity !!env !evdref dep indf s in
          let nameP = make_name env "P" ERelevance.relevant in
            mkLambda (nameP,typP,
              (put_arity (RelEnv.push_rel (LocalAssum (nameP,typP)) env)) (i+1) rest)
      | [] ->
          make_branch env 0 listdepkind
    in

    (* Body on make_one_rec *)
    let ((indi,u),mibi,mipi,dep,kind) = List.nth listdepkind p in

      if force_mutual || (mis_is_recursive_subset !!env
        (List.map (fun ((indi,u),_,_,_,_) -> indi) listdepkind)
        (Rtree.Kind.make mipi.mind_recargs))
      then
        let env' = RelEnv.push_rel_context lnamesparrec env in
          it_mkLambda_or_LetIn_name env (put_arity env' 0 listdepkind)
            lnamesparrec
      else
        let evd = !evdref in
        let (evd, c) = mis_make_case_com dep !!env evd (indi,u) (mibi,mipi) kind in
        let (c, _) = eval_case_analysis c in
          evdref := evd; c
  in
    (* Body of mis_make_indrec *)
    !evdref, List.init nrec make_one_rec

(**********************************************************************)
(* This builds elimination predicate for Case tactic *)

let build_case_analysis_scheme env sigma pity dep kind =
  let specif = lookup_mind_specif env (fst pity) in
  mis_make_case_com dep env sigma pity specif kind

let prop_but_default_dependent_elim =
  Summary.ref ~name:"prop_but_default_dependent_elim" Indset_env.empty

let inPropButDefaultDepElim : inductive -> Libobject.obj =
  Libobject.declare_object @@
  Libobject.superglobal_object "prop_but_default_dependent_elim"
    ~cache:(fun i ->
        prop_but_default_dependent_elim := Indset_env.add i !prop_but_default_dependent_elim)
    ~subst:(Some (fun (subst,i) -> Mod_subst.subst_ind subst i))
    ~discharge:(fun i -> Some i)

let declare_prop_but_default_dependent_elim i =
  Lib.add_leaf (inPropButDefaultDepElim i)

let is_prop_but_default_dependent_elim i = Indset_env.mem i !prop_but_default_dependent_elim

let pseudo_sort_family_for_elim ind mip =
  let s = mip.mind_sort in
  if Sorts.is_prop s && is_prop_but_default_dependent_elim ind then InType
  else Sorts.family s

let is_in_prop mip =
  let s = mip.mind_sort in
  Sorts.is_prop s

let default_case_analysis_dependence env ind =
  let _, mip as specif = lookup_mind_specif env ind in
  Inductiveops.has_dependent_elim specif
  && (not (is_in_prop mip) || is_prop_but_default_dependent_elim ind)

let build_case_analysis_scheme_default env sigma pity kind =
  let dep = default_case_analysis_dependence env (fst pity) in
  build_case_analysis_scheme env sigma pity dep kind

(**********************************************************************)
(* Interface to build complex Scheme *)
(* Check inductive types only occurs once
(otherwise we obtain a meaning less scheme) *)

let check_arities env sigma listdepkind =
  let _ = List.fold_left
     (fun ln (((_,ni as mind),u),mibi,mipi,dep,s) ->
       if not @@ Inductiveops.is_allowed_elimination sigma ((mibi,mipi),u) s then
        let s = ESorts.kind sigma s in
        let u = EInstance.kind sigma u in
        raise
         (RecursionSchemeError
          (env, NotAllowedCaseAnalysis (true, s,(mind,u))))
       else if Int.List.mem ni ln then raise
         (RecursionSchemeError (env, NotMutualInScheme (mind,mind)))
       else ni::ln)
            [] listdepkind
  in true

let build_mutual_induction_scheme env sigma ?(force_mutual=false) = function
  | ((mind,u),dep,s)::lrecspec ->
      let mib, mip as specif = lookup_mind_specif env mind in
      if dep && not (Inductiveops.has_dependent_elim specif) then
        raise (RecursionSchemeError (env, NotAllowedDependentAnalysis (true, mind)));
      let (sp,tyi) = mind in
      let listdepkind =
        ((mind,u),mib,mip,dep,s)::
        (List.map
           (function ((mind',u'),dep',s') ->
              let (sp',_) = mind' in
              if QMutInd.equal env sp sp' then
                let (mibi',mipi') = lookup_mind_specif env mind' in
                ((mind',u'),mibi',mipi',dep',s')
              else
                raise (RecursionSchemeError (env, NotMutualInScheme (mind,mind'))))
           lrecspec)
      in
      let _ = check_arities env sigma listdepkind in
      mis_make_indrec env sigma ~force_mutual listdepkind mib u
  | _ -> anomaly (Pp.str "build_induction_scheme expects a non empty list of inductive types.")

let build_induction_scheme env sigma pind dep kind =
  let (mib,mip) as specif = lookup_mind_specif env (fst pind) in
  if dep && not (Inductiveops.has_dependent_elim specif) then
    raise (RecursionSchemeError (env, NotAllowedDependentAnalysis (true, fst pind)));
  let sigma, l = mis_make_indrec env sigma [(pind,mib,mip,dep,kind)] mib (snd pind) in
    sigma, List.hd l

(*s Eliminations. *)

let elimination_suffix = function
  | InSProp -> "_sind"
  | InProp -> "_ind"
  | InSet  -> "_rec"
  | InType | InQSort -> "_rect"

let case_suffix = "_case"

let make_elimination_ident id s = add_suffix id (elimination_suffix s)

(* Look up function for the default elimination constant *)

let lookup_eliminator env ind_sp s =
  let kn,i = ind_sp in
  let mpu = KerName.modpath @@ MutInd.user kn in
  let mpc = KerName.modpath @@ MutInd.canonical kn in
  let ind_id = (lookup_mind kn env).mind_packets.(i).mind_typename in
  let id = add_suffix ind_id (elimination_suffix s) in
  let l = Label.of_id id in
  let knu = KerName.make mpu l in
  let knc = KerName.make mpc l in
  (* Try first to get an eliminator defined in the same section as the *)
  (* inductive type *)
  let cst = Constant.make knu knc in
  if mem_constant cst env then GlobRef.ConstRef cst
  else
    (* Then try to get a user-defined eliminator in some other places *)
    (* using short name (e.g. for "eq_rec") *)
    try Nametab.locate (qualid_of_ident id)
    with Not_found ->
      user_err
        (strbrk "Cannot find the elimination combinator " ++
         Id.print id ++ strbrk ", the elimination of the inductive definition " ++
         Nametab.pr_global_env Id.Set.empty (GlobRef.IndRef ind_sp) ++
         strbrk " on sort " ++ Sorts.pr_sort_family s ++
         strbrk " is probably not allowed.")
