(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Names
open Pp
open Term
open Tactics
open Tacticals
open Tacmach
open Coqlib
open Util
open Evd
open Printer

open Ssrmatching_plugin
open Ssrmatching
open Ssrast
open Ssrprinters
open Ssrcommon
open Ssrequality
open Ssrview
open Ssrelim
open Ssrbwd

module RelDecl = Context.Rel.Declaration
(** Extended intro patterns {{{ ***********************************************)


(* There are two ways of "applying" a view to term:            *)
(*  1- using a view hint if the view is an instance of some    *)
(*     (reflection) inductive predicate.                       *)
(*  2- applying the view if it coerces to a function, adding   *)
(*     implicit arguments.                                     *)
(* They require guessing the view hints and the number of      *)
(* implicits, respectively, which we do by brute force.        *)

let apply_type x xs = Proofview.V82.of_tactic (apply_type x xs)

let new_tac = Proofview.V82.of_tactic

let with_top tac gl =
  tac_ctx
    (tclTHENLIST [ introid top_id; tac (EConstr.mkVar top_id); new_tac (clear [top_id])])
    gl

let tclTHENS_nonstrict tac tacl taclname gl =
  let tacres = tac gl in
  let n_gls = List.length (sig_it tacres) in
  let n_tac = List.length tacl in
  if n_gls = n_tac then tclTHENS_a (fun _ -> tacres) tacl gl else
  if n_gls = 0 then tacres else
  let pr_only n1 n2 = if n1 < n2 then str "only " else mt () in
  let pr_nb n1 n2 name =
    pr_only n1 n2 ++ int n1 ++ str (" " ^ String.plural n1 name) in
  errorstrm (pr_nb n_tac n_gls taclname ++ spc ()
             ++ str "for " ++ pr_nb n_gls n_tac "subgoal")

let rec nat_of_n n =
  if n = 0 then EConstr.mkConstruct path_of_O
  else EConstr.mkApp (EConstr.mkConstruct path_of_S, [|nat_of_n (n-1)|])

let ssr_abstract_id = Summary.ref ~name:"SSR:abstractid" 0

let mk_abstract_id () = incr ssr_abstract_id; nat_of_n !ssr_abstract_id

let ssrmkabs id gl =
  let env, concl = pf_env gl, Tacmach.pf_concl gl in
  let step = begin fun sigma ->
    let (sigma, (abstract_proof, abstract_ty)) =
      let (sigma, (ty, _)) =
        Evarutil.new_type_evar env sigma Evd.univ_flexible_alg in
      let (sigma, ablock) = mkSsrConst "abstract_lock" env sigma in
      let (sigma, lock) = Evarutil.new_evar env sigma ablock in
      let (sigma, abstract) = mkSsrConst "abstract" env sigma in
      let abstract_ty = EConstr.mkApp(abstract, [|ty;mk_abstract_id ();lock|]) in
      let (sigma, m) = Evarutil.new_evar env sigma abstract_ty in
      (sigma, (m, abstract_ty)) in
    let sigma, kont =
      let rd = RelDecl.LocalAssum (Name id, abstract_ty) in
      let (sigma, ev) = Evarutil.new_evar (EConstr.push_rel rd env) sigma concl in
      (sigma, ev)
    in
(*    pp(lazy(pr_econstr concl)); *)
    let term = EConstr.(mkApp (mkLambda(Name id,abstract_ty,kont) ,[|abstract_proof|])) in
    let sigma, _ = Typing.type_of env sigma term in
    (sigma, term)
  end in
  Proofview.V82.of_tactic
    (Proofview.tclTHEN
      (Tactics.New.refine ~typecheck:false step)
      (Proofview.tclFOCUS 1 3 Proofview.shelve)) gl

let ssrmkabstac ids =
  List.fold_right (fun id tac -> tclTHENFIRST (ssrmkabs id) tac) ids tclIDTAC

(* introstac: for "move" and "clear", tclEQINTROS: for "case" and "elim" *)
(* This block hides the spaghetti-code needed to implement the only two  *)
(* tactics that should be used to process intro patters.                 *)
(* The difficulty is that we don't want to always rename, but we can     *)
(* compute needeed renamings only at runtime, so we theread a tree like  *)
(* imperativestructure so that outer renamigs are inherited by inner     *)
(* ipts and that the cler performed at the end of ipatstac clears hyps   *)
(* eventually renamed at runtime.                                        *)
let delayed_clear force rest clr gl = 
  let gl, ctx = pull_ctx gl in
  let hyps = pf_hyps gl in
  let () = if not force then List.iter (check_hyp_exists hyps) clr in
  if List.exists (fun x -> force || is_name_in_ipats (hyp_id x) rest) clr then
    let ren_clr, ren = 
      List.split (List.map (fun x ->
        let x = hyp_id x in
        let x' = mk_anon_id (Id.to_string x) gl in
        x', (x, x')) clr) in
    let ctx = { ctx with delayed_clears = ren_clr @ ctx.delayed_clears } in
    let gl = push_ctx ctx gl in
    tac_ctx (Proofview.V82.of_tactic (rename_hyp ren)) gl 
  else
    let ctx = { ctx with delayed_clears = hyps_ids clr @ ctx.delayed_clears } in
    let gl = push_ctx ctx gl in
    tac_ctx tclIDTAC gl
      
(* Common code to handle generalization lists along with the defective case *)

let with_defective maintac deps clr ist gl =
  let top_id =
    match EConstr.kind_of_type (project gl) (pf_concl gl) with
    | ProdType (Name id, _, _)
      when has_discharged_tag (Id.to_string id) -> id
    | _ -> top_id in
  let top_gen = mkclr clr, cpattern_of_id top_id in
  tclTHEN (introid top_id) (maintac deps top_gen ist) gl

let with_defective_a maintac deps clr ist gl =
  let sigma = sig_sig gl in
  let top_id =
    match EConstr.kind_of_type sigma (without_ctx pf_concl gl) with
    | ProdType (Name id, _, _)
      when has_discharged_tag (Id.to_string id) -> id
    | _ -> top_id in
  let top_gen = mkclr clr, cpattern_of_id top_id in
  tclTHEN_a (tac_ctx (introid top_id)) (maintac deps top_gen ist) gl

let with_dgens (gensl, clr) maintac ist = match gensl with
  | [deps; []] -> with_defective maintac deps clr ist
  | [deps; gen :: gens] ->
    tclTHEN (genstac (gens, clr) ist) (maintac deps gen ist)
  | [gen :: gens] -> tclTHEN (genstac (gens, clr) ist) (maintac [] gen ist)
  | _ -> with_defective maintac [] clr ist

let viewmovetac_aux ?(next=ref []) clear name_ref (_, vl as v) _ gen ist gl =
  let cl, c, clr, gl, gen_pat =
    let gl, ctx = pull_ctx gl in
    let _, gen_pat, a, b, c, ucst, gl = pf_interp_gen_aux ist gl false gen in
    a, b ,c, push_ctx ctx (pf_merge_uc ucst gl), gen_pat in
  let clr = if clear then clr else [] in
  name_ref := (match id_of_pattern gen_pat with Some id -> id | _ -> top_id);
  let clr = if clear then clr else [] in
  if vl = [] then tac_ctx (genclrtac cl [c] clr) gl
  else
    let _, _, gl =
      pfa_with_view ist ~next v cl c
        (fun cl c -> tac_ctx (genclrtac cl [c] clr)) clr gl in
      gl

let move_top_with_view ~next c r v =
  with_defective_a (viewmovetac_aux ~next c r v) [] []

type block_names = (int * EConstr.types array) option

let (introstac : ?ist:Tacinterp.interp_sign -> ssripats -> Tacmach.tactic),
    (tclEQINTROS : ?ind:block_names ref -> ?ist:Tacinterp.interp_sign ->
                     Tacmach.tactic -> Tacmach.tactic -> ssripats ->
                      Tacmach.tactic)
=

  let rec ipattac ?ist ~next p : tac_ctx tac_a = fun gl ->
(*     pp(lazy(str"ipattac: " ++ pr_ipat p)); *)
    match p with
    | IPatAnon Drop ->
        let id, gl = with_ctx new_wild_id gl in
        tac_ctx (introid id) gl
    | IPatAnon All -> tac_ctx intro_all gl
    (* TODO
    | IPatAnon Temporary ->
        let (id, orig), gl = with_ctx new_tmp_id gl in
        introid_a ~orig id gl
                     *)
    | IPatCase(iorpat) ->
        tclIORPAT ?ist (with_top (ssrscasetac false)) iorpat gl
    | IPatInj iorpat ->
        tclIORPAT ?ist (with_top (ssrscasetac true)) iorpat gl
    | IPatRewrite (occ, dir) ->
        with_top (ipat_rewrite occ dir) gl
    | IPatId id -> tac_ctx (introid id) gl
    | IPatNewHidden idl -> tac_ctx (ssrmkabstac idl) gl
    | IPatSimpl sim ->
        tac_ctx (simpltac sim) gl
    | IPatClear clr ->
        delayed_clear false !next clr gl
    | IPatAnon One -> tac_ctx intro_anon gl
    | IPatNoop -> tac_ctx tclIDTAC gl
    | IPatView v ->
        let ist =
          match ist with Some x -> x | _ -> anomaly "ipat: view with no ist" in
        let next_keeps =
          match !next with (IPatCase _ | IPatRewrite _)::_ -> false | _ -> true in
        let top_id = ref top_id in
        tclTHENLIST_a [
          (move_top_with_view ~next next_keeps top_id (next_keeps,v) ist);
          (fun gl ->
             let hyps = without_ctx pf_hyps gl in
             if not next_keeps && test_hypname_exists hyps !top_id then
               delayed_clear true !next [SsrHyp (Loc.tag !top_id)] gl
             else tac_ctx tclIDTAC gl)]
        gl

  and tclIORPAT ?ist tac = function
  | [[]] -> tac
  | orp -> tclTHENS_nonstrict tac (List.map (ipatstac ?ist) orp) "intro pattern"

  and ipatstac ?ist ipats gl =
    let rec aux ipats gl =
      match ipats with
      | [] -> tac_ctx tclIDTAC gl
      | p :: ps ->
          let next = ref ps in
          let gl = ipattac ?ist ~next p gl in
          tac_on_all gl (aux !next)
    in
      aux ipats gl
  in

  let rec split_itacs ?ist ~ind tac' = function
    | (IPatSimpl _ | IPatClear _ as spat) :: ipats' ->
        let tac = ipattac ?ist ~next:(ref ipats') spat in
        split_itacs ?ist ~ind (tclTHEN_a tac' tac) ipats'
    | IPatCase iorpat :: ipats' -> 
        tclIORPAT ?ist tac' iorpat, ipats'
    | ipats' -> tac', ipats' in

  let combine_tacs tac eqtac ipats ?ist ~ind gl =
    let tac1, ipats' = split_itacs ?ist ~ind tac ipats in
    let tac2 = ipatstac ?ist ipats' in
    tclTHENLIST_a [ tac1; eqtac; tac2 ] gl in
 
  (* Exported code *) 
  let introstac ?ist ipats gl =
    with_fresh_ctx (tclTHENLIST_a [
      ipatstac ?ist ipats;
      gen_tmp_ids ?ist;
      clear_wilds_and_tmp_and_delayed_ids
    ]) gl in
  
  let tclEQINTROS ?(ind=ref None) ?ist tac eqtac ipats gl =
    with_fresh_ctx (tclTHENLIST_a [
      combine_tacs (tac_ctx tac) (tac_ctx eqtac) ipats ?ist ~ind;
      gen_tmp_ids ?ist;
      clear_wilds_and_tmp_and_delayed_ids;
    ]) gl in

  introstac, tclEQINTROS
;;

(* Intro patterns processing for elim tactic*)
let elim_intro_tac ipats ?ist what eqid ssrelim is_rec clr gl =
  (* Utils of local interest only *)
  let iD s ?t gl = let t = match t with None -> pf_concl gl | Some x -> x in
                   ppdebug(lazy Pp.(str s ++ pr_econstr t)); Tacticals.tclIDTAC gl in
  let protectC, gl = pf_mkSsrConst "protect_term" gl in
  let eq, gl = pf_fresh_global (Coqlib.build_coq_eq ()) gl in
  let eq = EConstr.of_constr eq in
  let fire_subst gl t = Reductionops.nf_evar (project gl) t in
  let intro_eq = 
    match eqid with 
    | Some (IPatId ipat) when not is_rec -> 
       let rec intro_eq gl = match EConstr.kind_of_type (project gl) (pf_concl gl) with
         | ProdType (_, src, tgt) -> 
            (match EConstr.kind_of_type (project gl) src with
             | AtomicType (hd, _) when EConstr.eq_constr (project gl) hd protectC -> 
                Tacticals.tclTHENLIST [unprotecttac; introid ipat] gl
             | _ -> Tacticals.tclTHENLIST [ iD "IA"; Ssrcommon.intro_anon; intro_eq] gl)
         |_ -> errorstrm (Pp.str "Too many names in intro pattern") in
       intro_eq
    | Some (IPatId ipat) -> 
       let name gl = mk_anon_id "K" gl in
       let intro_lhs gl = 
         let elim_name = match clr, what with
           | [SsrHyp(_, x)], _ -> x
           | _, `EConstr(_,_,t) when EConstr.isVar (project gl) t -> EConstr.destVar (project gl) t
           | _ -> name gl in
         if is_name_in_ipats elim_name ipats then introid (name gl) gl
         else introid elim_name gl
       in
       let rec gen_eq_tac gl =
         let concl = pf_concl gl in
         let ctx, last = EConstr.decompose_prod_assum (project gl) concl in
         let args = match EConstr.kind_of_type (project gl) last with
           | AtomicType (hd, args) -> assert(EConstr.eq_constr (project gl) hd protectC); args
           | _ -> assert false in
         let case = args.(Array.length args-1) in
         if not(EConstr.Vars.closed0 (project gl) case) then Tacticals.tclTHEN Ssrcommon.intro_anon gen_eq_tac gl
         else
           let gl, case_ty = pfe_type_of gl case in 
           let refl = EConstr.mkApp (eq, [|EConstr.Vars.lift 1 case_ty; EConstr.mkRel 1; EConstr.Vars.lift 1 case|]) in
           let new_concl = fire_subst gl
                                      EConstr.(mkProd (Name (name gl), case_ty, mkArrow refl (Vars.lift 2 concl))) in 
           let erefl, gl = mkRefl case_ty case gl in
           let erefl = fire_subst gl erefl in
           apply_type new_concl [case;erefl] gl in
       Tacticals.tclTHENLIST [gen_eq_tac; intro_lhs; introid ipat]
    | _ -> Tacticals.tclIDTAC in
  let unprot = if eqid <> None && is_rec then unprotecttac else Tacticals.tclIDTAC in
  tclEQINTROS ?ist ssrelim (Tacticals.tclTHENLIST [intro_eq; unprot]) ipats gl

(* General case *)
let tclINTROS ist t ip = tclEQINTROS ~ist (t ist) tclIDTAC ip

(* }}} *)

let viewmovetac ?next v deps gen ist gl = 
 with_fresh_ctx
   (tclTHEN_a
     (viewmovetac_aux ?next true (ref top_id) v deps gen ist)
      clear_wilds_and_tmp_and_delayed_ids)
     gl

let mkCoqEq gl =
  let sigma = project gl in
  let (sigma, eq) = EConstr.fresh_global (pf_env gl) sigma (build_coq_eq_data()).eq in
  let gl = { gl with sigma } in
  eq, gl

let mkEq dir cl c t n gl =
  let open EConstr in
  let eqargs = [|t; c; c|] in eqargs.(dir_org dir) <- mkRel n;
  let eq, gl = mkCoqEq gl in
  let refl, gl = mkRefl t c gl in
  mkArrow (mkApp (eq, eqargs)) (EConstr.Vars.lift 1 cl), refl, gl

let pushmoveeqtac cl c gl =
  let open EConstr in
  let x, t, cl1 = destProd (project gl) cl in
  let cl2, eqc, gl = mkEq R2L cl1 c t 1 gl in
  apply_type (mkProd (x, t, cl2)) [c; eqc] gl

let eqmovetac _ gen ist gl =
  let cl, c, _, gl = pf_interp_gen ist gl false gen in pushmoveeqtac cl c gl

let movehnftac gl = match EConstr.kind (project gl) (pf_concl gl) with
  | Prod _ | LetIn _ -> tclIDTAC gl
  | _ -> new_tac hnf_in_concl gl

let rec eqmoveipats eqpat = function
  | (IPatSimpl _ | IPatClear _ as ipat) :: ipats -> ipat :: eqmoveipats eqpat ipats
  | (IPatAnon All :: _ | []) as ipats -> IPatAnon One :: eqpat :: ipats
   | ipat :: ipats -> ipat :: eqpat :: ipats

let ssrmovetac ist = function
  | _::_ as view, (_, (dgens, ipats)) ->
    let next = ref ipats in
    let dgentac = with_dgens dgens (viewmovetac ~next (true, view)) ist in
    tclTHEN dgentac (fun gl -> introstac ~ist !next gl)
  | _, (Some pat, (dgens, ipats)) ->
    let dgentac = with_dgens dgens eqmovetac ist in
    tclTHEN dgentac (introstac ~ist (eqmoveipats pat ipats))
  | _, (_, (([gens], clr), ipats)) ->
    let gentac = genstac (gens, clr) ist in
    tclTHEN gentac (introstac ~ist ipats)
  | _, (_, ((_, clr), ipats)) ->
    tclTHENLIST [movehnftac; cleartac clr; introstac ~ist ipats]

let ssrcasetac ist (view, (eqid, (dgens, ipats))) =
  let ndefectcasetac view eqid ipats deps ((_, occ), _ as gen) ist gl =
    let simple = (eqid = None && deps = [] && occ = None) in
    let cl, c, clr, gl = pf_interp_gen ist gl true gen in
    let _,vc, gl =
      if view = [] then c,c, gl else pf_with_view_linear ist gl (false, view) cl c in
    if simple && is_injection_case vc gl then
      tclTHENLIST [perform_injection vc; cleartac clr; introstac ~ist ipats] gl
    else 
      (* macro for "case/v E: x" ---> "case E: x / (v x)" *)
      let deps, clr, occ = 
        if view <> [] && eqid <> None && deps = [] then [gen], [], None
        else deps, clr, occ in
      ssrelim ~is_case:true ~ist deps (`EConstr (clr,occ, vc)) eqid (elim_intro_tac ipats) gl
  in
  with_dgens dgens (ndefectcasetac view eqid ipats) ist

let ssrapplytac ist (views, (_, ((gens, clr), intros))) =
  tclINTROS ist (inner_ssrapplytac views gens clr) intros


(* vim: set filetype=ocaml foldmethod=marker: *)
