(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ssrmatching_plugin

open Util
open Names
open Constr

open Proofview
open Proofview.Notations

open Ssrast

module IpatMachine : sig

  (* the => tactical.  ?eqtac is a tactic to be eventually run
   * after the first [..] block.  first_case_is_dispatch is the
   * ssr exception to elim: and case: *)
  val main : ?eqtac:unit tactic -> first_case_is_dispatch:bool ->
        ssripats -> unit tactic

end = struct (* {{{ *)

module State : sig

  (* to_clear API *)
  val isCLR_PUSH    : Id.t -> unit tactic
  val isCLR_PUSHL   : Id.t list -> unit tactic
  val isCLR_CONSUME : unit tactic

  (* Some data may expire *)
  val isTICK : ssripat -> unit tactic

  val isPRINT : Proofview.Goal.t -> Pp.t

end = struct (* {{{ *)

type istate = {

  (* Delayed clear *)
  to_clear : Id.t list;

}

let empty_state = {
  to_clear = [];
}

include Ssrcommon.MakeState(struct
  type state = istate
  let init = empty_state
end)

let isPRINT g =
  let state = get g in
  Pp.(str"{{ to_clear: " ++
        prlist_with_sep spc Id.print state.to_clear ++ spc () ++
      str" }}")


let isCLR_PUSH id =
  tclGET (fun { to_clear = ids } ->
  tclSET { to_clear = id :: ids })

let isCLR_PUSHL more_ids =
  tclGET (fun { to_clear = ids } ->
  tclSET { to_clear = more_ids @ ids })

let isCLR_CONSUME =
  tclGET (fun { to_clear = ids } ->
  tclSET { to_clear = [] } <*>
  Tactics.clear ids)


let isTICK _ = tclUNIT ()

end (* }}} *************************************************************** *)

open State

(** [=> *] ****************************************************************)
(** [nb_assums] returns the number of dependent premises *)
(** Warning: unlike [nb_deps_assums], it does not perform reduction *)
let rec nb_assums cur env sigma t =
  match EConstr.kind sigma t with
  | Prod(name,ty,body) ->
     nb_assums (cur+1) env sigma body
  | LetIn(name,ty,t1,t2) ->
    nb_assums (cur+1) env sigma t2
  | Cast(t,_,_) ->
     nb_assums cur env sigma t
  | _ -> cur
let nb_assums = nb_assums 0

let intro_anon_all = Goal.enter begin fun gl ->
  let env = Goal.env gl in
  let sigma = Goal.sigma gl in
  let g = Goal.concl gl in
  let n = nb_assums env sigma g in
  Tacticals.New.tclDO n Ssrcommon.tclINTRO_ANON
end

(** [intro_drop] behaves like [intro_anon] but registers the id of the
    introduced assumption for a delayed clear. *)
let intro_drop =
  Ssrcommon.tclINTRO ~id:None
    ~conclusion:(fun ~orig_name:_ ~new_name -> isCLR_PUSH new_name)

(** [intro_end] performs the actions that have been delayed. *)
let intro_end =
  Ssrcommon.tcl0G (isCLR_CONSUME)

(** [=> _] *****************************************************************)
let intro_clear ids =
  Goal.enter begin fun gl ->
    let _, clear_ids, ren =
      List.fold_left (fun (used_ids, clear_ids, ren) id ->
            let new_id = Ssrcommon.mk_anon_id (Id.to_string id) used_ids in
            (new_id :: used_ids, new_id :: clear_ids, (id, new_id) :: ren))
                     (Tacmach.New.pf_ids_of_hyps gl, [], []) ids
    in
    Tactics.rename_hyp ren <*>
    isCLR_PUSHL clear_ids
end

let tacCHECK_HYPS_EXIST hyps = Goal.enter begin fun gl ->
  let ctx = Goal.hyps gl in
  List.iter (Ssrcommon.check_hyp_exists ctx) hyps;
  tclUNIT ()
end

(** [=> []] *****************************************************************)
let tac_case t =
  Goal.enter begin fun _ ->
    Ssrcommon.tacTYPEOF t >>= fun ty ->
    Ssrcommon.tacIS_INJECTION_CASE ~ty t >>= fun is_inj ->
    if is_inj then
      V82.tactic ~nf_evars:false (Ssrelim.perform_injection t)
    else
      Ssrelim.ssrscasetac t
end

(** [=> [: id]] ************************************************************)
let mk_abstract_id =
  let open Coqlib in
  let ssr_abstract_id = Summary.ref ~name:"SSR:abstractid" 0 in
begin fun () ->
  let rec nat_of_n n =
    if n = 0 then EConstr.mkConstruct path_of_O
    else EConstr.mkApp (EConstr.mkConstruct path_of_S, [|nat_of_n (n-1)|]) in
  incr ssr_abstract_id; nat_of_n !ssr_abstract_id
end

let tcltclMK_ABSTRACT_VAR id = Goal.enter begin fun gl ->
  let env, concl = Goal.(env gl, concl gl) in
  let step = begin fun sigma ->
    let (sigma, (abstract_proof, abstract_ty)) =
      let (sigma, (ty, _)) =
        Evarutil.new_type_evar env sigma Evd.univ_flexible_alg in
      let (sigma, ablock) = Ssrcommon.mkSsrConst "abstract_lock" env sigma in
      let (sigma, lock) = Evarutil.new_evar env sigma ablock in
      let (sigma, abstract) = Ssrcommon.mkSsrConst "abstract" env sigma in
      let abstract_ty =
        EConstr.mkApp(abstract, [|ty;mk_abstract_id ();lock|]) in
      let sigma, m = Evarutil.new_evar env sigma abstract_ty in
      sigma, (m, abstract_ty) in
    let sigma, kont =
      let rd = Context.Rel.Declaration.LocalAssum (Name id, abstract_ty) in
      let sigma, ev = Evarutil.new_evar (EConstr.push_rel rd env) sigma concl in
      sigma, ev
    in
    let term =
      EConstr.(mkApp (mkLambda(Name id,abstract_ty,kont),[|abstract_proof|])) in
    let sigma, _ = Typing.type_of env sigma term in
    sigma, term
  end in
  Tactics.New.refine ~typecheck:false step <*>
  tclFOCUS 1 3 Proofview.shelve
end

let tclMK_ABSTRACT_VARS ids =
  List.fold_right (fun id tac ->
    Tacticals.New.tclTHENFIRST (tcltclMK_ABSTRACT_VAR id) tac) ids (tclUNIT ())

(* Debugging *)
let tclLOG p t =
  tclUNIT () >>= begin fun () ->
    Ssrprinters.ppdebug (lazy Pp.(str "exec: " ++ Ssrprinters.pr_ipat p));
    tclUNIT ()
  end <*>
  Goal.enter begin fun g ->
    Ssrprinters.ppdebug (lazy Pp.(str" on state:" ++ spc () ++
      isPRINT g ++
      str" goal:" ++ spc () ++ Printer.pr_goal (Goal.print g)));
    tclUNIT ()
  end
  <*>
    t p
  <*>
  Goal.enter begin fun g ->
    Ssrprinters.ppdebug (lazy Pp.(str "done: " ++ isPRINT g));
    tclUNIT ()
  end

let rec ipat_tac1 ipat : unit tactic =
  match ipat with
  | IPatView (clear_if_id,l) ->
      Ssrview.tclIPAT_VIEWS ~views:l ~clear_if_id
        ~conclusion:(fun ~to_clear:clr -> intro_clear clr)

  | IPatDispatch(true,[[]]) ->
      tclUNIT ()
  | IPatDispatch(_,ipatss) ->
      tclDISPATCH (List.map ipat_tac ipatss)

  | IPatId id -> Ssrcommon.tclINTRO_ID id

  | IPatCase ipatss ->
     tclIORPAT (Ssrcommon.tclWITHTOP tac_case) ipatss
  | IPatInj ipatss ->
     tclIORPAT (Ssrcommon.tclWITHTOP
       (fun t -> V82.tactic  ~nf_evars:false (Ssrelim.perform_injection t)))
       ipatss

  | IPatAnon Drop -> intro_drop
  | IPatAnon One -> Ssrcommon.tclINTRO_ANON
  | IPatAnon All -> intro_anon_all

  | IPatNoop -> tclUNIT ()
  | IPatSimpl Nop -> tclUNIT ()

  | IPatClear ids ->
      tacCHECK_HYPS_EXIST ids <*>
      intro_clear (List.map Ssrcommon.hyp_id ids)

  | IPatSimpl (Simpl n) ->
       V82.tactic ~nf_evars:false (Ssrequality.simpltac (Simpl n))
  | IPatSimpl (Cut n) ->
       V82.tactic ~nf_evars:false (Ssrequality.simpltac (Cut n))
  | IPatSimpl (SimplCut (n,m)) ->
       V82.tactic ~nf_evars:false (Ssrequality.simpltac (SimplCut (n,m)))

  | IPatRewrite (occ,dir) ->
     Ssrcommon.tclWITHTOP
       (fun x -> V82.tactic  ~nf_evars:false (Ssrequality.ipat_rewrite occ dir x))

  | IPatAbstractVars ids -> tclMK_ABSTRACT_VARS ids

  | IPatTac t -> t

and ipat_tac pl : unit tactic =
  match pl with
  | [] -> tclUNIT ()
  | pat :: pl ->
      Ssrcommon.tcl0G (tclLOG pat ipat_tac1) <*>
      isTICK pat <*>
      ipat_tac pl

and tclIORPAT tac = function
  | [[]] -> tac
  | p -> Tacticals.New.tclTHENS tac (List.map ipat_tac p)

let split_at_first_case ipats =
  let rec loop acc = function
    | (IPatSimpl _ | IPatClear _) as x :: rest -> loop (x :: acc) rest
    | IPatCase _ as x :: xs -> CList.rev acc, Some x, xs
    | pats -> CList.rev acc, None, pats
  in
    loop [] ipats

let ssr_exception is_on = function
  | Some (IPatCase l) when is_on -> Some (IPatDispatch(true, l))
  | x -> x

let option_to_list = function None -> [] | Some x -> [x]

(* Simple pass doing {x}/v ->  /v{x} *)
let elaborate_ipats l =
  let rec elab = function
  | [] -> []
  | (IPatClear _ as p1) :: (IPatView _ as p2) :: rest -> p2 :: p1 :: elab rest
  | IPatDispatch(s,p) :: rest -> IPatDispatch (s,List.map elab p) :: elab rest
  | IPatCase p :: rest -> IPatCase (List.map elab p) :: elab rest
  | IPatInj p :: rest -> IPatInj (List.map elab p) :: elab rest
  | (IPatTac _ | IPatId _ | IPatSimpl _ | IPatClear _ |
     IPatAnon _ | IPatView _ | IPatNoop | IPatRewrite _ |
     IPatAbstractVars _) as x :: rest -> x :: elab rest
  in
    elab l

let main ?eqtac ~first_case_is_dispatch ipats =
  let ipats = elaborate_ipats ipats in
  let ip_before, case, ip_after = split_at_first_case ipats in
  let case = ssr_exception first_case_is_dispatch case in
  let case = option_to_list case in
  let eqtac = option_to_list (Option.map (fun x -> IPatTac x) eqtac) in
  Ssrcommon.tcl0G (ipat_tac (ip_before @ case @ eqtac @ ip_after) <*> intro_end)

end (* }}} *)

let tclIPAT_EQ eqtac ip =
  Ssrprinters.ppdebug (lazy Pp.(str "ipat@run: " ++ Ssrprinters.pr_ipats ip));
  IpatMachine.main ~eqtac ~first_case_is_dispatch:true ip

let tclIPATssr ip =
  Ssrprinters.ppdebug (lazy Pp.(str "ipat@run: " ++ Ssrprinters.pr_ipats ip));
  IpatMachine.main ~first_case_is_dispatch:true ip

(* Common code to handle generalization lists along with the defective case *)
let with_defective maintac deps clr = Goal.enter begin fun g ->
  let sigma, concl = Goal.(sigma g, concl g) in
  let top_id =
    match EConstr.kind_of_type sigma concl with
    | Term.ProdType (Name id, _, _)
      when Ssrcommon.is_discharged_id id -> id
    | _ -> Ssrcommon.top_id in
  let top_gen = Ssrequality.mkclr clr, Ssrmatching.cpattern_of_id top_id in
  Ssrcommon.tclINTRO_ID top_id <*> maintac deps top_gen
end

let with_dgens { dgens; gens; clr } maintac = match gens with
  | [] -> with_defective maintac dgens clr
  | gen :: gens ->
      V82.tactic ~nf_evars:false (Ssrcommon.genstac (gens, clr)) <*> maintac dgens gen

let mkCoqEq env sigma =
  let eq = Coqlib.((build_coq_eq_data ()).eq) in
  let sigma, eq = EConstr.fresh_global env sigma eq in
  eq, sigma

let mkCoqRefl t c env sigma =
  let refl = Coqlib.((build_coq_eq_data()).refl) in
  let sigma, refl = EConstr.fresh_global env sigma refl in
  EConstr.mkApp (refl, [|t; c|]), sigma

(** Intro patterns processing for elim tactic, in particular when used in
    conjunction with equation generation as in [elim E: x] *)
let elim_intro_tac ipats ?ist what eqid ssrelim is_rec clr =
  let intro_eq =
    match eqid with
    | Some (IPatId ipat) when not is_rec ->
       let rec intro_eq () = Goal.enter begin fun g ->
         let sigma, env, concl = Goal.(sigma g, env g, concl g) in
         match EConstr.kind_of_type sigma concl with
         | Term.ProdType (_, src, tgt) -> begin
             match EConstr.kind_of_type sigma src with
             | Term.AtomicType (hd, _) when Ssrcommon.is_protect hd env sigma ->
                V82.tactic ~nf_evars:false Ssrcommon.unprotecttac <*>
                Ssrcommon.tclINTRO_ID ipat
             | _ -> Ssrcommon.tclINTRO_ANON <*> intro_eq ()
             end
         |_ -> Ssrcommon.errorstrm (Pp.str "Too many names in intro pattern")
       end in
       intro_eq ()
    | Some (IPatId ipat) ->
       let intro_lhs = Goal.enter begin fun g ->
         let sigma = Goal.sigma g in
         let elim_name = match clr, what with
           | [SsrHyp(_, x)], _ -> x
           | _, `EConstr(_,_,t) when EConstr.isVar sigma t ->
              EConstr.destVar sigma t
           | _ -> Ssrcommon.mk_anon_id "K" (Tacmach.New.pf_ids_of_hyps g) in
         let elim_name =
           if Ssrcommon.is_name_in_ipats elim_name ipats then
             Ssrcommon.mk_anon_id "K" (Tacmach.New.pf_ids_of_hyps g)
           else elim_name
         in
         Ssrcommon.tclINTRO_ID elim_name
       end in
       let rec gen_eq_tac () = Goal.enter begin fun g ->
         let sigma, env, concl = Goal.(sigma g, env g, concl g) in
         let sigma, eq =
           EConstr.fresh_global env sigma (Coqlib.build_coq_eq ()) in
         let ctx, last = EConstr.decompose_prod_assum sigma concl in
         let args = match EConstr.kind_of_type sigma last with
           | Term.AtomicType (hd, args) ->
               if Ssrcommon.is_protect hd env sigma then args
               else Ssrcommon.errorstrm
                  (Pp.str "Too many names in intro pattern")
           | _ -> assert false in
         let case = args.(Array.length args-1) in
         if not(EConstr.Vars.closed0 sigma case)
         then Ssrcommon.tclINTRO_ANON <*> gen_eq_tac ()
         else
           Ssrcommon.tacTYPEOF case >>= fun case_ty ->
           let open EConstr in
           let refl =
             mkApp (eq, [|Vars.lift 1 case_ty; mkRel 1; Vars.lift 1 case|]) in
           let name = Ssrcommon.mk_anon_id "K" (Tacmach.New.pf_ids_of_hyps g) in

           let new_concl =
             mkProd (Name name, case_ty, mkArrow refl (Vars.lift 2 concl)) in
           let erefl, sigma = mkCoqRefl case_ty case env sigma in
           Proofview.Unsafe.tclEVARS sigma <*>
           Tactics.apply_type ~typecheck:true new_concl [case;erefl]
       end in
       gen_eq_tac () <*>
       intro_lhs <*>
       Ssrcommon.tclINTRO_ID ipat
    | _ -> tclUNIT () in
  let unprot =
    if eqid <> None && is_rec
    then V82.tactic ~nf_evars:false Ssrcommon.unprotecttac else tclUNIT () in
  V82.of_tactic begin
    V82.tactic ~nf_evars:false ssrelim <*>
    tclIPAT_EQ (intro_eq <*> unprot) ipats
  end

let mkEq dir cl c t n env sigma =
  let open EConstr in
  let eqargs = [|t; c; c|] in
  eqargs.(Ssrequality.dir_org dir) <- mkRel n;
  let eq, sigma = mkCoqEq env sigma in
  let refl, sigma = mkCoqRefl t c env sigma in
  mkArrow (mkApp (eq, eqargs)) (Vars.lift 1 cl), refl, sigma

(** in [tac/v: last gens..] the first (last to be run) generalization is
    "special" in that is it also the main argument of [tac] and is eventually
    to be processed forward with view [v]. The behavior implemented is
    very close to [tac: (v last) gens..] but:
    - [v last] may use a view adaptor
    - eventually clear for [last] is taken into account
    - [tac/v {clr}] is also supported, and [{clr}] is to be run later
    The code here does not "grab" [v last] nor apply [v] to [last], see the
    [tacVIEW_THEN_GRAB] combinator. *)
let tclLAST_GEN ~to_ind ((oclr, occ), t) conclusion = tclINDEPENDENTL begin
  Ssrcommon.tacSIGMA >>= fun sigma0 ->
  Goal.enter_one begin fun g ->
  let pat = Ssrmatching.interp_cpattern sigma0 t None in
  let cl0, env, sigma, hyps = Goal.(concl g, env g, sigma g, hyps g) in
  let cl = EConstr.to_constr ~abort_on_undefined_evars:false sigma cl0 in
  let (c, ucst), cl =
    try Ssrmatching.fill_occ_pattern ~raise_NoMatch:true env sigma cl pat occ 1
    with Ssrmatching.NoMatch -> Ssrmatching.redex_of_pattern env pat, cl in
  let sigma = Evd.merge_universe_context sigma ucst in
  let c, cl = EConstr.of_constr c, EConstr.of_constr cl in
  let clr =
    Ssrcommon.interp_clr sigma (oclr, (Ssrmatching.tag_of_cpattern t,c)) in
  (* Historically in Coq, and hence in ssr, [case t] accepts [t] of type
     [A.. -> Ind] and opens new goals for [A..] as well as for the branches
     of [Ind], see the [~to_ind] argument *)
  if not(Termops.occur_existential sigma c) then
    if Ssrmatching.tag_of_cpattern t = Ssrprinters.xWithAt then
      if not (EConstr.isVar sigma c) then
        Ssrcommon.errorstrm Pp.(str "@ can be used with variables only")
      else match Context.Named.lookup (EConstr.destVar sigma c) hyps with
      | Context.Named.Declaration.LocalAssum _ ->
          Ssrcommon.errorstrm Pp.(str "@ can be used with let-ins only")
      | Context.Named.Declaration.LocalDef (name, b, ty) ->
          Unsafe.tclEVARS sigma <*>
          tclUNIT (true, EConstr.mkLetIn (Name name,b,ty,cl), c, clr)
    else
      Unsafe.tclEVARS sigma <*>
      Ssrcommon.tacMKPROD c cl >>= fun ccl ->
      tclUNIT (false, ccl, c, clr)
  else
    if to_ind && occ = None then
      let _, p, _, ucst' =
        (* TODO: use abs_evars2 *)
        Ssrcommon.pf_abs_evars sigma0 (fst pat, c) in
      let sigma = Evd.merge_universe_context sigma ucst' in
      Unsafe.tclEVARS sigma <*>
      Ssrcommon.tacTYPEOF p >>= fun pty ->
      (* TODO: check bug: cl0 no lift? *)
      let ccl = EConstr.mkProd (Ssrcommon.constr_name sigma c, pty, cl0) in
      tclUNIT (false, ccl, p, clr)
  else
    Ssrcommon.errorstrm Pp.(str "generalized term didn't match")
end end >>= begin
  fun infos -> tclDISPATCH (infos |> List.map conclusion)
end

(** a typical mate of [tclLAST_GEN] doing the job of applying the views [cs]
    to [c] and generalizing the resulting term *)
let tacVIEW_THEN_GRAB ?(simple_types=true)
  vs ~conclusion (is_letin, new_concl, c, clear)
=
  Ssrview.tclWITH_FWD_VIEWS ~simple_types ~subject:c ~views:vs
  ~conclusion:(fun t ->
    Ssrcommon.tacCONSTR_NAME c >>= fun name ->
    Goal.enter_one ~__LOC__ begin fun g ->
      let sigma, env = Goal.sigma g, Goal.env g in
      Ssrcommon.tacMKPROD t ~name
        (Termops.subst_term sigma t (* NOTE: we grab t here *)
          (Termops.prod_applist sigma new_concl [c])) >>=
      conclusion is_letin t clear
    end)

(* Elim views are elimination lemmas, so the eliminated term is not added *)
(* to the dependent terms as for "case", unless it actually occurs in the  *)
(* goal, the "all occurrences" {+} switch is used, or the equation switch  *)
(* is used and there are no dependents.                                    *)

let ssrelimtac (view, (eqid, (dgens, ipats))) =
  let ndefectelimtac view eqid ipats deps gen =
    match view with
    | [v] ->
      Ssrcommon.tclINTERP_AST_CLOSURE_TERM_AS_CONSTR v >>= fun cs ->
      tclDISPATCH (List.map (fun elim ->
        V82.tactic ~nf_evars:false
          (Ssrelim.ssrelim deps (`EGen gen) ~elim eqid (elim_intro_tac ipats)))
        cs)
    | [] ->
      tclINDEPENDENT
        (V82.tactic ~nf_evars:false
          (Ssrelim.ssrelim deps (`EGen gen) eqid (elim_intro_tac ipats)))
    | _ ->
      Ssrcommon.errorstrm
        Pp.(str "elim: only one elimination lemma can be provided")
  in
  with_dgens dgens (ndefectelimtac view eqid ipats)

let ssrcasetac (view, (eqid, (dgens, ipats))) =
  let ndefectcasetac view eqid ipats deps ((_, occ), _ as gen) =
    tclLAST_GEN ~to_ind:true gen (fun (_, cl, c, clear as info) ->
      let conclusion _ vc _clear _cl =
        Ssrcommon.tacIS_INJECTION_CASE vc >>= fun inj ->
        let simple = (eqid = None && deps = [] && occ = None) in
        if simple && inj then
          V82.tactic ~nf_evars:false (Ssrelim.perform_injection vc) <*>
          Tactics.clear (List.map Ssrcommon.hyp_id clear) <*>
          tclIPATssr ipats
        else
        (* macro for "case/v E: x" ---> "case E: x / (v x)" *)
          let deps, clear, occ =
            if view <> [] && eqid <> None && deps = []
            then [gen], [], None
            else deps, clear, occ in
          V82.tactic ~nf_evars:false
            (Ssrelim.ssrelim ~is_case:true deps (`EConstr (clear, occ, vc))
              eqid (elim_intro_tac ipats))
      in
      if view = [] then conclusion false c clear c
      else tacVIEW_THEN_GRAB ~simple_types:false view ~conclusion info)
  in
  with_dgens dgens (ndefectcasetac view eqid ipats)

let ssrscasetoptac = Ssrcommon.tclWITHTOP Ssrelim.ssrscase_or_inj_tac
let ssrselimtoptac = Ssrcommon.tclWITHTOP Ssrelim.elimtac

(** [move] **************************************************************)
let pushmoveeqtac cl c = Goal.enter begin fun g ->
  let env, sigma = Goal.(env g, sigma g) in
  let x, t, cl1 = EConstr.destProd sigma cl in
  let cl2, eqc, sigma = mkEq R2L cl1 c t 1 env sigma in
  Unsafe.tclEVARS sigma <*>
  Tactics.apply_type ~typecheck:true (EConstr.mkProd (x, t, cl2)) [c; eqc]
end

let eqmovetac _ gen = Goal.enter begin fun g ->
  Ssrcommon.tacSIGMA >>= fun gl ->
  let cl, c, _, gl = Ssrcommon.pf_interp_gen gl false gen in
  Unsafe.tclEVARS (Tacmach.project gl) <*>
  pushmoveeqtac cl c
end

let rec eqmoveipats eqpat = function
  | (IPatSimpl _ | IPatClear _ as ipat) :: ipats ->
       ipat :: eqmoveipats eqpat ipats
  | (IPatAnon All :: _ | []) as ipats ->
       IPatAnon One :: eqpat :: ipats
  | ipat :: ipats ->
       ipat :: eqpat :: ipats

let ssrsmovetac = Goal.enter begin fun g ->
  let sigma, concl = Goal.(sigma g, concl g) in
  match EConstr.kind sigma concl with
  | Prod _ | LetIn _ -> tclUNIT ()
  | _ -> Tactics.hnf_in_concl
end

let tclIPAT ip =
  Ssrprinters.ppdebug (lazy Pp.(str "ipat@run: " ++ Ssrprinters.pr_ipats ip));
  IpatMachine.main ~first_case_is_dispatch:false ip

let ssrmovetac = function
  | _::_ as view, (_, ({ gens = lastgen :: gens; clr }, ipats)) ->
     let gentac = V82.tactic ~nf_evars:false (Ssrcommon.genstac (gens, [])) in
     let conclusion _ t clear ccl =
       Tactics.apply_type ~typecheck:true ccl [t] <*>
       Tactics.clear (List.map Ssrcommon.hyp_id clear) in
     gentac <*>
     tclLAST_GEN ~to_ind:false lastgen
       (tacVIEW_THEN_GRAB view ~conclusion) <*>
     tclIPAT (IPatClear clr :: ipats)
  | _::_ as view, (_, ({ gens = []; clr }, ipats)) ->
     tclIPAT (IPatView (false,view) :: IPatClear clr :: ipats)
  | _, (Some pat, (dgens, ipats)) ->
    let dgentac = with_dgens dgens eqmovetac in
    dgentac <*> tclIPAT (eqmoveipats pat ipats)
  | _, (_, ({ gens = (_ :: _ as gens); dgens = []; clr}, ipats)) ->
    let gentac = V82.tactic ~nf_evars:false (Ssrcommon.genstac (gens, clr)) in
    gentac <*> tclIPAT ipats
  | _, (_, ({ clr }, ipats)) ->
    Tacticals.New.tclTHENLIST [ssrsmovetac; Tactics.clear (List.map Ssrcommon.hyp_id clr); tclIPAT ipats]

(** [abstract: absvar gens] **************************************************)
let rec is_Evar_or_CastedMeta sigma x =
  EConstr.isEvar sigma x ||
  EConstr.isMeta sigma x ||
  (EConstr.isCast sigma x &&
    is_Evar_or_CastedMeta sigma (pi1 (EConstr.destCast sigma x)))

let occur_existential_or_casted_meta sigma c =
  let rec occrec c = match EConstr.kind sigma c with
    | Evar _ -> raise Not_found
    | Cast (m,_,_) when EConstr.isMeta sigma m -> raise Not_found
    | _ -> EConstr.iter sigma occrec c
  in
  try occrec c; false
  with Not_found -> true

let tacEXAMINE_ABSTRACT id = Ssrcommon.tacTYPEOF id >>= begin fun tid ->
  Ssrcommon.tacMK_SSR_CONST "abstract" >>= fun abstract ->
  Goal.enter_one ~__LOC__ begin fun g ->
  let sigma, env = Goal.(sigma g, env g) in
  let err () =
    Ssrcommon.errorstrm
      Pp.(strbrk"not a proper abstract constant: "++
        Printer.pr_econstr_env env sigma id) in
  if not (EConstr.isApp sigma tid) then err ();
  let hd, args_id = EConstr.destApp sigma tid in
  if not (EConstr.eq_constr_nounivs sigma hd abstract) then err ();
  if Array.length args_id <> 3 then err ();
  if not (is_Evar_or_CastedMeta sigma args_id.(2)) then
    Ssrcommon.errorstrm Pp.(strbrk"abstract constant "++
      Printer.pr_econstr_env env sigma id++str" already used");
  tclUNIT (tid, args_id)
end end

let tacFIND_ABSTRACT_PROOF check_lock abstract_n =
  Ssrcommon.tacMK_SSR_CONST "abstract" >>= fun abstract ->
  Goal.enter_one ~__LOC__ begin fun g ->
    let sigma, env = Goal.(sigma g, env g) in
    let l = Evd.fold_undefined (fun e ei l ->
      match EConstr.kind sigma ei.Evd.evar_concl with
      | App(hd, [|ty; n; lock|])
        when (not check_lock ||
                   (occur_existential_or_casted_meta sigma ty &&
                    is_Evar_or_CastedMeta sigma lock)) &&
             EConstr.eq_constr_nounivs sigma hd abstract &&
             EConstr.eq_constr_nounivs sigma n abstract_n -> e :: l
      | _ -> l) sigma [] in
    match l with
    | [e] -> tclUNIT e
    | _ -> Ssrcommon.errorstrm
       Pp.(strbrk"abstract constant "++
         Printer.pr_econstr_env env sigma abstract_n ++
           strbrk" not found in the evar map exactly once. "++
           strbrk"Did you tamper with it?")
end

let ssrabstract dgens =
  let main _ (_,cid) = Goal.enter begin fun g ->
    Ssrcommon.tacMK_SSR_CONST "abstract" >>= fun abstract ->
    Ssrcommon.tacMK_SSR_CONST "abstract_key" >>= fun abstract_key ->
    Ssrcommon.tacINTERP_CPATTERN cid >>= fun cid ->
    let id = EConstr.mkVar (Option.get (Ssrmatching.id_of_pattern cid)) in
    tacEXAMINE_ABSTRACT id >>= fun (idty, args_id) ->
    let abstract_n = args_id.(1) in
    tacFIND_ABSTRACT_PROOF true abstract_n >>= fun abstract_proof ->
    let tacFIND_HOLE = Goal.enter_one ~__LOC__ begin fun g ->
      let sigma, env, concl = Goal.(sigma g, env g, concl g) in
      let t = args_id.(0) in
      match EConstr.kind sigma t with
      | (Evar _ | Meta _) -> Ssrcommon.tacUNIFY concl t <*> tclUNIT id
      | Cast(m,_,_)
        when EConstr.isEvar sigma m || EConstr.isMeta sigma m ->
          Ssrcommon.tacUNIFY concl t <*> tclUNIT id
      | _ ->
          Ssrcommon.errorstrm
            Pp.(strbrk"abstract constant "++
               Printer.pr_econstr_env env sigma abstract_n ++
               strbrk" has an unexpected shape. Did you tamper with it?")
      end in
    tacFIND_HOLE >>= fun proof ->
    Ssrcommon.tacUNIFY abstract_key args_id.(2) <*>
    Ssrcommon.tacTYPEOF idty >>= fun _ ->
    Unsafe.tclGETGOALS >>= fun goals ->
    (* Here we jump in the proof tree: we move from the current goal to
       the evar that inhabits the abstract variable with the current goal *)
    Unsafe.tclSETGOALS
      (goals @ [Proofview_monad.with_empty_state abstract_proof]) <*>
    tclDISPATCH [
      Tacticals.New.tclSOLVE [Tactics.apply proof];
      Ssrcommon.unfold[abstract;abstract_key]
    ]
  end in
  let interp_gens { gens } ~conclusion = Goal.enter begin fun g ->
   Ssrcommon.tacSIGMA >>= fun gl0 ->
     let open Ssrmatching in
     let ipats = List.map (fun (_,cp) ->
       match id_of_pattern (interp_cpattern gl0 cp None) with
       | None -> IPatAnon One
       | Some id -> IPatId id)
       (List.tl gens) in
     conclusion ipats
  end in
  interp_gens dgens ~conclusion:(fun ipats ->
  with_dgens dgens main <*>
  tclIPATssr ipats)

module Internal = struct

  let pf_find_abstract_proof b gl t =
    let res = ref None in
    let _ = V82.of_tactic (tacFIND_ABSTRACT_PROOF b (EConstr.of_constr t) >>= fun x -> res := Some x; tclUNIT ()) gl in
    match !res with
    | None -> assert false
    | Some x -> x

  let examine_abstract t gl =
    let res = ref None in
    let _ = V82.of_tactic (tacEXAMINE_ABSTRACT t >>= fun x -> res := Some x; tclUNIT ()) gl in
    match !res with
    | None -> assert false
    | Some x -> x

end

(* vim: set filetype=ocaml foldmethod=marker: *)
