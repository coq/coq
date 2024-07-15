(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module CVars = Vars
open Pp
open CErrors
open Util
open Names
open Nameops
open Term
open Constr
open Context
open Termops
open EConstr
open Vars
open Namegen
open Inductive
open Inductiveops
open Libnames
open Globnames
open Reductionops
open Retyping
open Tacmach
open Logic
open Hipattern
open Tacticals
open Tactics
open Tacred
open Coqlib
open Declarations
open Indrec
open Ind_tables
open Eqschemes
open Locus
open Locusops
open Tactypes
open Proofview.Notations
open Unification
open Context.Named.Declaration
open Combinators

module NamedDecl = Context.Named.Declaration

(* Options *)

type inj_flags = {
    keep_proof_equalities : bool;
    injection_pattern_l2r_order : bool;
  }

open Goptions

let use_injection_pattern_l2r_order = function
  | None -> true
  | Some flags -> flags.injection_pattern_l2r_order

let { Goptions.get = injection_in_context_flag } =
  declare_bool_option_and_ref
    ~key:["Structural";"Injection"]
    ~value:false
    ()

(* Rewriting tactics *)

type dep_proof_flag = bool (* true = support rewriting dependent proofs *)
type freeze_evars_flag = bool (* true = don't instantiate existing evars *)

type orientation = bool

type conditions =
  | Naive (* Only try the first occurrence of the lemma (default) *)
  | FirstSolved (* Use the first match whose side-conditions are solved *)
  | AllMatches (* Rewrite all matches whose side-conditions are solved *)

(* Warning : rewriting from left to right only works
   if there exists in the context a theorem named <eqname>_<suffsort>_r
   with type (A:<sort>)(x:A)(P:A->Prop)(P x)->(y:A)(eqname A y x)->(P y).
   If another equality myeq is introduced, then corresponding theorems
   myeq_ind_r, myeq_rec_r and myeq_rect_r have to be proven. See below.
   -- Eduardo (19/8/97)
*)

let rewrite_core_unif_flags = {
  modulo_conv_on_closed_terms = None;
  use_metas_eagerly_in_conv_on_closed_terms = true;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = TransparentState.empty;
  modulo_delta_types = TransparentState.empty;
  check_applied_meta_types = true;
  use_pattern_unification = true;
  use_meta_bound_pattern_unification = true;
  allowed_evars = Evarsolve.AllowedEvars.all;
  restrict_conv_on_strict_subterms = false;
  modulo_betaiota = false;
  modulo_eta = true;
}

let rewrite_unif_flags = {
  core_unify_flags = rewrite_core_unif_flags;
  merge_unify_flags = rewrite_core_unif_flags;
  subterm_unify_flags = rewrite_core_unif_flags;
  allow_K_in_toplevel_higher_order_unification = false;
    (* allow_K does not matter in practice because calls w_typed_unify *)
  resolve_evars = true
}

let freeze_initial_evars sigma flags newevars =
  let initial = Evd.undefined_map sigma in
  let allowed evk =
    if Evar.Map.mem evk initial then false
    else Evar.Set.mem evk (Lazy.force newevars)
  in
  let allowed_evars = Evarsolve.AllowedEvars.from_pred allowed in
  {flags with
    core_unify_flags = {flags.core_unify_flags with allowed_evars};
    merge_unify_flags = {flags.merge_unify_flags with allowed_evars};
    subterm_unify_flags = {flags.subterm_unify_flags with allowed_evars}}

let make_flags frzevars sigma flags newevars =
  if frzevars then freeze_initial_evars sigma flags newevars else flags

let side_tac tac sidetac =
  match sidetac with
  | None -> tac
  | Some sidetac -> tclTHENSFIRSTn tac [|Proofview.tclUNIT ()|] sidetac

let instantiate_lemma_all env flags eqclause l2r concl =
  let (_, args) = decompose_app (Clenv.clenv_evd eqclause) (Clenv.clenv_type eqclause) in
  let arglen = Array.length args in
  let () = if arglen < 2 then user_err Pp.(str "The term provided is not an applied relation.") in
  let c1 = args.(arglen - 2) in
  let c2 = args.(arglen - 1) in
  w_unify_to_subterm_all ~flags env (Clenv.clenv_evd eqclause)
    ((if l2r then c1 else c2),concl)

let rewrite_conv_closed_core_unif_flags = {
  modulo_conv_on_closed_terms = Some TransparentState.full;
    (* We have this flag for historical reasons, it has e.g. the consequence *)
    (* to rewrite "?x+2" in "y+(1+1)=0" or to rewrite "?x+?x" in "2+(1+1)=0" *)

  use_metas_eagerly_in_conv_on_closed_terms = true;
  use_evars_eagerly_in_conv_on_closed_terms = false;
    (* Combined with modulo_conv_on_closed_terms, this flag allows since 8.2 *)
    (* to rewrite e.g. "?x+(2+?x)" in "1+(1+2)=0" *)

  modulo_delta = TransparentState.empty;
  modulo_delta_types = TransparentState.full;
  check_applied_meta_types = true;
  use_pattern_unification = true;
    (* To rewrite "?n x y" in "y+x=0" when ?n is *)
    (* a preexisting evar of the goal*)

  use_meta_bound_pattern_unification = true;

  allowed_evars = Evarsolve.AllowedEvars.all;

  restrict_conv_on_strict_subterms = false;
  modulo_betaiota = false;
  modulo_eta = true;
}

let rewrite_conv_closed_unif_flags = {
  core_unify_flags = rewrite_conv_closed_core_unif_flags;
  merge_unify_flags = rewrite_conv_closed_core_unif_flags;
  subterm_unify_flags = rewrite_conv_closed_core_unif_flags;
  allow_K_in_toplevel_higher_order_unification = false;
  resolve_evars = false
}

let rewrite_keyed_core_unif_flags = {
  modulo_conv_on_closed_terms = Some TransparentState.full;
    (* We have this flag for historical reasons, it has e.g. the consequence *)
    (* to rewrite "?x+2" in "y+(1+1)=0" or to rewrite "?x+?x" in "2+(1+1)=0" *)

  use_metas_eagerly_in_conv_on_closed_terms = true;
  use_evars_eagerly_in_conv_on_closed_terms = false;
    (* Combined with modulo_conv_on_closed_terms, this flag allows since 8.2 *)
    (* to rewrite e.g. "?x+(2+?x)" in "1+(1+2)=0" *)

  modulo_delta = TransparentState.full;
  modulo_delta_types = TransparentState.full;
  check_applied_meta_types = true;
  use_pattern_unification = true;
    (* To rewrite "?n x y" in "y+x=0" when ?n is *)
    (* a preexisting evar of the goal*)

  use_meta_bound_pattern_unification = true;

  allowed_evars = Evarsolve.AllowedEvars.all;

  restrict_conv_on_strict_subterms = false;
  modulo_betaiota = true;

  modulo_eta = true;
}

let rewrite_keyed_unif_flags = {
  core_unify_flags = rewrite_keyed_core_unif_flags;
  merge_unify_flags = rewrite_keyed_core_unif_flags;
  subterm_unify_flags = rewrite_keyed_core_unif_flags;
  allow_K_in_toplevel_higher_order_unification = false;
  resolve_evars = false
}

let tclNOTSAMEGOAL tac =
  let goal gl = Proofview.Goal.goal gl in
  Proofview.Goal.enter begin fun gl ->
    let sigma = project gl in
    let ev = goal gl in
    tac >>= fun () ->
    Proofview.Goal.goals >>= fun gls ->
    let check accu gl' =
      gl' >>= fun gl' ->
      let accu = accu || Proofview.Progress.goal_equal
                            ~evd:sigma ~extended_evd:(project gl') ev (goal gl')
      in
      Proofview.tclUNIT accu
    in
    Proofview.Monad.List.fold_left check false gls >>= fun has_same ->
    if has_same then
      tclZEROMSG (str"Tactic generated a subgoal identical to the original goal.")
    else
      Proofview.tclUNIT ()
  end

let elim_wrapper cls rwtac =
  let open Pretype_errors in
  Proofview.tclORELSE
    begin match cls with
    | None ->
      (* was tclWEAK_PROGRESS which only fails for tactics generating one
          subgoal and did not fail for useless conditional rewritings generating
          an extra condition *)
      tclNOTSAMEGOAL rwtac
    | Some _ -> rwtac
    end
    begin function (e, info) -> match e with
    | PretypeError (env, evd, NoOccurrenceFound (c', _)) ->
      Proofview.tclZERO ~info (PretypeError (env, evd, NoOccurrenceFound (c', cls)))
    | e ->
      Proofview.tclZERO ~info e
    end

let general_elim_clause with_evars frzevars tac cls c (ctx, eqn, args) l l2r elim =
  (* Ad hoc asymmetric general_elim_clause *)
  let general_elim_clause0 rew =
    let rewrite_elim =
      Proofview.Goal.enter begin fun gl ->
      let sigma = Proofview.Goal.sigma gl in
      let flags = if Unification.is_keyed_unification ()
                  then rewrite_keyed_unif_flags else rewrite_conv_closed_unif_flags in
      (* We take evars of the type: this may include old evars! For excluding *)
      (* all old evars, including the ones occurring in the rewriting lemma, *)
      (* we would have to take the clenv_value *)
      let newevars = lazy (Evarutil.undefined_evars_of_term sigma (Clenv.clenv_type rew)) in
      let flags = make_flags frzevars sigma flags newevars in
      let metas = Evd.meta_list (Clenv.clenv_evd rew) in
      let submetas = List.map (fun mv -> mv, Evd.Metamap.find mv metas) (Clenv.clenv_arguments rew) in
      general_elim_clause with_evars flags cls (submetas, c, Clenv.clenv_type rew) elim
      end
    in
    Proofview.Unsafe.tclEVARS (Evd.clear_metas (Clenv.clenv_evd rew)) <*>
    elim_wrapper cls rewrite_elim
  in
  let strat, tac =
    match tac with
    | None -> Naive, None
    | Some (tac, Naive) -> Naive, Some tac
    | Some (tac, FirstSolved) -> FirstSolved, Some (tclCOMPLETE tac)
    | Some (tac, AllMatches) -> AllMatches, Some (tclCOMPLETE tac)
  in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let typ = match cls with
    | None -> pf_concl gl
    | Some id -> pf_get_hyp_typ id gl
    in
    let ty = it_mkProd_or_LetIn (applist (eqn, args)) ctx in
    let eqclause = Clenv.make_clenv_binding env sigma (c, ty) l in
    let try_clause evd' =
      let clenv = Clenv.update_clenv_evd eqclause evd' in
      let clenv = Clenv.clenv_pose_dependent_evars ~with_evars:true clenv in
      side_tac (general_elim_clause0 clenv) tac
    in
    match strat with
    | Naive ->
      side_tac (general_elim_clause0 eqclause) tac
    | FirstSolved ->
      let flags = make_flags frzevars sigma rewrite_unif_flags (lazy Evar.Set.empty) in
      let cs = instantiate_lemma_all env flags eqclause l2r typ in
      tclFIRST (List.map try_clause cs)
    | AllMatches ->
      let flags = make_flags frzevars sigma rewrite_unif_flags (lazy Evar.Set.empty) in
      let cs = instantiate_lemma_all env flags eqclause l2r typ in
      tclMAP try_clause cs
  end

(* The next function decides in particular whether to try a regular
  rewrite or a generalized rewrite.
  Approach is to break everything, if [eq] appears in head position
  then regular rewrite else try general rewrite.
  If occurrences are set, use general rewrite.
*)

let (forward_general_setoid_rewrite_clause, general_setoid_rewrite_clause) = Hook.make ()

(* Do we have a JMeq instance on twice the same domains ? *)

let jmeq_same_dom env sigma (rels, eq, args) =
  let env = push_rel_context rels env in
  match args with
    | [dom1; _; dom2;_] -> is_conv env sigma dom1 dom2
    | _ -> false

let eq_elimination_ref l2r sort =
  let name =
    if l2r then
      match sort with
      | InProp -> "core.eq.ind_r"
      | InSProp -> "core.eq.sind_r"
      | InSet | InType | InQSort -> "core.eq.rect_r"
    else
      match sort with
      | InProp -> "core.eq.ind"
      | InSProp -> "core.eq.sind"
      | InSet | InType | InQSort -> "core.eq.rect"
  in
  Coqlib.lib_ref_opt name

(* find_elim determines which elimination principle is necessary to
   eliminate lbeq on sort_of_gl. *)

let find_elim lft2rgt dep cls ((_, hdcncl, _) as t) =
  Proofview.Goal.enter_one begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = project gl in
  let is_global_exists gr c = match Coqlib.lib_ref_opt gr with
    | Some gr -> isRefX env sigma gr c
    | None -> false
  in
  let inccl = Option.is_empty cls in
  let is_eq = is_global_exists "core.eq.type" hdcncl in
  let is_jmeq = is_global_exists "core.JMeq.type" hdcncl && jmeq_same_dom env sigma t in
  if (is_eq || is_jmeq) && not dep
  then
    let sort = elimination_sort_of_clause cls gl in
    let c =
      match EConstr.kind sigma hdcncl with
      | Ind (ind_sp,u) ->
        begin match lft2rgt, cls with
        | Some true, None
        | Some false, Some _ ->
          begin match if is_eq then eq_elimination_ref true sort else None with
          | Some r -> destConstRef r
          | None ->
            let c1 = destConstRef (lookup_eliminator env ind_sp sort) in
            let mp,l = KerName.repr (Constant.canonical c1) in
            let l' = Label.of_id (add_suffix (Label.to_id l) "_r")  in
            let c1' = Global.constant_of_delta_kn (KerName.make mp l') in
            if not (Environ.mem_constant c1' (Global.env ())) then
              user_err
                (str "Cannot find rewrite principle " ++ Label.print l' ++ str ".");
            c1'
          end
        | _ ->
          begin match if is_eq then eq_elimination_ref false sort else None with
          | Some r -> destConstRef r
          | None -> destConstRef (lookup_eliminator env ind_sp sort)
          end
        end
      | _ ->
          (* cannot occur since we checked that we are in presence of
             Logic.eq or Jmeq just before *)
        assert false
    in
    Proofview.tclUNIT c
  else
  let scheme_name = match dep, lft2rgt, inccl with
    (* Non dependent case *)
    | false, Some true, true -> rew_l2r_scheme_kind
    | false, Some true, false -> rew_r2l_scheme_kind
    | false, _, false -> rew_l2r_scheme_kind
    | false, _, true -> rew_r2l_scheme_kind
    (* Dependent case *)
    | true, Some true, true -> rew_l2r_dep_scheme_kind
    | true, Some true, false -> rew_l2r_forward_dep_scheme_kind
    | true, _, true -> rew_r2l_dep_scheme_kind
    | true, _, false -> rew_r2l_forward_dep_scheme_kind
  in
  match EConstr.kind sigma hdcncl with
  | Ind (ind,u) -> find_scheme scheme_name ind
  | _ -> assert false
  end

let type_of_clause cls gl = match cls with
  | None -> Proofview.Goal.concl gl
  | Some id -> pf_get_hyp_typ id gl

let leibniz_rewrite_ebindings_clause cls lft2rgt tac c ((_, hdcncl, _) as t) l with_evars frzevars dep_proof_ok =
  Proofview.Goal.enter begin fun gl ->
  let evd = Proofview.Goal.sigma gl in
  let type_of_cls = type_of_clause cls gl in
  let dep = dep_proof_ok && dependent_no_evar evd c type_of_cls in
  find_elim lft2rgt dep cls t >>= fun elim ->
      general_elim_clause with_evars frzevars tac cls c t l
      (match lft2rgt with None -> false | Some b -> b) elim
  end

let adjust_rewriting_direction args lft2rgt =
  match args with
  | [_] ->
    (* equality to a constant, like in eq_true *)
    (* more natural to see -> as the rewriting to the constant *)
    if not lft2rgt then
      user_err Pp.(str "Rewriting non-symmetric equality not allowed from right-to-left.");
    None
  | _ ->
    (* other equality *)
    Some lft2rgt

let rewrite_side_tac tac sidetac = side_tac tac (Option.map fst sidetac)

(* Main function for dispatching which kind of rewriting it is about *)

let general_rewrite ~where:cls ~l2r:lft2rgt occs ~freeze:frzevars ~dep:dep_proof_ok ~with_evars ?tac
    ((c,l) : constr with_bindings) =
  if not (Locusops.is_all_occurrences occs) then (
    rewrite_side_tac (Hook.get forward_general_setoid_rewrite_clause cls lft2rgt occs (c,l) ~new_goals:[]) tac)
  else
    Proofview.Goal.enter begin fun gl ->
      let sigma = Tacmach.project gl in
      let env = Proofview.Goal.env gl in
    let ctype = get_type_of env sigma c in
    let rels, t = decompose_prod_decls sigma (whd_betaiotazeta env sigma ctype) in
      match match_with_equality_type env sigma t with
      | Some (hdcncl,args) -> (* Fast path: direct leibniz-like rewrite *)
          let lft2rgt = adjust_rewriting_direction args lft2rgt in
          leibniz_rewrite_ebindings_clause cls lft2rgt tac c (rels, hdcncl, args)
            l with_evars frzevars dep_proof_ok
      | None ->
          Proofview.tclORELSE
            begin
              rewrite_side_tac (Hook.get forward_general_setoid_rewrite_clause cls
                                   lft2rgt occs (c,l) ~new_goals:[]) tac
            end
            begin function
              | (e, info) ->
                  Proofview.tclEVARMAP >>= fun sigma ->
                  let env' = push_rel_context rels env in
                  let rels',t' = whd_decompose_prod_decls env' sigma t in (* Search for underlying eq *)
                  match match_with_equality_type env' sigma t' with
                    | Some (hdcncl,args) ->
                  let lft2rgt = adjust_rewriting_direction args lft2rgt in
                  leibniz_rewrite_ebindings_clause cls lft2rgt tac c
                    (rels' @ rels, hdcncl, args) l with_evars frzevars dep_proof_ok
                    | None -> Proofview.tclZERO ~info e
            (* error "The provided term does not end with an equality or a declared rewrite relation." *)
            end
    end

let clear_for_rewrite_in_hyps ids c =
  let ids = Id.Set.of_list ids in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    (* Is this the right err? *)
    let err = (Evarutil.OccurHypInSimpleClause None) in
    let sigma =
      try Evarutil.check_and_clear_in_constr env sigma err ids c
      with Evarutil.ClearDependencyError (id,err,inglobal) ->
        CErrors.user_err Pp.(str "Cannot rewrite due to dependency on " ++ Id.print id ++ str ".")
    in
    Proofview.Unsafe.tclEVARS sigma
  end

let general_rewrite_clause l2r with_evars ?tac c cl =
  let occs_of = occurrences_map (List.fold_left
    (fun acc ->
      function ArgArg x -> x :: acc | ArgVar _ -> acc)
    [])
  in
  match cl.onhyps with
    | Some l ->
        (* If a precise list of locations is given, success is mandatory for
           each of these locations. *)
        let rec do_hyps = function
          | [] -> Proofview.tclUNIT ()
          | ((occs,id),_) :: l ->
            tclTHENFIRST
              (general_rewrite ~where:(Some id) ~l2r (occs_of occs) ~freeze:false ~dep:true ~with_evars ?tac c)
              (do_hyps l)
        in
        let tac =
          if cl.concl_occs == NoOccurrences then do_hyps l
          else
            tclTHENFIRST
              (general_rewrite ~where:None ~l2r (occs_of cl.concl_occs) ~freeze:false ~dep:true ~with_evars ?tac c)
              (do_hyps l)
        in
        begin match l with
        | [] | [_] ->
          (* don't clear when rewriting in 1 hyp *)
          tac
        | _ ->
          tclTHEN (clear_for_rewrite_in_hyps (List.map (fun ((_,id),_) -> id) l) (fst c)) tac
        end
    | None ->
        (* Otherwise, if we are told to rewrite in all hypothesis via the
           syntax "* |-", we fail iff all the different rewrites fail *)
        let rec do_hyps_atleastonce = function
          | [] -> tclZEROMSG (Pp.str"Nothing to rewrite.")
          | id :: l ->
            tclIFTHENFIRSTTRYELSEMUST
              (tclTHEN (clear_for_rewrite_in_hyps [id] (fst c))
                 (general_rewrite ~where:(Some id) ~l2r AllOccurrences ~freeze:false ~dep:true ~with_evars ?tac c))
              (do_hyps_atleastonce l)
        in
        let do_hyps =
          Proofview.Goal.enter begin fun gl ->
            do_hyps_atleastonce (pf_ids_of_hyps gl)
          end
        in
        if cl.concl_occs == NoOccurrences then do_hyps else
          tclIFTHENFIRSTTRYELSEMUST
           (general_rewrite ~where:None ~l2r (occs_of cl.concl_occs) ~freeze:false ~dep:true ~with_evars ?tac c)
           do_hyps

let apply_special_clear_request clear_flag f =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Tacmach.project gl in
    let env = Proofview.Goal.env gl in
    try
      let (sigma, (c, bl)) = f env sigma in
      let c = try Some (destVar sigma c) with DestKO -> None in
      apply_clear_request clear_flag (use_clear_hyp_by_default ()) c
    with
      e when noncritical e -> tclIDTAC
  end

type multi =
  | Precisely of int
  | UpTo of int
  | RepeatStar
  | RepeatPlus

let general_multi_rewrite with_evars l cl tac =
  let do1 l2r f =
    Proofview.Goal.enter begin fun gl ->
      let sigma = Tacmach.project gl in
      let env = Proofview.Goal.env gl in
      let (sigma, c) = f env sigma in
      tclWITHHOLES with_evars
        (general_rewrite_clause l2r with_evars ?tac c cl) sigma
    end
  in
  let rec doN l2r c = function
    | Precisely n when n <= 0 -> Proofview.tclUNIT ()
    | Precisely 1 -> do1 l2r c
    | Precisely n -> tclTHENFIRST (do1 l2r c) (doN l2r c (Precisely (n-1)))
    | RepeatStar -> tclREPEAT_MAIN (do1 l2r c)
    | RepeatPlus -> tclTHENFIRST (do1 l2r c) (doN l2r c RepeatStar)
    | UpTo n when n<=0 -> Proofview.tclUNIT ()
    | UpTo n -> tclTHENFIRST (tclTRY (do1 l2r c)) (doN l2r c (UpTo (n-1)))
  in
  let rec loop = function
    | [] -> Proofview.tclUNIT ()
    | (l2r,m,clear_flag,c)::l ->
        tclTHENFIRST
          (tclTHEN (doN l2r c m) (apply_special_clear_request clear_flag c)) (loop l)
  in loop l

let rewriteLR c =
  general_rewrite ~where:None ~l2r:true AllOccurrences ~freeze:true ~dep:true ~with_evars:false (c, NoBindings)
let rewriteRL c =
  general_rewrite ~where:None ~l2r:false AllOccurrences ~freeze:true ~dep:true ~with_evars:false (c, NoBindings)

(* Replacing tactics *)

let classes_dirpath =
  DirPath.make (List.map Id.of_string ["Classes";"Stdlib"])

let init_setoid () =
  if is_dirpath_prefix_of classes_dirpath (Lib.cwd ()) then ()
  else check_required_library ["Stdlib";"Setoids";"Setoid"]

let check_setoid cl =
  let concloccs = Locusops.occurrences_map (fun x -> x) cl.concl_occs in
  Option.fold_left
    (List.fold_left
        (fun b ((occ,_),_) ->
          b||(not (Locusops.is_all_occurrences (Locusops.occurrences_map (fun x -> x) occ)))
        )
    )
    (not (Locusops.is_all_occurrences concloccs) &&
     (concloccs <> NoOccurrences))
    cl.onhyps

let replace_core clause l2r eq =
  if check_setoid clause
  then init_setoid ();
  tclTHENFIRST
    (assert_after Anonymous eq)
    (onLastHypId (fun id ->
      tclTHEN
        (tclTRY (general_rewrite_clause l2r false (mkVar id,NoBindings) clause))
        (clear [id])))

(* eq,sym_eq : equality on Type and its symmetry theorem
   c1 c2 : c1 is to be replaced by c2
   unsafe : If true, do not check that c1 and c2 are convertible
   tac : Used to prove the equality c1 = c2
   gl : goal *)

let replace_using_leibniz clause c1 c2 l2r unsafe try_prove_eq_opt =
  Proofview.Goal.enter begin fun gl ->
  let get_type_of = pf_apply get_type_of gl in
  let t1 = get_type_of c1
  and t2 = get_type_of c2 in
  let evd =
    if unsafe then Some (Tacmach.project gl)
    else
      try Some (Evarconv.unify_delay (Proofview.Goal.env gl) (Tacmach.project gl) t1 t2)
      with Evarconv.UnableToUnify _ -> None
  in
  match evd with
  | None ->
    tclFAIL (str"Terms do not have convertible types")
  | Some evd ->
    let e,sym =
      try lib_ref "core.eq.type", lib_ref "core.eq.sym"
      with NotFoundRef _ ->
      try lib_ref "core.identity.type", lib_ref "core.identity.sym"
      with NotFoundRef _ ->
        user_err (strbrk "Need a registration for either core.eq.type and core.eq.sym or core.identity.type and core.identity.sym.") in
    Tacticals.pf_constr_of_global sym >>= fun sym ->
    Tacticals.pf_constr_of_global e >>= fun e ->
    let eq = applist (e, [t1;c1;c2]) in
    let solve_tac = match try_prove_eq_opt with
      | None ->
        tclFIRST
          [ assumption;
            tclTHEN (apply sym) assumption;
            Proofview.tclUNIT () ]
      | Some tac -> tclCOMPLETE tac
    in
    tclTHENLAST
      (replace_core clause l2r eq)
      solve_tac
  end

let replace c1 c2 =
  replace_using_leibniz onConcl c2 c1 false false None

let replace_by c1 c2 tac =
  replace_using_leibniz onConcl c2 c1 false false (Some tac)

let replace_in_clause_maybe_by dir_opt c1 c2 cl tac_opt =
  let c1, c2, dir = match dir_opt with
  | None | Some false -> c1, c2, false
  | Some true -> c2, c1, true
  in
  replace_using_leibniz cl c2 c1 dir false tac_opt

(* End of Eduardo's code. The rest of this file could be improved
   using the functions match_with_equation, etc that I defined
   in Pattern.ml.
   -- Eduardo (19/8/97)
*)

(* Tactics for equality reasoning with the "eq" relation. This code
   will work with any equivalence relation which is substitutive *)

(* [find_positions t1 t2]

   will find the positions in the two terms which are suitable for
   discrimination, or for injection.  Obviously, if there is a
   position which is suitable for discrimination, then we want to
   exploit it, and not bother with injection.  So when we find a
   position which is suitable for discrimination, we will just raise
   an exception with that position.

   So the algorithm goes like this:

   if [t1] and [t2] start with the same constructor, then we can
   continue to try to find positions in the arguments of [t1] and
   [t2].

   if [t1] and [t2] do not start with the same constructor, then we
   have found a discrimination position

   if one [t1] or [t2] do not start with a constructor and the two
   terms are not already convertible, then we have found an injection
   position.

   A discriminating position consists of a constructor-path and a pair
   of operators.  The constructor-path tells us how to get down to the
   place where the two operators, which must differ, can be found.

   An injecting position has two terms instead of the two operators,
   since these terms are different, but not manifestly so.

   A constructor-path is a list of pairs of (operator * int), where
   the int (based at 0) tells us which argument of the operator we
   descended into.

 *)

exception DiscrFound of
  (constructor * int) list * constructor * constructor

let keep_proof_equalities_for_injection = ref false

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Keep";"Proof";"Equalities"];
      optread  = (fun () -> !keep_proof_equalities_for_injection) ;
      optwrite = (fun b -> keep_proof_equalities_for_injection := b) }

let keep_proof_equalities = function
  | None -> !keep_proof_equalities_for_injection
  | Some flags -> flags.keep_proof_equalities

module KeepEqualities =
struct
  type t = inductive
  module Set = Indset_env
  let encode _env r = Nametab.global_inductive r
  let subst subst obj = Mod_subst.subst_ind subst obj
  let printer ind = Nametab.pr_global_env Id.Set.empty (GlobRef.IndRef ind)
  let key = ["Keep"; "Equalities"]
  let title = "Prop-valued inductive types for which injection keeps equality proofs"
  let member_message ind b =
    let b = if b then mt () else str "not " in
    str "Equality proofs over " ++ (printer ind) ++
      str " are " ++ b ++ str "kept by injection"
end

module KeepEqualitiesTable = Goptions.MakeRefTable(KeepEqualities)

let set_keep_equality = KeepEqualitiesTable.set

(* [keep_proofs] is relevant for types in Prop with elimination in Type *)
(* In particular, it is relevant for injection but not for discriminate *)

let keep_head_inductive sigma c =
  (* Note that we do not weak-head normalize c before checking it is an
     applied inductive, because [get_sort_family_of] did not use to either.
     As a matter of fact, if it reduces to an applied template inductive
     type but is not syntactically equal to it, it will fail to project. *)
  let _, hd = EConstr.decompose_prod sigma c in
  let hd, _ = EConstr.decompose_app sigma hd in
  match EConstr.kind sigma hd with
  | Ind (ind, _) -> KeepEqualitiesTable.active ind
  | _ -> false

let find_positions env sigma ~keep_proofs ~no_discr t1 t2 =
  let project env sorts posn t1 t2 =
    let ty1 = get_type_of env sigma t1 in
    let keep =
      if keep_head_inductive sigma ty1 then true
      else
        let s = get_sort_family_of env sigma ty1 in
        List.mem_f Sorts.family_equal s sorts
    in
    if keep then [(List.rev posn,t1,t2)] else []
  in
  let rec findrec sorts posn t1 t2 =
    let hd1,args1 = whd_all_stack env sigma t1 in
    let hd2,args2 = whd_all_stack env sigma t2 in
    match (EConstr.kind sigma hd1, EConstr.kind sigma hd2) with
      | Construct ((ind1,i1 as sp1),u1), Construct (sp2,_)
          when Int.equal (List.length args1) (constructor_nallargs env sp1)
            ->
          let sorts' =
            CList.intersect Sorts.family_equal sorts (sorts_below (top_allowed_sort env (fst sp1)))
          in
          (* both sides are fully applied constructors, so either we descend,
             or we can discriminate here. *)
          if Environ.QConstruct.equal env sp1 sp2 then
            let nparams = inductive_nparams env ind1 in
            let params1,rargs1 = List.chop nparams args1 in
            let _,rargs2 = List.chop nparams args2 in
            let (mib,mip) = lookup_mind_specif env ind1 in
            let ctxt = (get_constructor ((ind1,u1),mib,mip,params1) i1).cs_args in
            let adjust i = CVars.adjust_rel_to_rel_context ctxt (i+1) - 1 in
            List.flatten
              (List.map2_i (fun i -> findrec sorts' ((sp1,adjust i)::posn))
                0 rargs1 rargs2)
          else if List.mem_f Sorts.family_equal InType sorts' && not no_discr
          then (* see build_discriminator *)
            raise (DiscrFound (List.rev posn,sp1,sp2))
          else
          (* if we cannot eliminate to Type, we cannot discriminate but we
             may still try to project *)
          project env sorts posn (applist (hd1,args1)) (applist (hd2,args2))
      | _ ->
          let t1_0 = applist (hd1,args1)
          and t2_0 = applist (hd2,args2) in
          if is_conv env sigma t1_0 t2_0 then
            []
          else
            project env sorts posn t1_0 t2_0
  in
  try
    let sorts = if keep_proofs then [InSet;InType;InProp] else [InSet;InType] in
    Inr (findrec sorts [] t1 t2)
  with DiscrFound (path,c1,c2) ->
    Inl (path,c1,c2)

let use_keep_proofs = function
  | None -> !keep_proof_equalities_for_injection
  | Some b -> b

(* Once we have found a position, we need to project down to it.  If
   we are discriminating, then we need to produce False on one of the
   branches of the discriminator, and True on the other one.  So the
   result type of the case-expressions is always Prop.

   If we are injecting, then we need to discover the result-type.
   This can be difficult, since the type of the two terms at the
   injection-position can be different, and we need to find a
   dependent sigma-type which generalizes them both.

   We can get an approximation to the right type to choose by:

   (0) Before beginning, we reserve a patvar for the default
   value of the match, to be used in all the bogus branches.

   (1) perform the case-splits, down to the site of the injection.  At
   each step, we have a term which is the "head" of the next
   case-split.  At the point when we actually reach the end of our
   path, the "head" is the term to return.  We compute its type, and
   then, backwards, make a sigma-type with every free debruijn
   reference in that type.  We can be finer, and first do a S(TRONG)NF
   on the type, so that we get the fewest number of references
   possible.

   (2) This gives us a closed type for the head, which we use for the
   types of all the case-splits.

   (3) Now, we can compute the type of one of T1, T2, and then unify
   it with the type of the last component of the result-type, and this
   will give us the bindings for the other arguments of the tuple.

 *)

(* The algorithm, then is to perform successive case-splits.  We have
   the result-type of the case-split, and also the type of that
   result-type.  We have a "direction" we want to follow, i.e. a
   constructor-number, and in all other "directions", we want to juse
   use the default-value.

   After doing the case-split, we call the afterfun, with the updated
   environment, to produce the term for the desired "direction".

   The assumption is made here that the result-type is not manifestly
   functional, so we can just use the length of the branch-type to
   know how many lambda's to stick in.

 *)

(* [descend_then env sigma head dirn]

   returns the number of products introduced, and the environment
   which is active, in the body of the case-branch given by [dirn],
   along with a continuation, which expects to be fed:

    (1) the value of the body of the branch given by [dirn]
    (2) the default-value

    (3) the type of the default-value, which must also be the type of
        the body of the [dirn] branch

   the continuation then constructs the case-split.
 *)

let descend_then env sigma head dirn =
  let IndType (indf,_) as indt =
    try find_rectype env sigma (get_type_of env sigma head)
    with Not_found ->
      user_err Pp.(str "Cannot project on an inductive type derived from a dependency.")
  in
  let (ind, _),_ = (dest_ind_family indf) in
  let () = check_privacy env ind in
  let (mib,mip) = lookup_mind_specif env ind in
  let cstr = get_constructors env indf in
  let dirn_nlams = cstr.(dirn-1).cs_nargs in
  let dirn_env = EConstr.push_rel_context cstr.(dirn-1).cs_args env in
  (dirn_nlams,
   dirn_env,
   (fun sigma dirnval (dfltval,resty) ->
      let deparsign = make_arity_signature env sigma true indf in
      let p =
        it_mkLambda_or_LetIn (lift (mip.mind_nrealargs+1) resty) deparsign in
      let build_branch i =
        let result = if Int.equal i dirn then dirnval else dfltval in
        let cs_args = cstr.(i-1).cs_args in
        let args = name_context env sigma cs_args in
        it_mkLambda_or_LetIn result args in
      let brl =
        List.map build_branch
          (List.interval 1 (Array.length mip.mind_consnames)) in
      let rci = ERelevance.relevant in (* TODO relevance *)
      let ci = make_case_info env ind RegularStyle in
      Inductiveops.make_case_or_project env sigma indt ci (p, rci) head (Array.of_list brl)))

(* Now we need to construct the discriminator, given a discriminable
   position.  This boils down to:

   (1) If the position is directly beneath us, then we need to do a
   case-split, with result-type Prop, and stick True and False into
   the branches, as is convenient.

   (2) If the position is not directly beneath us, then we need to
   call descend_then, to descend one step, and then recursively
   construct the discriminator.

 *)

let build_coq_False () = pf_constr_of_global (lib_ref "core.False.type")
let build_coq_True () = pf_constr_of_global (lib_ref "core.True.type")
let build_coq_I () = pf_constr_of_global (lib_ref "core.True.I")

let rec build_discriminator env sigma true_0 false_0 pos c = function
  | [] ->
      let cty = get_type_of env sigma c in
      make_selector env sigma ~pos ~special:true_0 ~default:(fst false_0) c cty
  | ((sp,cnum),argnum)::l ->
      let (cnum_nlams,cnum_env,kont) = descend_then env sigma c cnum in
      let newc = mkRel(cnum_nlams-argnum) in
      let subval = build_discriminator cnum_env sigma true_0 false_0 pos newc l in
      kont sigma subval false_0

(* Note: discrimination could be more clever: if some elimination is
   not allowed because of a large impredicative constructor in the
   path (see allowed_sorts in find_positions), the positions could
   still be discrimated by projecting first instead of putting the
   discrimination combinator inside the projecting combinator. Example
   of relevant situation:

   Inductive t:Set := c : forall A:Set, A -> nat -> t.
   Goal ~ c _ 0 0 = c _ 0 1. intro. discriminate H.
*)

let gen_absurdity id =
  Proofview.Goal.enter begin fun gl ->
  let env = pf_env gl in
  let sigma = project gl in
  let hyp_typ = pf_get_hyp_typ id gl in
  if is_empty_type env sigma hyp_typ
  then
    simplest_elim (mkVar id)
  else
    tclZEROMSG (str "Not the negation of an equality.")
  end

(* Precondition: eq is leibniz equality

   returns ((eq_elim t t1 P i t2), absurd_term)
   where  P=[e:t]discriminator
          absurd_term=False
*)

let ind_scheme_of_eq lbeq to_kind =
  (* use ind rather than case by compatibility *)
  let kind = Elimschemes.elim_scheme ~dep:false ~to_kind in
  find_scheme kind (destIndRef lbeq.eq) >>= fun c ->
  Proofview.tclUNIT (GlobRef.ConstRef c)


let discrimination_pf e (t,t1,t2) discriminator lbeq to_kind =
  build_coq_I () >>= fun i ->
  ind_scheme_of_eq lbeq to_kind >>= fun eq_elim ->
    pf_constr_of_global eq_elim >>= fun eq_elim ->
    Proofview.tclEVARMAP >>= fun sigma ->
    Proofview.tclUNIT
       (applist (eq_elim, [t;t1;mkNamedLambda sigma (make_annot e ERelevance.relevant) t discriminator;i;t2]))

type equality = {
  eq_data  : (coq_eq_data * (EConstr.t * EConstr.t * EConstr.t));
  (* equality data + A : Type, t1 : A, t2 : A *)
  eq_term : EConstr.t;
  (* term [M : R A t1 t2] where [R] is the equality from above *)
  eq_evar : Proofview_monad.goal_with_state list;
  (* List of implicit hypotheses on which the data above depends. *)
}

let eq_baseid = Id.of_string "e"

let discr_positions env sigma { eq_data = (lbeq,(t,t1,t2)); eq_term = v; eq_evar = evs } cpath dirn =
  build_coq_True () >>= fun true_0 ->
  build_coq_False () >>= fun false_0 ->
  let false_ty = Retyping.get_type_of env sigma false_0 in
  let false_kind = Retyping.get_sort_family_of env sigma false_0 in
  let e = next_ident_away eq_baseid (vars_of_env env) in
  let e_env = push_named (Context.Named.Declaration.LocalAssum (make_annot e ERelevance.relevant,t)) env in
  let discriminator =
    try
      Proofview.tclUNIT
        (build_discriminator e_env sigma true_0 (false_0,false_ty) dirn (mkVar e) cpath)
    with
      UserError _ as ex ->
      let _, info = Exninfo.capture ex in
      Proofview.tclZERO ~info ex
  in
    discriminator >>= fun discriminator ->
    discrimination_pf e (t,t1,t2) discriminator lbeq false_kind >>= fun pf ->
    (* pf : eq t t1 t2 -> False *)
    let pf = EConstr.mkApp (pf, [|v|]) in
    tclTHENS (assert_after Anonymous false_0)
      [onLastHypId gen_absurdity; Tactics.exact_check pf <*> Proofview.Unsafe.tclNEWGOALS evs]

let discrEq eq =
  let { eq_data = (_, (_, t1, t2)) } = eq in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    match find_positions env sigma ~keep_proofs:false ~no_discr:false t1 t2 with
    | Inr _ ->
      let info = Exninfo.reify () in
      tclZEROMSG ~info (str"Not a discriminable equality.")
    | Inl (cpath, (_,dirn), _) ->
      discr_positions env sigma eq cpath dirn
  end

let make_clause with_evars env sigma t lbindc =
  let sigma', eq_clause = EClause.make_evar_clause env sigma t in
  let sigma' = EClause.solve_evar_clause env sigma' false eq_clause lbindc in
  let () = if not with_evars then EClause.check_evar_clause env sigma sigma' eq_clause in
  sigma', eq_clause

let onEquality with_evars tac (c,lbindc) =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let state = Proofview.Goal.state gl in
  let t = Retyping.get_type_of env sigma c in
  let t' = try snd (Tacred.reduce_to_quantified_ind env sigma t) with UserError _ -> t in
  let sigma, eq_clause = make_clause with_evars env sigma t' lbindc in
  let filter h =
    if h.EClause.hole_deps then None
    else
      try Some (Proofview_monad.goal_with_state (fst @@ destEvar sigma h.EClause.hole_evar) state)
      with DestKO -> None
  in
  let goals = List.map_filter filter eq_clause.EClause.cl_holes in
  let cl_args = Array.map_of_list (fun h -> h.EClause.hole_evar) eq_clause.EClause.cl_holes in
  let (eq,u,eq_args) = find_this_eq_data_decompose env sigma eq_clause.cl_concl in
  let eq = { eq_data = (eq, eq_args); eq_term = mkApp (c, cl_args); eq_evar = goals } in
  Proofview.Unsafe.tclEVARS sigma <*> tac eq
  end

let onNegatedEquality with_evars tac =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Tacmach.project gl in
    let ccl = Proofview.Goal.concl gl in
    let env = Proofview.Goal.env gl in
    match EConstr.kind sigma (hnf_constr0 env sigma ccl) with
    | Prod (na,t,u) ->
      let u = nf_betaiota (push_rel_assum (na, t) env) sigma u in
      if is_empty_type env sigma u then
        tclTHEN introf
          (onLastHypId (fun id ->
            onEquality with_evars tac (mkVar id,NoBindings)))
      else tclZEROMSG (str "Not a negated primitive equality.")
    | _ ->
      let info = Exninfo.reify () in
      tclZEROMSG ~info (str "Not a negated primitive equality.")
  end

let discrSimpleClause with_evars = function
  | None -> onNegatedEquality with_evars discrEq
  | Some id -> onEquality with_evars discrEq (mkVar id,NoBindings)

let discr with_evars = onEquality with_evars discrEq

let discrClause with_evars = onClause (discrSimpleClause with_evars)

let discrEverywhere with_evars =
  tclTHEN (Proofview.tclUNIT ())
    (* Delay the interpretation of side-effect *)
    (tclTHEN
       (tclREPEAT introf)
       (tryAllHyps
          (fun id -> tclCOMPLETE (discr with_evars (mkVar id,NoBindings)))))

let discr_tac with_evars = function
  | None -> discrEverywhere with_evars
  | Some c -> onInductionArg (fun clear_flag -> discr with_evars) c

let discrConcl = discrClause false onConcl
let discrHyp id = discrClause false (onHyp id)

(* The problem is to build a destructor (a generalization of the
   predecessor) which, when applied to a term made of constructors
   (say [Ci(e1,Cj(e2,Ck(...,term,...),...),...)]), returns a given
   subterm of the term (say [term]).

   Let [typ] be the type of [term]. If [term] has no dependencies in
   the [e1], [e2], etc, then all is simple. If not, then we need to
   encapsulated the dependencies into a dependent tuple in such a way
   that the destructor has not a dependent type and rewriting can then
   be applied. The destructor has the form

   [e]Cases e of
      | ...
      | Ci (x1,x2,...) =>
          Cases x2 of
          | ...
          | Cj (y1,y2,...) =>
              Cases y2 of
              | ...
              | Ck (...,z,...) => z
              | ... end
          | ... end
      | ... end

   and the dependencies is expressed by the fact that [z] has a type
   dependent in the x1, y1, ...

   Assume [z] is typed as follows: env |- z:zty

   If [zty] has no dependencies, this is simple. Otherwise, assume
   [zty] has free (de Bruijn) variables in,...i1 then the role of
   [make_iterated_tuple env sigma (term,typ) (z,zty)] is to build the
   tuple

   [existT [xn]Pn Rel(in) .. (existT [x2]P2 Rel(i2) (existT [x1]P1 Rel(i1) z))]

   where P1 is zty[i1/x1], P2 is {x1 | P1[i2/x2]} etc.
*)

let rec build_injrec env sigma default c = function
  | [] ->
    let cty = get_type_of env sigma c in
    let sigma, { telescope_type; telescope_value }, dfltval = make_iterated_tuple env sigma ~default c cty in
    sigma, (telescope_value, telescope_type, dfltval)
  | ((sp,cnum),argnum)::l ->
    try
      let (cnum_nlams,cnum_env,kont) = descend_then env sigma c cnum in
      let newc = mkRel(cnum_nlams-argnum) in
      let sigma, (subval,tuplety,dfltval) = build_injrec cnum_env sigma default newc l in
      let res = kont sigma subval (dfltval,tuplety) in
      sigma, (res, tuplety,dfltval)
    with
        UserError _ -> failwith "caught"

let build_injector env sigma dflt c cpath =
  let sigma, (injcode,resty,_) = build_injrec env sigma dflt c cpath in
    sigma, (injcode,resty)

let eq_dec_scheme_kind_name = ref (fun _ -> failwith "eq_dec_scheme undefined")
let set_eq_dec_scheme_kind k = eq_dec_scheme_kind_name := (fun _ -> k)

let warn_inject_no_eqdep_dec =
  CWarnings.create ~name:"injection-missing-eqdep-dec" ~category:CWarnings.CoreCategories.tactics
    Pp.(fun (env,ind) ->
        str "The equality scheme for" ++ spc() ++ Printer.pr_inductive env ind ++ spc() ++
        str "could not be used as Coq.Logic.Eqdep_dec has not been required.")

let inject_if_homogenous_dependent_pair ty =
  Proofview.Goal.enter begin fun gl ->
  try
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    let eq,u,(t,t1,t2) = pf_apply find_this_eq_data_decompose gl ty in
    (* fetch the informations of the  pair *)
    let sigTconstr   = Coqlib.(lib_ref "core.sigT.type") in
    let existTconstr = Coqlib.lib_ref    "core.sigT.intro" in
    (* check whether the equality deals with dep pairs or not *)
    let eqTypeDest = fst (decompose_app sigma t) in
    if not (isRefX env sigma sigTconstr eqTypeDest) then raise_notrace Exit;
    let hd1,ar1 = decompose_app sigma t1 and
        hd2,ar2 = decompose_app sigma t2 in
    if not (isRefX env sigma existTconstr hd1) then raise_notrace Exit;
    if not (isRefX env sigma existTconstr hd2) then raise_notrace Exit;
    let (ind, _), _ = try pf_apply find_mrectype gl ar1.(0) with Not_found -> raise_notrace Exit in
    (* check if the user has declared the dec principle *)
    (* and compare the fst arguments of the dep pair *)
    (* Note: should work even if not an inductive type, but the table only *)
    (* knows inductive types *)
    if not (Option.has_some (Ind_tables.lookup_scheme (!eq_dec_scheme_kind_name()) ind) &&
            pf_apply is_conv gl ar1.(2) ar2.(2)) then raise_notrace Exit;
    let inj2 = match lib_ref_opt "core.eqdep_dec.inj_pair2" with
      | None ->
        warn_inject_no_eqdep_dec (env,ind);
        raise_notrace Exit
      | Some v -> v
    in
    let new_eq_args = [|pf_get_type_of gl ar1.(3);ar1.(3);ar2.(3)|] in
    find_scheme (!eq_dec_scheme_kind_name()) ind >>= fun c ->
    let c = if Global.is_polymorphic (ConstRef c)
      then CErrors.anomaly Pp.(str "Unexpected univ poly in inject_if_homogenous_dependent_pair")
      else UnsafeMonomorphic.mkConst c
    in
    (* cut with the good equality and prove the requested goal *)
    tclTHENLIST
      [
       intro;
       onLastHyp (fun hyp ->
        Tacticals.pf_constr_of_global Coqlib.(lib_ref "core.eq.type") >>= fun ceq ->
        tclTHENS (cut (mkApp (ceq,new_eq_args)))
          [clear [destVar sigma hyp];
           Tacticals.pf_constr_of_global inj2 >>= fun inj2 ->
           Tactics.exact_check
             (mkApp(inj2,[|ar1.(0);c;ar1.(1);ar1.(2);ar1.(3);ar2.(3);hyp|]))
          ])]
  with Exit ->
    Proofview.tclUNIT ()
  end

(* Given t1=t2 Inj calculates the whd normal forms of t1 and t2 and it
   expands then only when the whdnf has a constructor of an inductive type
   in hd position, otherwise delta expansion is not done *)

let simplify_args env sigma t =
  (* Quick hack to reduce in arguments of eq only *)
  match decompose_app sigma t with
    | eq, [|t;c1;c2|] -> applist (eq,[t;simpl env sigma c1;simpl env sigma c2])
    | eq, [|t1;c1;t2;c2|] -> applist (eq,[t1;simpl env sigma c1;t2;simpl env sigma c2])
    | _ -> t

let inject_at_positions env sigma l2r eq posns tac =
  let { eq_data = (eq, (t,t1,t2)); eq_term = v; eq_evar = evs } = eq in
  let e = next_ident_away eq_baseid (vars_of_env env) in
  let e_env = push_named (LocalAssum (make_annot e ERelevance.relevant,t)) env in
  let evdref = ref sigma in
  let filter (cpath, t1', t2') =
    try
      (* arbitrarily take t1' as the injector default value *)
      let sigma, (injbody,resty) = build_injector e_env !evdref t1' (mkVar e) cpath in
      let injfun = mkNamedLambda sigma (make_annot e ERelevance.relevant) t injbody in
      let sigma,congr = Evd.fresh_global env sigma eq.congr in
      (* pf : eq t t1 t2 -> eq resty (injfun t1) (injfun t2) *)
      let mk c = Retyping.get_judgment_of env sigma c in
      let args = Array.map mk [|t; resty; injfun; t1; t2|] in
      let sigma, pf = Typing.judge_of_apply env sigma (mk congr) args in
      let { Environ.uj_val = pf; Environ.uj_type = pf_typ } = pf in
      let pf_typ = Vars.subst1 mkProp (pi3 @@ destProd sigma pf_typ) in
      let pf = mkApp (pf, [| v |]) in
      let ty = simplify_args env sigma pf_typ in
        evdref := sigma;
        Some (pf, ty)
    with Failure _ -> None
  in
  let injectors = List.map_filter filter posns in
  if List.is_empty injectors then
    tclZEROMSG (str "Failed to decompose the equality.")
  else
    let map (pf, ty) =
      tclTHENS (cut ty) [
        inject_if_homogenous_dependent_pair ty;
        Tactics.exact_check pf <*> Proofview.Unsafe.tclNEWGOALS evs;
    ] in
    Proofview.Unsafe.tclEVARS !evdref <*>
    Tacticals.tclTHENFIRST
      (Tacticals.tclMAP map (if l2r then List.rev injectors else injectors))
      (tac (List.length injectors))

exception NothingToInject
let () = CErrors.register_handler (function
  | NothingToInject -> Some (Pp.str "Nothing to inject.")
  | _ -> None)

let injEqThen keep_proofs tac l2r eql =
  Proofview.Goal.enter begin fun gl ->
  let { eq_data = (eq, (t,t1,t2)) } = eql in
  let sigma = Proofview.Goal.sigma gl in
  let env = Proofview.Goal.env gl in
  let id = try Some (destVar sigma eql.eq_term) with DestKO -> None in
  match find_positions env sigma ~keep_proofs ~no_discr:true t1 t2 with
  | Inl _ ->
     assert false
  | Inr [] ->
     let suggestion =
         if keep_proofs then
            "" else
            " You can try to use option Set Keep Proof Equalities." in
     tclZEROMSG (strbrk("No information can be deduced from this equality and the injectivity of constructors. This may be because the terms are convertible, or due to pattern matching restrictions in the sort Prop." ^ suggestion))
  | Inr [([],_,_)] ->
     Proofview.tclZERO NothingToInject
  | Inr posns ->
      inject_at_positions env sigma l2r eql posns
        (tac id)
  end

let get_previous_hyp_position id gl =
  let env, sigma = Proofview.Goal.(env gl, sigma gl) in
  let rec aux dest = function
  | [] -> raise (RefinerError (env, sigma, NoSuchHyp id))
  | d :: right ->
    let hyp = Context.Named.Declaration.get_id d in
    if Id.equal hyp id then dest else aux (MoveAfter hyp) right
  in
  aux MoveLast (Proofview.Goal.hyps gl)

let injEq flags ?(injection_in_context = injection_in_context_flag ()) with_evars clear_flag ipats =
  (* Decide which compatibility mode to use *)
  let ipats_style, l2r, dft_clear_flag, bounded_intro = match ipats with
    | None when injection_in_context -> Some [], true, true, true
    | None -> None, false, false, false
    | _ -> let b = use_injection_pattern_l2r_order flags in ipats, b, b, b in
  (* Built the post tactic depending on compatibility mode *)
  let post_tac id n =
    match ipats_style with
    | Some ipats ->
      Proofview.Goal.enter begin fun gl ->
        let destopt = match id with
        | Some id -> get_previous_hyp_position id gl
        | None -> MoveLast in
        let clear_tac =
          tclTRY (apply_clear_request clear_flag dft_clear_flag id) in
        (* Try should be removal if dependency were treated *)
        let intro_tac =
          if bounded_intro
          then intro_patterns_bound_to with_evars n destopt ipats
          else intro_patterns_to with_evars destopt ipats in
        tclTHEN clear_tac intro_tac
      end
    | None -> tclIDTAC in
  injEqThen (keep_proof_equalities flags) post_tac l2r

let inj flags ?injection_in_context ipats with_evars clear_flag =
  onEquality with_evars (injEq flags ?injection_in_context with_evars clear_flag ipats)

let injClause flags ?injection_in_context ipats with_evars = function
  | None -> onNegatedEquality with_evars (injEq flags ?injection_in_context with_evars None ipats)
  | Some c -> onInductionArg (inj flags ?injection_in_context ipats with_evars) c

let simpleInjClause flags with_evars = function
  | None -> onNegatedEquality with_evars (injEq flags ~injection_in_context:false with_evars None None)
  | Some c -> onInductionArg (fun clear_flag -> onEquality with_evars (injEq flags ~injection_in_context:false with_evars clear_flag None)) c

let injConcl flags ?injection_in_context () = injClause flags ?injection_in_context None false None
let injHyp flags ?injection_in_context clear_flag id = injClause flags ?injection_in_context None false (Some (clear_flag,ElimOnIdent CAst.(make id)))

let decompEqThen keep_proofs ntac eq =
  let { eq_data = (_, (_,t1,t2) as u) } = eq in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let ido = try Some (destVar sigma eq.eq_term) with DestKO -> None in
    match find_positions env sigma ~keep_proofs ~no_discr:false t1 t2 with
    | Inl (cpath, (_,dirn), _) ->
      discr_positions env sigma eq cpath dirn
    | Inr [] -> (* Change: do not fail, simplify clear this trivial hyp *)
      ntac ido 0
    | Inr posns ->
      inject_at_positions env sigma true eq posns (ntac ido)
  end

let dEqThen0 ~keep_proofs with_evars ntac = function
  | None -> onNegatedEquality with_evars (decompEqThen (use_keep_proofs keep_proofs) (ntac None))
  | Some c -> onInductionArg (fun clear_flag -> onEquality with_evars (decompEqThen (use_keep_proofs keep_proofs) (ntac clear_flag))) c

let dEq ~keep_proofs with_evars =
  dEqThen0 ~keep_proofs with_evars (fun clear_flag ido x ->
    (apply_clear_request clear_flag (use_clear_hyp_by_default ()) ido))

let dEqThen ~keep_proofs with_evars ntac where =
  dEqThen0 ~keep_proofs with_evars (fun _ _ n -> ntac n) where

let intro_decomp_eq tac (eq, _, data) (c, t) =
  Proofview.Goal.enter begin fun gl ->
    let eq = { eq_data = (eq, data); eq_term = c; eq_evar = [] } in
    decompEqThen !keep_proof_equalities_for_injection (fun _ -> tac) eq
  end

let () = declare_intro_decomp_eq intro_decomp_eq

(* [subst_tuple_term dep_pair B]

   Given that dep_pair looks like:

   (existT e1 (existT e2 ... (existT en en+1) ... ))

   of type {x1:T1 & {x2:T2(x1) & ... {xn:Tn(x1..xn-1) & en+1 } } }

   and B might contain instances of the ei, we will return the term:

   ([x1:ty1]...[xn+1:tyn+1]B
    (projT1 (mkRel 1))
    (projT1 (projT2 (mkRel 1)))
    ...
    (projT1 (projT2^n (mkRel 1)))
    (projT2 (projT2^n (mkRel 1)))

   That is, we will abstract out the terms e1...en+1 of types
   t1 (=_beta T1), ..., tn+1 (=_beta Tn+1(e1..en)) as usual, but
   will then produce a term in which the abstraction is on a single
   term - the debruijn index [mkRel 1], which will be of the same type
   as dep_pair (note that the abstracted body may not be typable!).

   ALGORITHM for abstraction:

   We have a list of terms, [e1]...[en+1], which we want to abstract
   out of [B].  For each term [ei], going backwards from [n+1], we
   just do a [subst_term], and then do a lambda-abstraction to the
   type of the [ei].

 *)

let decomp_tuple env sigma c =
  let rec decomprec accu ex = match find_sigma_data_decompose env sigma ex with
  | ({ proj1; proj2 }), (u, a, b, car, cdr) ->
    decomprec ((proj1, proj2, u, a, b, car, cdr) :: accu) cdr
  | exception Constr_matching.PatternMatchingFailure -> List.rev accu
  in
  decomprec [] c

let make_tuple_projs data =
  let fold accu (p1, p2, u, a, b, _, _) =
    let proj = applist (mkConstU (destConstRef p1, u), [a; b; accu]) in
    let accu = applist (mkConstU (destConstRef p2, u), [a; b; accu]) in
    accu, proj
  in
  let last, projs = List.fold_left_map fold (mkRel 1) data in
  projs @ [last]

let make_tuple_args sigma arg typ data =
  let fold _ (_, _, _, a, b, car, cdr) =
    let typ = beta_applist sigma (b, [car]) in
    (cdr, typ), (car, a)
  in
  let last, args = List.fold_left_map fold (arg, typ) data in
  args @ [last]

let subst_tuple_term env sigma dep_pair1 dep_pair2 body =
  let typ = get_type_of env sigma dep_pair1 in
  (* We find all possible decompositions *)
  let data1 = decomp_tuple env sigma dep_pair1 in
  let data2 = decomp_tuple env sigma dep_pair2 in
  (* We adjust to the shortest decomposition *)
  let n = min (List.length data1) (List.length data2) in
  let data1 = List.firstn n data1 in
  let data2 = List.firstn n data2 in
  (* We rewrite dep_pair1 ... *)
  let proj_list = make_tuple_projs data1 in
  let e1_list = make_tuple_args sigma dep_pair1 typ data1 in
  (* ... and use dep_pair2 to compute the expected goal *)
  let e2_list = make_tuple_args sigma dep_pair2 typ data2 in
  (* We build the expected goal *)
  let fold (e, t) body = lambda_create env sigma (ERelevance.relevant, t, subst_term sigma e body) in
  let abst_B = List.fold_right fold e1_list body in
  let ctx, abst_B = decompose_lambda_n_assum sigma (List.length e1_list) abst_B in
  (* Retype the body, it might be ill-typed if it depends on the abstracted subterms *)
  let sigma, _ = Typing.type_of (push_rel_context ctx env) sigma abst_B in
  let sigma =
    (* FIXME: this should be enforced before. We only have to check the last
       projection, since all previous ones mention a prefix of the subtypes. *)
    let env = push_rel (Rel.Declaration.LocalAssum (anonR, typ)) env in
    let sigma, _ = Typing.type_of env sigma (List.last proj_list) in
    sigma
  in
  let pred_body = Vars.substl (List.rev proj_list) abst_B in
  let body = mkApp (lambda_create env sigma (ERelevance.relevant,typ,pred_body),[|dep_pair1|]) in
  let expected_goal = Vars.substl (List.rev_map fst e2_list) abst_B in
  (* Simulate now the normalisation treatment made by Logic.mk_refgoals *)
  let expected_goal = nf_betaiota env sigma expected_goal in
  (sigma, (body, expected_goal))

(* Like "replace" but decompose dependent equalities                      *)
(* i.e. if equality is "exists t v = exists u w", and goal is "phi(t,u)", *)
(* then it uses the predicate "\x.phi(proj1_sig x,proj2_sig x)", and so   *)
(* on for further iterated sigma-tuples                                   *)

let cutSubstInConcl l2r eqn =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let (lbeq,u,(t,e1,e2)) = pf_apply find_eq_data_decompose gl eqn in
  let typ = pf_concl gl in
  let (e1,e2) = if l2r then (e1,e2) else (e2,e1) in
  let (sigma, (typ, expected)) = subst_tuple_term env sigma e1 e2 typ in
  tclTHEN (Proofview.Unsafe.tclEVARS sigma)
  (tclTHENFIRST
    (tclTHENLIST [
       (change_concl typ); (* Put in pattern form *)
       (replace_core onConcl l2r eqn)
    ])
    (change_concl expected)) (* Put in normalized form *)
  end

let cutSubstInHyp l2r eqn id =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let (lbeq,u,(t,e1,e2)) = pf_apply find_eq_data_decompose gl eqn in
  let typ = pf_get_hyp_typ id gl in
  let (e1,e2) = if l2r then (e1,e2) else (e2,e1) in
  let (sigma, (typ, expected)) = subst_tuple_term env sigma e1 e2 typ in
  tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (tclTHENFIRST
    (tclTHENLIST [
       (change_in_hyp ~check:true None (make_change_arg typ) (id,InHypTypeOnly));
       (replace_core (onHyp id) l2r eqn)
    ])
    (change_in_hyp ~check:true None (make_change_arg expected) (id,InHypTypeOnly)))
  end

let try_rewrite tac =
  Proofview.tclORELSE tac begin function (e, info) -> match e with
    | Constr_matching.PatternMatchingFailure ->
      tclZEROMSG ~info (str "Not a primitive equality here.")
    | e ->
      (* XXX: absorbing anomalies?? *)
      tclZEROMSG ~info
        (strbrk "Cannot find a well-typed generalization of the goal that makes the proof progress.")
  end

let cutSubstClause l2r eqn cls =
  match cls with
    | None ->    cutSubstInConcl l2r eqn
    | Some id -> cutSubstInHyp l2r eqn id

let substClause l2r c cls =
  Proofview.Goal.enter begin fun gl ->
  let eq = pf_apply get_type_of gl c in
  tclTHENS (cutSubstClause l2r eq cls)
    [Proofview.tclUNIT (); exact_no_check c]
  end

let rewriteClause l2r c cls = try_rewrite (substClause l2r c cls)
let rewriteInHyp l2r c id = rewriteClause l2r c (Some id)
let rewriteInConcl l2r c = rewriteClause l2r c None

(* Naming scheme for rewrite tactics

      give equality        give proof of equality

    / cutSubstClause       substClause
raw | cutSubstInHyp        substInHyp
    \ cutSubstInConcl      substInConcl

raw = raise typing error or PatternMatchingFailure
user = raise user error specific to rewrite
*)

(**********************************************************************)
(* Substitutions tactics (JCF) *)

let restrict_to_eq_and_identity env eq = (* compatibility *)
  let is_ref b = match Coqlib.lib_ref_opt b with
    | None -> false
    | Some b -> Environ.QGlobRef.equal env eq b
  in
  if not (List.exists is_ref ["core.eq.type"; "core.identity.type"])
  then raise Constr_matching.PatternMatchingFailure

exception FoundHyp of (Id.t * constr * bool)

(* tests whether hyp [c] is [x = t] or [t = x], [x] not occurring in [t] *)
let is_eq_x gl x d =
  let id = NamedDecl.get_id d in
  try
    let is_var id c = match EConstr.kind (project gl) c with
    | Var id' -> Id.equal id id'
    | _ -> false
    in
    let c = pf_nf_evar gl (NamedDecl.get_type d) in
    let (_,lhs,rhs) = pi3 (pf_apply find_eq_data_decompose gl c) in
    if (is_var x lhs) && not (local_occur_var (project gl) x rhs) then raise (FoundHyp (id,rhs,true));
    if (is_var x rhs) && not (local_occur_var (project gl) x lhs) then raise (FoundHyp (id,lhs,false))
  with Constr_matching.PatternMatchingFailure ->
    ()

exception FoundDepInGlobal of Id.t option * GlobRef.t

let test_non_indirectly_dependent_section_variable gl x =
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.project gl in
  let hyps = Proofview.Goal.hyps gl in
  let concl = Proofview.Goal.concl gl in
  List.iter (fun decl ->
    NamedDecl.iter_constr (fun c ->
      match occur_var_indirectly env sigma x c with
      | Some gr -> raise (FoundDepInGlobal (Some (NamedDecl.get_id decl), gr))
      | None -> ()) decl) hyps;
  match occur_var_indirectly env sigma x concl with
    | Some gr -> raise (FoundDepInGlobal (None, gr))
    | None -> ()

let check_non_indirectly_dependent_section_variable gl x =
  try test_non_indirectly_dependent_section_variable gl x
  with FoundDepInGlobal (pos,gr) ->
    let where = match pos with
      | Some id -> str "hypothesis " ++ Id.print id
      | None -> str "the conclusion of the goal" in
    user_err
      (strbrk "Section variable " ++ Id.print x ++
       strbrk " occurs implicitly in global declaration " ++ Printer.pr_global gr ++
       strbrk " present in " ++ where ++ strbrk ".")

let is_non_indirectly_dependent_section_variable gl z =
  try test_non_indirectly_dependent_section_variable gl z; true
  with FoundDepInGlobal (pos,gr) -> false

(* Rewrite "hyp:x=rhs" or "hyp:rhs=x" (if dir=false) everywhere and
   erase hyp and x; proceed by generalizing all dep hyps *)

let subst_one dep_proof_ok x (hyp,rhs,dir) =
  Proofview.Goal.enter begin fun gl ->
  let sigma = Tacmach.project gl in
  let hyps = Proofview.Goal.hyps gl in
  let concl = Proofview.Goal.concl gl in
  (* The set of hypotheses using x *)
  let dephyps =
    List.rev (pi3 (List.fold_right (fun dcl (dest,deps,allhyps) ->
      let id = NamedDecl.get_id dcl in
      if not (Id.equal id hyp)
         && List.exists (fun y -> local_occur_var_in_decl sigma y dcl) deps
      then
        (dest,id::deps,(dest,id)::allhyps)
      else
        (MoveBefore id,deps,allhyps))
      hyps
      (MoveBefore x,[x],[]))) in (* In practice, no dep hyps before x, so MoveBefore x is good enough *)
  (* Decides if x appears in conclusion *)
  let depconcl = local_occur_var sigma x concl in
  let need_rewrite = not (List.is_empty dephyps) || depconcl in
  tclTHENLIST
    ((if need_rewrite then
      [Generalize.revert (List.map snd dephyps);
       general_rewrite ~where:None ~l2r:dir AtLeastOneOccurrence ~freeze:true ~dep:dep_proof_ok ~with_evars:false (mkVar hyp, NoBindings);
       (tclMAP (fun (dest,id) -> intro_move (Some id) dest) dephyps)]
      else
       [Proofview.tclUNIT ()]) @
     [tclTRY (clear [x; hyp])])
  end

(* Look for an hypothesis hyp of the form "x=rhs" or "rhs=x", rewrite
   it everywhere, and erase hyp and x; proceed by generalizing all dep hyps *)

let subst_one_var dep_proof_ok x =
  Proofview.Goal.enter begin fun gl ->
    let decl = pf_get_hyp x gl in
    (* If x has a body, simply replace x with body and clear x *)
    if is_local_def decl then tclTHEN (unfold_body x) (clear [x]) else
      (* Find a non-recursive definition for x *)
      let res =
        try
          (* [is_eq_x] ensures nf_evar on its side *)
          let hyps = Proofview.Goal.hyps gl in
          let test hyp _ = is_eq_x gl x hyp in
          Context.Named.fold_outside test ~init:() hyps;
          user_err
            (str "Cannot find any non-recursive equality over " ++ Id.print x ++
               str".")
        with FoundHyp res -> res in
      if is_section_variable (Global.env ()) x then
        check_non_indirectly_dependent_section_variable gl x;
      subst_one dep_proof_ok x res
  end

let subst_gen dep_proof_ok ids =
  tclMAP (subst_one_var dep_proof_ok) ids

(* For every x, look for an hypothesis hyp of the form "x=rhs" or "rhs=x",
   rewrite it everywhere, and erase hyp and x; proceed by generalizing
   all dep hyps *)

let subst = subst_gen true

type subst_tactic_flags = {
  only_leibniz : bool;
  rewrite_dependent_proof : bool
}

let default_subst_tactic_flags =
  { only_leibniz = false; rewrite_dependent_proof = true }

let warn_deprecated_simple_subst =
  CWarnings.create ~name:"deprecated-simple-subst" ~category:Deprecation.Version.v8_8
    (fun () -> strbrk"\"simple subst\" is deprecated")

let subst_all ?(flags=default_subst_tactic_flags) () =

  let () =
    if flags.only_leibniz || not flags.rewrite_dependent_proof then
      warn_deprecated_simple_subst ()
  in

  (* Find hypotheses to treat in linear time *)
  let process hyp =
    Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = project gl in
    let c = pf_get_hyp hyp gl |> NamedDecl.get_type in
    try
      let lbeq,u,(_,x,y) = pf_apply find_eq_data_decompose gl c in
      if flags.only_leibniz then restrict_to_eq_and_identity env lbeq.eq;
      match EConstr.kind sigma x, EConstr.kind sigma y with
      | Var x, Var y when Id.equal x y ->
          Proofview.tclUNIT ()
      | Var x', _ when not (Termops.local_occur_var sigma x' y) &&
                      not (is_evaluable env (EvalVarRef x')) &&
                      is_non_indirectly_dependent_section_variable gl x' ->
          subst_one flags.rewrite_dependent_proof x' (hyp,y,true)
      | _, Var y' when not (Termops.local_occur_var sigma y' x) &&
                      not (is_evaluable env (EvalVarRef y')) &&
                      is_non_indirectly_dependent_section_variable gl y' ->
          subst_one flags.rewrite_dependent_proof y' (hyp,x,false)
      | _ ->
          Proofview.tclUNIT ()
    with Constr_matching.PatternMatchingFailure ->
        Proofview.tclUNIT ()
      end
  in
  Proofview.Goal.enter begin fun gl ->
    tclMAP process (List.rev (List.map NamedDecl.get_id (Proofview.Goal.hyps gl)))
  end

(* Rewrite the first assumption for which a condition holds
   and gives the direction of the rewrite *)

let cond_eq_term_left c t gl =
  try
    let (_,x,_) = pi3 (pf_apply find_eq_data_decompose gl t) in
    if pf_conv_x gl c x then true else failwith "not convertible"
  with Constr_matching.PatternMatchingFailure -> failwith "not an equality"

let cond_eq_term_right c t gl =
  try
    let (_,_,x) = pi3 (pf_apply find_eq_data_decompose gl t) in
    if pf_conv_x gl c x then false else failwith "not convertible"
  with Constr_matching.PatternMatchingFailure -> failwith "not an equality"

let cond_eq_term c t gl =
  try
    let (_,x,y) = pi3 (pf_apply find_eq_data_decompose gl t) in
    if pf_conv_x gl c x then true
    else if pf_conv_x gl c y then false
    else failwith "not convertible"
  with Constr_matching.PatternMatchingFailure -> failwith "not an equality"

let rewrite_assumption_cond cond_eq_term cl =
  let rec arec hyps gl = match hyps with
    | [] -> user_err Pp.(str "No such assumption.")
    | hyp ::rest ->
        let id = NamedDecl.get_id hyp in
        begin
          try
            let dir = cond_eq_term (NamedDecl.get_type hyp) gl in
            general_rewrite_clause dir false (mkVar id,NoBindings) cl
          with | Failure _ | UserError _ -> arec rest gl
        end
  in
  Proofview.Goal.enter begin fun gl ->
    let hyps = Proofview.Goal.hyps gl in
    arec hyps gl
  end

(* Generalize "subst x" to substitution of subterm appearing as an
   equation in the context, but not clearing the hypothesis *)

let replace_term dir_opt c  =
  let cond_eq_fun =
    match dir_opt with
      | None -> cond_eq_term c
      | Some true -> cond_eq_term_left c
      | Some false -> cond_eq_term_right c
  in
  rewrite_assumption_cond cond_eq_fun

(* Declare rewriting tactic for intro patterns "<-" and "->" *)

let () =
  let gmr l2r with_evars tac c = general_rewrite_clause l2r with_evars tac c in
  Hook.set Tactics.general_rewrite_clause gmr

let () = Hook.set Tactics.subst_one subst_one
