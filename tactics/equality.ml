(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
open Termops
open EConstr
open Vars
open Namegen
open Inductive
open Inductiveops
open Libnames
open Globnames
open Reductionops
open Typing
open Retyping
open Tacmach.New
open Logic
open Hipattern
open Tacticals.New
open Tactics
open Tacred
open Coqlib
open Declarations
open Indrec
open Clenv
open Evd
open Ind_tables
open Eqschemes
open Locus
open Locusops
open Tactypes
open Proofview.Notations
open Unification
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration

(* Options *)

type inj_flags = {
    keep_proof_equalities : bool;
    injection_in_context : bool;
    injection_pattern_l2r_order : bool;
  }

open Goptions

let use_injection_pattern_l2r_order = function
  | None -> true
  | Some flags -> flags.injection_pattern_l2r_order

let injection_in_context = ref false

let use_injection_in_context = function
  | None -> !injection_in_context
  | Some flags -> flags.injection_in_context

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "injection in context";
      optkey   = ["Structural";"Injection"];
      optread  = (fun () -> !injection_in_context) ;
      optwrite = (fun b -> injection_in_context := b) }

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
  modulo_delta = empty_transparent_state;
  modulo_delta_types = empty_transparent_state;
  check_applied_meta_types = true;
  use_pattern_unification = true;
  use_meta_bound_pattern_unification = true;
  frozen_evars = Evar.Set.empty;
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

let freeze_initial_evars sigma flags clause =
  (* We take evars of the type: this may include old evars! For excluding *)
  (* all old evars, including the ones occurring in the rewriting lemma, *)
  (* we would have to take the clenv_value *)
  let newevars = Evarutil.undefined_evars_of_term sigma (clenv_type clause) in
  let evars =
    fold_undefined (fun evk _ evars ->
      if Evar.Set.mem evk newevars then evars
      else Evar.Set.add evk evars)
      sigma Evar.Set.empty in
  {flags with
    core_unify_flags = {flags.core_unify_flags with frozen_evars = evars};
    merge_unify_flags = {flags.merge_unify_flags with frozen_evars = evars};
    subterm_unify_flags = {flags.subterm_unify_flags with frozen_evars = evars}}

let make_flags frzevars sigma flags clause =
  if frzevars then freeze_initial_evars sigma flags clause else flags

let side_tac tac sidetac =
  match sidetac with
  | None -> tac
  | Some sidetac -> tclTHENSFIRSTn tac [|Proofview.tclUNIT ()|] sidetac

let instantiate_lemma_all frzevars gl c ty l l2r concl =
  let env = Proofview.Goal.env gl in
  let sigma = project gl in
  let eqclause = pf_apply Clenv.make_clenv_binding gl (c,ty) l in
  let (equiv, args) = decompose_app_vect sigma (Clenv.clenv_type eqclause) in
  let arglen = Array.length args in
  let () = if arglen < 2 then user_err Pp.(str "The term provided is not an applied relation.") in
  let c1 = args.(arglen - 2) in
  let c2 = args.(arglen - 1) in
  let try_occ (evd', c') =
    Clenvtac.clenv_pose_dependent_evars ~with_evars:true {eqclause with evd = evd'}
  in
  let flags = make_flags frzevars (Tacmach.New.project gl) rewrite_unif_flags eqclause in
  let occs =
    w_unify_to_subterm_all ~flags env eqclause.evd
      ((if l2r then c1 else c2),concl)
  in List.map try_occ occs

let instantiate_lemma gl c ty l l2r concl =
  let sigma, ct = pf_type_of gl c in
  let t = try snd (reduce_to_quantified_ind (pf_env gl) sigma ct) with UserError _ -> ct in
  let eqclause = Clenv.make_clenv_binding (pf_env gl) sigma (c,t) l in
  [eqclause]

let rewrite_conv_closed_core_unif_flags = {
  modulo_conv_on_closed_terms = Some full_transparent_state;
    (* We have this flag for historical reasons, it has e.g. the consequence *)
    (* to rewrite "?x+2" in "y+(1+1)=0" or to rewrite "?x+?x" in "2+(1+1)=0" *)

  use_metas_eagerly_in_conv_on_closed_terms = true;
  use_evars_eagerly_in_conv_on_closed_terms = false;
    (* Combined with modulo_conv_on_closed_terms, this flag allows since 8.2 *)
    (* to rewrite e.g. "?x+(2+?x)" in "1+(1+2)=0" *)

  modulo_delta = empty_transparent_state;
  modulo_delta_types = full_transparent_state;
  check_applied_meta_types = true;
  use_pattern_unification = true;
    (* To rewrite "?n x y" in "y+x=0" when ?n is *)
    (* a preexisting evar of the goal*)

  use_meta_bound_pattern_unification = true;

  frozen_evars = Evar.Set.empty;
    (* This is set dynamically *)

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
  modulo_conv_on_closed_terms = Some full_transparent_state;
    (* We have this flag for historical reasons, it has e.g. the consequence *)
    (* to rewrite "?x+2" in "y+(1+1)=0" or to rewrite "?x+?x" in "2+(1+1)=0" *)

  use_metas_eagerly_in_conv_on_closed_terms = true;
  use_evars_eagerly_in_conv_on_closed_terms = false;
    (* Combined with modulo_conv_on_closed_terms, this flag allows since 8.2 *)
    (* to rewrite e.g. "?x+(2+?x)" in "1+(1+2)=0" *)

  modulo_delta = full_transparent_state;
  modulo_delta_types = full_transparent_state;
  check_applied_meta_types = true;
  use_pattern_unification = true;
    (* To rewrite "?n x y" in "y+x=0" when ?n is *)
    (* a preexisting evar of the goal*)

  use_meta_bound_pattern_unification = true;

  frozen_evars = Evar.Set.empty;
    (* This is set dynamically *)

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

let rewrite_elim with_evars frzevars cls c e =
  Proofview.Goal.enter begin fun gl ->
  let flags = if Unification.is_keyed_unification ()
	      then rewrite_keyed_unif_flags else rewrite_conv_closed_unif_flags in
  let flags = make_flags frzevars (Tacmach.New.project gl) flags c in
  general_elim_clause with_evars flags cls c e
  end

let tclNOTSAMEGOAL tac =
  let goal gl = Proofview.Goal.goal gl in
  Proofview.Goal.nf_enter begin fun gl ->
    let sigma = project gl in
    let ev = goal gl in
    tac >>= fun () ->
    Proofview.Goal.goals >>= fun gls ->
    let check accu gl' =
      gl' >>= fun gl' ->
      let accu = accu || Goal.V82.same_goal sigma ev (project gl') (goal gl') in
      Proofview.tclUNIT accu
    in
    Proofview.Monad.List.fold_left check false gls >>= fun has_same ->
    if has_same then
      tclZEROMSG (str"Tactic generated a subgoal identical to the original goal.")
    else
      Proofview.tclUNIT ()
  end

(* Ad hoc asymmetric general_elim_clause *)
let general_elim_clause with_evars frzevars cls rew elim =
  let open Pretype_errors in
  Proofview.tclORELSE
    begin match cls with
    | None ->
      (* was tclWEAK_PROGRESS which only fails for tactics generating one
          subgoal and did not fail for useless conditional rewritings generating
          an extra condition *)
      tclNOTSAMEGOAL (rewrite_elim with_evars frzevars cls rew elim)
    | Some _ -> rewrite_elim with_evars frzevars cls rew elim
    end
    begin function (e, info) -> match e with
    | PretypeError (env, evd, NoOccurrenceFound (c', _)) ->
      Proofview.tclZERO (PretypeError (env, evd, NoOccurrenceFound (c', cls)))
    | e -> Proofview.tclZERO ~info e
    end

let general_elim_clause with_evars frzevars tac cls c t l l2r elim =
  let all, firstonly, tac =
    match tac with
    | None -> false, false, None
    | Some (tac, Naive) -> false, false, Some tac
    | Some (tac, FirstSolved) -> true, true, Some (tclCOMPLETE tac)
    | Some (tac, AllMatches) -> true, false, Some (tclCOMPLETE tac)
  in
  let try_clause c =
    side_tac
      (tclTHEN
         (Proofview.Unsafe.tclEVARS c.evd)
         (general_elim_clause with_evars frzevars cls c elim))
      tac
  in
  Proofview.Goal.enter begin fun gl ->
    let instantiate_lemma concl =
      if not all then instantiate_lemma gl c t l l2r concl
      else instantiate_lemma_all frzevars gl c t l l2r concl
    in
    let typ = match cls with
    | None -> pf_concl gl
    | Some id -> pf_get_hyp_typ id gl
    in
    let cs = instantiate_lemma typ in
    if firstonly then tclFIRST (List.map try_clause cs)
    else tclMAP try_clause cs
  end

(* The next function decides in particular whether to try a regular
  rewrite or a generalized rewrite.
  Approach is to break everything, if [eq] appears in head position
  then regular rewrite else try general rewrite.
  If occurrences are set, use general rewrite.
*)

let (forward_general_setoid_rewrite_clause, general_setoid_rewrite_clause) = Hook.make ()

(* Do we have a JMeq instance on twice the same domains ? *)

let jmeq_same_dom env sigma = function
  | None -> true (* already checked in Hipattern.find_eq_data_decompose *)
  | Some t ->
    let rels, t = decompose_prod_assum sigma t in
    let env = push_rel_context rels env in
    match decompose_app sigma t with
      | _, [dom1; _; dom2;_] -> is_conv env sigma dom1 dom2
      | _ -> false

(* find_elim determines which elimination principle is necessary to
   eliminate lbeq on sort_of_gl. *)

let find_elim hdcncl lft2rgt dep cls ot =
  Proofview.Goal.enter_one begin fun gl ->
  let sigma = project gl in
  let is_global gr c = Termops.is_global sigma gr c in
  let inccl = Option.is_empty cls in
  let env = Proofview.Goal.env gl in
  if (is_global Coqlib.glob_eq hdcncl ||
      (is_global Coqlib.glob_jmeq hdcncl &&
	 jmeq_same_dom env sigma ot)) && not dep
  then
    let c = 
      match EConstr.kind sigma hdcncl with 
      | Ind (ind_sp,u) -> 
	let pr1 = 
	  lookup_eliminator ind_sp (elimination_sort_of_clause cls gl) 
	in
        begin match lft2rgt, cls with
        | Some true, None
        | Some false, Some _ ->
	  let c1 = destConstRef pr1 in 
	  let mp,dp,l = Constant.repr3 (Constant.make1 (Constant.canonical c1)) in 
	  let l' = Label.of_id (add_suffix (Label.to_id l) "_r")  in 
	  let c1' = Global.constant_of_delta_kn (KerName.make mp dp l') in
	  begin 
	    try 
	      let _ = Global.lookup_constant c1' in
		c1'
	    with Not_found -> 
	      user_err ~hdr:"Equality.find_elim"
                (str "Cannot find rewrite principle " ++ Label.print l' ++ str ".")
	  end
	| _ -> destConstRef pr1
        end
      | _ -> 
	  (* cannot occur since we checked that we are in presence of 
	     Logic.eq or Jmeq just before *)
	assert false
    in
        pf_constr_of_global (ConstRef c) 
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
  | Ind (ind,u) -> 
      
      let c, eff = find_scheme scheme_name ind in 
      Proofview.tclEFFECTS eff <*>
        pf_constr_of_global (ConstRef c) 
  | _ -> assert false
  end

let type_of_clause cls gl = match cls with
  | None -> Proofview.Goal.concl gl
  | Some id -> pf_get_hyp_typ id gl

let leibniz_rewrite_ebindings_clause cls lft2rgt tac c t l with_evars frzevars dep_proof_ok hdcncl =
  Proofview.Goal.enter begin fun gl ->
  let evd = Proofview.Goal.sigma gl in
  let isatomic = isProd evd (whd_zeta evd hdcncl) in
  let dep_fun = if isatomic then dependent else dependent_no_evar in
  let type_of_cls = type_of_clause cls gl in
  let dep = dep_proof_ok && dep_fun evd c type_of_cls in
  find_elim hdcncl lft2rgt dep cls (Some t) >>= fun elim ->
      general_elim_clause with_evars frzevars tac cls c t l
      (match lft2rgt with None -> false | Some b -> b)
      {elimindex = None; elimbody = (elim,NoBindings); elimrename = None}
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

let general_rewrite_ebindings_clause cls lft2rgt occs frzevars dep_proof_ok ?tac
    ((c,l) : constr with_bindings) with_evars =
  if occs != AllOccurrences then (
    rewrite_side_tac (Hook.get forward_general_setoid_rewrite_clause cls lft2rgt occs (c,l) ~new_goals:[]) tac)
  else
    Proofview.Goal.enter begin fun gl ->
      let sigma = Tacmach.New.project gl in
      let env = Proofview.Goal.env gl in
    let ctype = get_type_of env sigma c in
    let rels, t = decompose_prod_assum sigma (whd_betaiotazeta sigma ctype) in
      match match_with_equality_type sigma t with
      | Some (hdcncl,args) -> (* Fast path: direct leibniz-like rewrite *)
	  let lft2rgt = adjust_rewriting_direction args lft2rgt in
          leibniz_rewrite_ebindings_clause cls lft2rgt tac c (it_mkProd_or_LetIn t rels)
	    l with_evars frzevars dep_proof_ok hdcncl
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
	          let rels',t' = splay_prod_assum env' sigma t in (* Search for underlying eq *)
	          match match_with_equality_type sigma t' with
	            | Some (hdcncl,args) ->
		  let lft2rgt = adjust_rewriting_direction args lft2rgt in
		  leibniz_rewrite_ebindings_clause cls lft2rgt tac c
		    (it_mkProd_or_LetIn t' (rels' @ rels)) l with_evars frzevars dep_proof_ok hdcncl
	            | None -> Proofview.tclZERO ~info e
            (* error "The provided term does not end with an equality or a declared rewrite relation." *)  
            end
    end

let general_rewrite_ebindings =
  general_rewrite_ebindings_clause None

let general_rewrite_bindings l2r occs frzevars dep_proof_ok ?tac (c,bl) =
  general_rewrite_ebindings_clause None l2r occs
    frzevars dep_proof_ok ?tac (c,bl)

let general_rewrite l2r occs frzevars dep_proof_ok ?tac c =
  general_rewrite_bindings l2r occs
    frzevars dep_proof_ok ?tac (c,NoBindings) false

let general_rewrite_ebindings_in l2r occs frzevars dep_proof_ok ?tac id =
  general_rewrite_ebindings_clause (Some id) l2r occs frzevars dep_proof_ok ?tac

let general_rewrite_bindings_in l2r occs frzevars dep_proof_ok ?tac id (c,bl) =
  general_rewrite_ebindings_clause (Some id) l2r occs
    frzevars dep_proof_ok ?tac (c,bl)

let general_rewrite_in l2r occs frzevars dep_proof_ok ?tac id c =
  general_rewrite_ebindings_clause (Some id) l2r occs
    frzevars dep_proof_ok ?tac (c,NoBindings)

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
	      (general_rewrite_ebindings_in l2r (occs_of occs) false true ?tac id c with_evars)
	      (do_hyps l)
	in
	if cl.concl_occs == NoOccurrences then do_hyps l else
	  tclTHENFIRST
	    (general_rewrite_ebindings l2r (occs_of cl.concl_occs) false true ?tac c with_evars)
            (do_hyps l)
    | None ->
	(* Otherwise, if we are told to rewrite in all hypothesis via the
           syntax "* |-", we fail iff all the different rewrites fail *)
	let rec do_hyps_atleastonce = function
	  | [] -> tclZEROMSG (Pp.str"Nothing to rewrite.")
	  | id :: l ->
            tclIFTHENFIRSTTRYELSEMUST
	     (general_rewrite_ebindings_in l2r AllOccurrences false true ?tac id c with_evars)
	     (do_hyps_atleastonce l)
	in
	let do_hyps =
	  (* If the term to rewrite uses an hypothesis H, don't rewrite in H *)
	  let ids gl =
	    let ids_in_c = Termops.global_vars_set (Proofview.Goal.env gl) (project gl) (fst c) in
            let ids_of_hyps = pf_ids_of_hyps gl in
	    Id.Set.fold (fun id l -> List.remove Id.equal id l) ids_in_c ids_of_hyps
	  in
          Proofview.Goal.enter begin fun gl ->
            do_hyps_atleastonce (ids gl)
          end
	in
	if cl.concl_occs == NoOccurrences then do_hyps else
          tclIFTHENFIRSTTRYELSEMUST
	   (general_rewrite_ebindings l2r (occs_of cl.concl_occs) false true ?tac c with_evars)
	   do_hyps

let apply_special_clear_request clear_flag f =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Tacmach.New.project gl in
    let env = Proofview.Goal.env gl in
    try
      let (sigma, (c, bl)) = f env sigma in
      apply_clear_request clear_flag (use_clear_hyp_by_default ()) c
    with
      e when catchable_exception e -> tclIDTAC
  end

type multi =
  | Precisely of int
  | UpTo of int
  | RepeatStar
  | RepeatPlus

let general_multi_rewrite with_evars l cl tac =
  let do1 l2r f =
    Proofview.Goal.enter begin fun gl ->
      let sigma = Tacmach.New.project gl in
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

let rewriteLR = general_rewrite true AllOccurrences true true
let rewriteRL = general_rewrite false AllOccurrences true true

(* Replacing tactics *)

let classes_dirpath =
  DirPath.make (List.map Id.of_string ["Classes";"Coq"])

let init_setoid () =
  if is_dirpath_prefix_of classes_dirpath (Lib.cwd ()) then ()
  else Coqlib.check_required_library ["Coq";"Setoids";"Setoid"]

let check_setoid cl = 
  Option.fold_left
    ( List.fold_left 
	(fun b ((occ,_),_) -> 
	  b||(Locusops.occurrences_map (fun x -> x) occ <> AllOccurrences)
	)
    )
    ((Locusops.occurrences_map (fun x -> x) cl.concl_occs <> AllOccurrences) &&
	(Locusops.occurrences_map (fun x -> x) cl.concl_occs <> NoOccurrences))
    cl.onhyps

let replace_core clause l2r eq =
  if check_setoid clause
  then init_setoid ();
  tclTHENFIRST
    (assert_as false None None eq)
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
  let try_prove_eq =
    match try_prove_eq_opt with
      | None -> Proofview.tclUNIT ()
      | Some tac ->  tclCOMPLETE tac
  in
  Proofview.Goal.enter begin fun gl ->
  let get_type_of = pf_apply get_type_of gl in
  let t1 = get_type_of c1
  and t2 = get_type_of c2 in
  let evd = 
    if unsafe then Some (Tacmach.New.project gl)
    else
      try Some (Evarconv.the_conv_x (Proofview.Goal.env gl) t1 t2 (Tacmach.New.project gl))
      with Evarconv.UnableToUnify _ -> None
  in
  match evd with
  | None ->
    tclFAIL 0 (str"Terms do not have convertible types")
  | Some evd ->
    let e = build_coq_eq () in
    let sym = build_coq_eq_sym () in
    Tacticals.New.pf_constr_of_global sym >>= fun sym ->
    Tacticals.New.pf_constr_of_global e >>= fun e ->
    let eq = applist (e, [t1;c1;c2]) in
    tclTHENLAST
      (replace_core clause l2r eq)
      (tclFIRST
         [assumption;
          tclTHEN (apply sym) assumption;
          try_prove_eq
         ])
  end

let replace c1 c2 =
  replace_using_leibniz onConcl c2 c1 false false None

let replace_by c1 c2 tac =
  replace_using_leibniz onConcl c2 c1 false false (Some tac)

let replace_in_clause_maybe_by c1 c2 cl tac_opt =
  replace_using_leibniz cl c2 c1 false false tac_opt

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

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "injection on prop arguments";
      optkey   = ["Keep";"Proof";"Equalities"];
      optread  = (fun () -> !keep_proof_equalities_for_injection) ;
      optwrite = (fun b -> keep_proof_equalities_for_injection := b) }

let keep_proof_equalities = function
  | None -> !keep_proof_equalities_for_injection
  | Some flags -> flags.keep_proof_equalities

(* [keep_proofs] is relevant for types in Prop with elimination in Type *)
(* In particular, it is relevant for injection but not for discriminate *)

let find_positions env sigma ~keep_proofs ~no_discr t1 t2 =
  let project env sorts posn t1 t2 =
    let ty1 = get_type_of env sigma t1 in
    let s = get_sort_family_of ~truncation_style:true env sigma ty1 in
    if Sorts.List.mem s sorts
    then [(List.rev posn,t1,t2)] else []
  in
  let rec findrec sorts posn t1 t2 =
    let hd1,args1 = whd_all_stack env sigma t1 in
    let hd2,args2 = whd_all_stack env sigma t2 in
    match (EConstr.kind sigma hd1, EConstr.kind sigma hd2) with
      | Construct ((ind1,i1 as sp1),u1), Construct (sp2,_)
          when Int.equal (List.length args1) (constructor_nallargs_env env sp1)
            ->
	  let sorts' =
            Sorts.List.intersect sorts (allowed_sorts env (fst sp1))
          in
          (* both sides are fully applied constructors, so either we descend,
             or we can discriminate here. *)
	  if eq_constructor sp1 sp2 then
	    let nparams = inductive_nparams_env env ind1 in
	    let params1,rargs1 = List.chop nparams args1 in
	    let _,rargs2 = List.chop nparams args2 in
            let (mib,mip) = lookup_mind_specif env ind1 in
            let params1 = List.map EConstr.Unsafe.to_constr params1 in
            let u1 = EInstance.kind sigma u1 in
            let ctxt = (get_constructor ((ind1,u1),mib,mip,params1) i1).cs_args in
            let adjust i = CVars.adjust_rel_to_rel_context ctxt (i+1) - 1 in
            List.flatten
	      (List.map2_i (fun i -> findrec sorts' ((sp1,adjust i)::posn))
		0 rargs1 rargs2)
	  else if Sorts.List.mem InType sorts' && not no_discr
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

let discriminable env sigma t1 t2 =
  match find_positions env sigma ~keep_proofs:false ~no_discr:false t1 t2 with
    | Inl _ -> true
    | _ -> false

let injectable env sigma ~keep_proofs t1 t2 =
    match find_positions env sigma ~keep_proofs:(use_keep_proofs keep_proofs) ~no_discr:true t1 t2 with
    | Inl _ -> assert false
    | Inr [] | Inr [([],_,_)] -> false
    | Inr _ -> true


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
  let IndType (indf,_) =
    try find_rectype env sigma (get_type_of env sigma head)
    with Not_found ->
      user_err Pp.(str "Cannot project on an inductive type derived from a dependency.") 
  in
  let indp,_ = (dest_ind_family indf) in
  let ind, _ = check_privacy env indp in
  let (mib,mip) = lookup_mind_specif env ind in
  let cstr = get_constructors env indf in
  let dirn_nlams = cstr.(dirn-1).cs_nargs in
  let dirn_env = Environ.push_rel_context cstr.(dirn-1).cs_args env in
  (dirn_nlams,
   dirn_env,
   (fun sigma dirnval (dfltval,resty) ->
      let deparsign = make_arity_signature env sigma true indf in
      let p =
	it_mkLambda_or_LetIn (lift (mip.mind_nrealargs+1) resty) deparsign in
      let build_branch i =
	let result = if Int.equal i dirn then dirnval else dfltval in
	let cs_args = List.map (fun d -> map_rel_decl EConstr.of_constr d) cstr.(i-1).cs_args in
	let args = name_context env sigma cs_args in
	it_mkLambda_or_LetIn result args in
      let brl =
        List.map build_branch
          (List.interval 1 (Array.length mip.mind_consnames)) in
      let ci = make_case_info env ind RegularStyle in
      Inductiveops.make_case_or_project env sigma indf ci p head (Array.of_list brl)))

(* Now we need to construct the discriminator, given a discriminable
   position.  This boils down to:

   (1) If the position is directly beneath us, then we need to do a
   case-split, with result-type Prop, and stick True and False into
   the branches, as is convenient.

   (2) If the position is not directly beneath us, then we need to
   call descend_then, to descend one step, and then recursively
   construct the discriminator.

 *)

(* [construct_discriminator env sigma dirn c ind special default]]
   constructs a case-split on [c] of type [ind], with the [dirn]-th
   branch giving [special], and all the rest giving [default]. *)

let build_selector env sigma dirn c ind special default =
  let IndType(indf,_) =
    try find_rectype env sigma ind
    with Not_found ->
       (* one can find Rel(k) in case of dependent constructors
          like T := c : (A:Set)A->T and a discrimination
          on (c bool true) = (c bool false)
          CP : changed assert false in a more informative error
       *)
      user_err ~hdr:"Equality.construct_discriminator"
	(str "Cannot discriminate on inductive constructors with \
		 dependent types.") in
  let (indp,_) = dest_ind_family indf in
  let ind, _ = check_privacy env indp in
  let typ = Retyping.get_type_of env sigma default in
  let (mib,mip) = lookup_mind_specif env ind in
  let deparsign = make_arity_signature env sigma true indf in
  let p = it_mkLambda_or_LetIn typ deparsign in
  let cstrs = get_constructors env indf in
  let build_branch i =
    let endpt = if Int.equal i dirn then special else default in
    let args = List.map (fun d -> map_rel_decl EConstr.of_constr d) cstrs.(i-1).cs_args in
    it_mkLambda_or_LetIn endpt args in
  let brl =
    List.map build_branch(List.interval 1 (Array.length mip.mind_consnames)) in
  let ci = make_case_info env ind RegularStyle in
  let ans = Inductiveops.make_case_or_project env sigma indf ci p c (Array.of_list brl) in
  ans

let build_coq_False () = pf_constr_of_global (build_coq_False ())
let build_coq_True () = pf_constr_of_global (build_coq_True ())
let build_coq_I () = pf_constr_of_global (build_coq_I ())

let rec build_discriminator env sigma true_0 false_0 dirn c = function
  | [] ->
      let ind = get_type_of env sigma c in
      build_selector env sigma dirn c ind true_0 false_0
  | ((sp,cnum),argnum)::l ->
      let (cnum_nlams,cnum_env,kont) = descend_then env sigma c cnum in
      let newc = mkRel(cnum_nlams-argnum) in
      let subval = build_discriminator cnum_env sigma true_0 false_0 dirn newc l in
      kont sigma subval (false_0,mkProp)

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
  let sigma = project gl in
  let hyp_typ = pf_get_hyp_typ id gl in
  if is_empty_type sigma hyp_typ
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

let ind_scheme_of_eq lbeq =
  let (mib,mip) = Global.lookup_inductive (destIndRef lbeq.eq) in
  let kind = inductive_sort_family mip in
  (* use ind rather than case by compatibility *)
  let kind =
    if kind == InProp then Elimschemes.ind_scheme_kind_from_prop
    else Elimschemes.ind_scheme_kind_from_type in
  let c, eff = find_scheme kind (destIndRef lbeq.eq) in
    ConstRef c, eff


let discrimination_pf e (t,t1,t2) discriminator lbeq =
  build_coq_I () >>= fun i ->
  build_coq_False () >>= fun absurd_term ->
  let eq_elim, eff       = ind_scheme_of_eq lbeq in
  Proofview.tclEFFECTS eff <*>
    pf_constr_of_global eq_elim >>= fun eq_elim ->
    Proofview.tclUNIT
       (applist (eq_elim, [t;t1;mkNamedLambda e t discriminator;i;t2]), absurd_term)


let eq_baseid = Id.of_string "e"

let apply_on_clause (f,t) clause =
  let sigma =  clause.evd in
  let f_clause = mk_clenv_from_env clause.env sigma None (f,t) in
  let argmv =
    (match EConstr.kind sigma (last_arg f_clause.evd f_clause.templval.Evd.rebus) with
     | Meta mv -> mv
     | _  -> user_err  (str "Ill-formed clause applicator.")) in
  clenv_fchain ~with_univs:false argmv f_clause clause

let discr_positions env sigma (lbeq,eqn,(t,t1,t2)) eq_clause cpath dirn =
  build_coq_True () >>= fun true_0 ->
  build_coq_False () >>= fun false_0 ->
  let e = next_ident_away eq_baseid (vars_of_env env) in
  let e_env = push_named (Context.Named.Declaration.LocalAssum (e,t)) env in
  let discriminator =
    try
      Proofview.tclUNIT
        (build_discriminator e_env sigma true_0 false_0 dirn (mkVar e) cpath)
    with
      UserError _ as ex -> Proofview.tclZERO ex
  in
    discriminator >>= fun discriminator ->
    discrimination_pf e (t,t1,t2) discriminator lbeq >>= fun (pf, absurd_term) ->
    let pf_ty = mkArrow eqn absurd_term in
    let absurd_clause = apply_on_clause (pf,pf_ty) eq_clause in
    let pf = Clenvtac.clenv_value_cast_meta absurd_clause in
    tclTHENS (assert_after Anonymous absurd_term)
      [onLastHypId gen_absurdity; (Proofview.V82.tactic (Tacmach.refine pf))]

let discrEq (lbeq,_,(t,t1,t2) as u) eq_clause =
  let sigma = eq_clause.evd in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    match find_positions env sigma ~keep_proofs:false ~no_discr:false t1 t2 with
    | Inr _ ->
	tclZEROMSG (str"Not a discriminable equality.")
    | Inl (cpath, (_,dirn), _) ->
	discr_positions env sigma u eq_clause cpath dirn
  end

let onEquality with_evars tac (c,lbindc) =
  Proofview.Goal.enter begin fun gl ->
  let type_of = pf_unsafe_type_of gl in
  let reduce_to_quantified_ind = pf_apply Tacred.reduce_to_quantified_ind gl in
  let t = type_of c in
  let t' = try snd (reduce_to_quantified_ind t) with UserError _ -> t in
  let eq_clause = pf_apply make_clenv_binding gl (c,t') lbindc in
  let eq_clause' = Clenvtac.clenv_pose_dependent_evars ~with_evars eq_clause in
  let eqn = clenv_type eq_clause' in
  let (eq,u,eq_args) = find_this_eq_data_decompose gl eqn in
  tclTHEN
    (Proofview.Unsafe.tclEVARS eq_clause'.evd)
    (tac (eq,eqn,eq_args) eq_clause')
  end

let onNegatedEquality with_evars tac =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Tacmach.New.project gl in
    let ccl = Proofview.Goal.concl gl in
    let env = Proofview.Goal.env gl in
    match EConstr.kind sigma (hnf_constr env sigma ccl) with
    | Prod (_,t,u) when is_empty_type sigma u ->
        tclTHEN introf
          (onLastHypId (fun id ->
            onEquality with_evars tac (mkVar id,NoBindings)))
    | _ ->
        tclZEROMSG (str "Not a negated primitive equality.")
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

(* returns the sigma type (sigS, sigT) with the respective
    constructor depending on the sort *)
(* J.F.: correction du bug #1167 en accord avec Hugo. *)

let find_sigma_data env s = build_sigma_type ()

(* [make_tuple env sigma (rterm,rty) lind] assumes [lind] is the lesser
   index bound in [rty]

   Then we build the term

     [(existT A P (mkRel lind) rterm)] of type [(sigS A P)]

   where [A] is the type of [mkRel lind] and [P] is [\na:A.rty{1/lind}]
 *)

let make_tuple env sigma (rterm,rty) lind =
  assert (not (noccurn sigma lind rty));
  let sigdata = find_sigma_data env (get_sort_of env sigma rty) in
  let sigma, a = type_of ~refresh:true env sigma (mkRel lind) in
  let na = Context.Rel.Declaration.get_name (lookup_rel lind env) in
  (* We move [lind] to [1] and lift other rels > [lind] by 1 *)
  let rty = lift (1-lind) (liftn lind (lind+1) rty) in
  (* Now [lind] is [mkRel 1] and we abstract on (na:a) *)
  let p = mkLambda (na, a, rty) in
  let sigma, exist_term = Evd.fresh_global env sigma sigdata.intro in
  let sigma, sig_term = Evd.fresh_global env sigma sigdata.typ in
    sigma,
    (applist(exist_term,[a;p;(mkRel lind);rterm]),
     applist(sig_term,[a;p]))

(* check that the free-references of the type of [c] are contained in
   the free-references of the normal-form of that type. Strictly
   computing the exact set of free rels would require full
   normalization but this is not reasonable (e.g. in presence of
   records that contains proofs). We restrict ourself to a "simpl"
   normalization *)

let minimal_free_rels env sigma (c,cty) =
  let cty_rels = free_rels sigma cty in
  let cty' = simpl env sigma cty in
  let rels' = free_rels sigma cty' in
  if Int.Set.subset cty_rels rels' then
    (cty,cty_rels)
  else
    (cty',rels')

(* Like the above, but recurse over all the rels found until there are
   no more rels to be found *)
let minimal_free_rels_rec env sigma =
  let rec minimalrec_free_rels_rec prev_rels (c,cty) =
    let (cty,direct_rels) = minimal_free_rels env sigma (c,cty) in
    let combined_rels = Int.Set.union prev_rels direct_rels in
    let folder rels i = snd (minimalrec_free_rels_rec rels (c, unsafe_type_of env sigma (mkRel i)))
    in (cty, List.fold_left folder combined_rels (Int.Set.elements (Int.Set.diff direct_rels prev_rels)))
  in minimalrec_free_rels_rec Int.Set.empty

(* [sig_clausal_form siglen ty]

   Will explode [siglen] [sigS,sigT ]'s on [ty] (depending on the
   type of ty), and return:

   (1) a pattern, with meta-variables in it for various arguments,
       which, when the metavariables are replaced with appropriate
       terms, will have type [ty]

   (2) an integer, which is the last argument - the one which we just
       returned.

   (3) a pattern, for the type of that last meta

   (4) a typing for each patvar

   WARNING: No checking is done to make sure that the
            sigS(or sigT)'s are actually there.
          - Only homogeneous pairs are built i.e. pairs where all the
   dependencies are of the same sort

   [sig_clausal_form] proceed as follows: the default tuple is
   constructed by taking the tuple-type, exploding the first [tuplen]
   [sigS]'s, and replacing at each step the binder in the
   right-hand-type by a fresh metavariable. In addition, on the way
   back out, we will construct the pattern for the tuple which uses
   these meta-vars.

   This gives us a pattern, which we use to match against the type of
   [dflt]; if that fails, then against the S(TRONG)NF of that type.  If
   both fail, then we just cannot construct our tuple.  If one of
   those succeed, then we can construct our value easily - we just use
   the tuple-pattern.

 *)

let sig_clausal_form env sigma sort_of_ty siglen ty dflt =
  let sigdata = find_sigma_data env sort_of_ty in
  let rec sigrec_clausal_form sigma siglen p_i =
    if Int.equal siglen 0 then
      (* is the default value typable with the expected type *)
      let dflt_typ = unsafe_type_of env sigma dflt in
      try
        let sigma = Evarconv.the_conv_x_leq env dflt_typ p_i sigma in
        let sigma =
          Evarconv.solve_unif_constraints_with_heuristics env sigma in
        sigma, dflt
      with Evarconv.UnableToUnify _ ->
	user_err Pp.(str "Cannot solve a unification problem.")
    else
      let (a,p_i_minus_1) = match whd_beta_stack sigma p_i with
	| (_sigS,[a;p]) -> (a, p)
 	| _ -> anomaly ~label:"sig_clausal_form" (Pp.str "should be a sigma type.") in
      let sigma, ev = Evarutil.new_evar env sigma a in
      let rty = beta_applist sigma (p_i_minus_1,[ev]) in
      let sigma, tuple_tail = sigrec_clausal_form sigma (siglen-1) rty in
      let evopt = match EConstr.kind sigma ev with Evar _ -> None | _ -> Some ev in
      match evopt with
	| Some w ->
          let w_type = unsafe_type_of env sigma w in
          begin match Evarconv.cumul env sigma w_type a with
            | Some sigma ->
              let sigma, exist_term = Evd.fresh_global env sigma sigdata.intro in
              sigma, applist(exist_term,[a;p_i_minus_1;w;tuple_tail])
            | None ->
              user_err Pp.(str "Cannot solve a unification problem.")
          end
	| None ->
            (* This at least happens if what has been detected as a
               dependency is not one; use an evasive error message;
               even if the problem is upwards: unification should be
               tried in the first place in make_iterated_tuple instead
               of approximatively computing the free rels; then
               unsolved evars would mean not binding rel *)
	    user_err Pp.(str "Cannot solve a unification problem.")
  in
  let sigma = Evd.clear_metas sigma in
  let sigma, scf = sigrec_clausal_form sigma siglen ty in
    sigma, Evarutil.nf_evar sigma scf

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

   To do this, we find the free (relative) references of the strong NF
   of [z]'s type, gather them together in left-to-right order
   (i.e. highest-numbered is farthest-left), and construct a big
   iterated pair out of it. This only works when the references are
   all themselves to members of [Set]s, because we use [sigS] to
   construct the tuple.

   Suppose now that our constructed tuple is of length [tuplen]. We
   need also to construct a default value for the other branches of
   the destructor. As default value, we take a tuple of the form

    [existT [xn]Pn ?n (... existT [x2]P2 ?2 (existT [x1]P1 ?1 term))]

   but for this we have to solve the following unification problem:

     typ = zty[i1/?1;...;in/?n]

   This is done by [sig_clausal_form].
 *)

let make_iterated_tuple env sigma dflt (z,zty) =
  let (zty,rels) = minimal_free_rels_rec env sigma (z,zty) in
  let sort_of_zty = get_sort_of env sigma zty in
  let sorted_rels = Int.Set.elements rels in
  let sigma, (tuple,tuplety) =
    List.fold_left (fun (sigma, t) -> make_tuple env sigma t) (sigma, (z,zty)) sorted_rels
  in
  assert (closed0 sigma tuplety);
  let n = List.length sorted_rels in
  let sigma, dfltval = sig_clausal_form env sigma sort_of_zty n tuplety dflt in
    sigma, (tuple,tuplety,dfltval)

let rec build_injrec env sigma dflt c = function
  | [] -> make_iterated_tuple env sigma dflt (c,unsafe_type_of env sigma c)
  | ((sp,cnum),argnum)::l ->
    try
      let (cnum_nlams,cnum_env,kont) = descend_then env sigma c cnum in
      let newc = mkRel(cnum_nlams-argnum) in
      let sigma, (subval,tuplety,dfltval) = build_injrec cnum_env sigma dflt newc l in
      let res = kont sigma subval (dfltval,tuplety) in
      sigma, (res, tuplety,dfltval)
    with
	UserError _ -> failwith "caught"

let build_injector env sigma dflt c cpath =
  let sigma, (injcode,resty,_) = build_injrec env sigma dflt c cpath in
    sigma, (injcode,resty)

let eq_dec_scheme_kind_name = ref (fun _ -> failwith "eq_dec_scheme undefined")
let set_eq_dec_scheme_kind k = eq_dec_scheme_kind_name := (fun _ -> k)

let inject_if_homogenous_dependent_pair ty =
  Proofview.Goal.enter begin fun gl ->
  try
    let sigma = Tacmach.New.project gl in
    let eq,u,(t,t1,t2) = find_this_eq_data_decompose gl ty in
    (* fetch the informations of the  pair *)
    let sigTconstr () = (Coqlib.build_sigma_type()).Coqlib.typ in
    let existTconstr () = (Coqlib.build_sigma_type()).Coqlib.intro in
    (* check whether the equality deals with dep pairs or not *)
    let eqTypeDest = fst (decompose_app sigma t) in
    if not (Termops.is_global sigma (sigTconstr()) eqTypeDest) then raise Exit;
    let hd1,ar1 = decompose_app_vect sigma t1 and
        hd2,ar2 = decompose_app_vect sigma t2 in
    if not (Termops.is_global sigma (existTconstr()) hd1) then raise Exit;
    if not (Termops.is_global sigma (existTconstr()) hd2) then raise Exit;
    let (ind, _), _ = try pf_apply find_mrectype gl ar1.(0) with Not_found -> raise Exit in
    (* check if the user has declared the dec principle *)
    (* and compare the fst arguments of the dep pair *)
    (* Note: should work even if not an inductive type, but the table only *)
    (* knows inductive types *)
    if not (Ind_tables.check_scheme (!eq_dec_scheme_kind_name()) ind &&
      pf_apply is_conv gl ar1.(2) ar2.(2)) then raise Exit;
    Coqlib.check_required_library ["Coq";"Logic";"Eqdep_dec"];
    let new_eq_args = [|pf_unsafe_type_of gl ar1.(3);ar1.(3);ar2.(3)|] in
    let inj2 = Coqlib.coq_reference "inj_pair2_eq_dec is missing" ["Logic";"Eqdep_dec"]
                                    "inj_pair2_eq_dec" in
    let c, eff = find_scheme (!eq_dec_scheme_kind_name()) ind in
    (* cut with the good equality and prove the requested goal *)
    tclTHENLIST
      [Proofview.tclEFFECTS eff;
       intro;
       onLastHyp (fun hyp ->
        Tacticals.New.pf_constr_of_global Coqlib.glob_eq >>= fun ceq ->
        tclTHENS (cut (mkApp (ceq,new_eq_args)))
          [clear [destVar sigma hyp];
           Tacticals.New.pf_constr_of_global inj2 >>= fun inj2 ->
           Proofview.V82.tactic (Tacmach.refine
             (mkApp(inj2,[|ar1.(0);mkConst c;ar1.(1);ar1.(2);ar1.(3);ar2.(3);hyp|])))
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
    | eq, [t;c1;c2] -> applist (eq,[t;simpl env sigma c1;simpl env sigma c2])
    | eq, [t1;c1;t2;c2] -> applist (eq,[t1;simpl env sigma c1;t2;simpl env sigma c2])
    | _ -> t

let inject_at_positions env sigma l2r (eq,_,(t,t1,t2)) eq_clause posns tac =
  let e = next_ident_away eq_baseid (vars_of_env env) in
  let e_env = push_named (LocalAssum (e,t)) env in
  let evdref = ref sigma in
  let filter (cpath, t1', t2') =
    try
      (* arbitrarily take t1' as the injector default value *)
      let sigma, (injbody,resty) = build_injector e_env !evdref t1' (mkVar e) cpath in
      let injfun = mkNamedLambda e t injbody in
      let sigma,congr = Evd.fresh_global env sigma eq.congr in
      let pf = applist(congr,[t;resty;injfun;t1;t2]) in
      let sigma, pf_typ = Typing.type_of env sigma pf in
      let inj_clause = apply_on_clause (pf,pf_typ) eq_clause in
      let pf = Clenvtac.clenv_value_cast_meta inj_clause in
      let ty = simplify_args env sigma (clenv_type inj_clause) in
	evdref := sigma;
	Some (pf, ty)
    with Failure _ -> None
  in
  let injectors = List.map_filter filter posns in
  if List.is_empty injectors then
    tclZEROMSG (str "Failed to decompose the equality.")
  else
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS !evdref)
    (Tacticals.New.tclTHENFIRST
      (Proofview.tclIGNORE (Proofview.Monad.List.map
         (fun (pf,ty) -> tclTHENS (cut ty)
           [inject_if_homogenous_dependent_pair ty;
            Proofview.V82.tactic (Tacmach.refine pf)])
         (if l2r then List.rev injectors else injectors)))
      (tac (List.length injectors)))

let injEqThen keep_proofs tac l2r (eq,_,(t,t1,t2) as u) eq_clause =
  let sigma = eq_clause.evd in
  let env = eq_clause.env in
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
     tclZEROMSG (str"Nothing to inject.")
  | Inr posns ->
      inject_at_positions env sigma l2r u eq_clause posns
	(tac (clenv_value eq_clause))

let get_previous_hyp_position id gl =
  let env, sigma = Proofview.Goal.(env gl, sigma gl) in
  let rec aux dest = function
  | [] -> raise (RefinerError (env, sigma, NoSuchHyp id))
  | d :: right ->
    let hyp = Context.Named.Declaration.get_id d in
    if Id.equal hyp id then dest else aux (MoveAfter hyp) right
  in
  aux MoveLast (Proofview.Goal.hyps gl)

let injEq flags ?(old=false) with_evars clear_flag ipats =
  (* Decide which compatibility mode to use *)
  let ipats_style, l2r, dft_clear_flag, bounded_intro = match ipats with
    | None when not old && use_injection_in_context flags ->
      Some [], true, true, true
    | None -> None, false, false, false
    | _ -> let b = use_injection_pattern_l2r_order flags in ipats, b, b, b in
  (* Built the post tactic depending on compatibility mode *)
  let post_tac c n =
    match ipats_style with
    | Some ipats ->
      Proofview.Goal.enter begin fun gl ->
        let sigma = project gl in
        let destopt = match EConstr.kind sigma c with
        | Var id -> get_previous_hyp_position id gl
        | _ -> MoveLast in
        let clear_tac =
          tclTRY (apply_clear_request clear_flag dft_clear_flag c) in
        (* Try should be removal if dependency were treated *)
        let intro_tac =
          if bounded_intro
          then intro_patterns_bound_to with_evars n destopt ipats
          else intro_patterns_to with_evars destopt ipats in
        tclTHEN clear_tac intro_tac
      end
    | None -> tclIDTAC in
  injEqThen (keep_proof_equalities flags) post_tac l2r

let inj flags ipats with_evars clear_flag = onEquality with_evars (injEq flags with_evars clear_flag ipats)

let injClause flags ipats with_evars = function
  | None -> onNegatedEquality with_evars (injEq flags with_evars None ipats)
  | Some c -> onInductionArg (inj flags ipats with_evars) c

let simpleInjClause flags with_evars = function
  | None -> onNegatedEquality with_evars (injEq flags ~old:true with_evars None None)
  | Some c -> onInductionArg (fun clear_flag -> onEquality with_evars (injEq flags ~old:true with_evars clear_flag None)) c

let injConcl flags = injClause flags None false None
let injHyp flags clear_flag id = injClause flags None false (Some (clear_flag,ElimOnIdent CAst.(make id)))

let decompEqThen keep_proofs ntac (lbeq,_,(t,t1,t2) as u) clause =
  Proofview.Goal.enter begin fun gl ->
    let sigma =  clause.evd in
    let env = Proofview.Goal.env gl in
      match find_positions env sigma ~keep_proofs ~no_discr:false t1 t2 with
      | Inl (cpath, (_,dirn), _) ->
	  discr_positions env sigma u clause cpath dirn
      | Inr [] -> (* Change: do not fail, simplify clear this trivial hyp *)
        ntac (clenv_value clause) 0
    | Inr posns ->
	inject_at_positions env sigma true u clause posns
          (ntac (clenv_value clause))
  end

let dEqThen ~keep_proofs with_evars ntac = function
  | None -> onNegatedEquality with_evars (decompEqThen (use_keep_proofs keep_proofs) (ntac None))
  | Some c -> onInductionArg (fun clear_flag -> onEquality with_evars (decompEqThen (use_keep_proofs keep_proofs) (ntac clear_flag))) c

let dEq ~keep_proofs with_evars =
  dEqThen ~keep_proofs with_evars (fun clear_flag c x ->
    (apply_clear_request clear_flag (use_clear_hyp_by_default ()) c))

let intro_decomp_eq tac data (c, t) =
  Proofview.Goal.enter begin fun gl ->
    let cl = pf_apply make_clenv_binding gl (c, t) NoBindings in
    decompEqThen !keep_proof_equalities_for_injection (fun _ -> tac) data cl
  end

let _ = declare_intro_decomp_eq intro_decomp_eq

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

let decomp_tuple_term env sigma c t =
  let rec decomprec inner_code ex exty =
    let iterated_decomp =
    try
      let ({proj1=p1; proj2=p2}),(i,a,p,car,cdr) = find_sigma_data_decompose env sigma ex in
      let car_code = applist (mkConstU (destConstRef p1,i),[a;p;inner_code])
      and cdr_code = applist (mkConstU (destConstRef p2,i),[a;p;inner_code]) in
      let cdrtyp = beta_applist sigma (p,[car]) in
      List.map (fun l -> ((car,a),car_code)::l) (decomprec cdr_code cdr cdrtyp)
    with Constr_matching.PatternMatchingFailure ->
      []
    in [((ex,exty),inner_code)]::iterated_decomp
  in decomprec (mkRel 1) c t

let subst_tuple_term env sigma dep_pair1 dep_pair2 b =
  let typ = get_type_of env sigma dep_pair1 in
  (* We find all possible decompositions *)
  let decomps1 = decomp_tuple_term env sigma dep_pair1 typ in
  let decomps2 = decomp_tuple_term env sigma dep_pair2 typ in
  (* We adjust to the shortest decomposition *)
  let n = min (List.length decomps1) (List.length decomps2) in
  let decomp1 = List.nth decomps1 (n-1) in
  let decomp2 = List.nth decomps2 (n-1) in
  (* We rewrite dep_pair1 ... *)
  let e1_list,proj_list = List.split decomp1 in
  (* ... and use dep_pair2 to compute the expected goal *)
  let e2_list,_ = List.split decomp2 in
  (* We build the expected goal *)
  let abst_B =
    List.fold_right
      (fun (e,t) body -> lambda_create env sigma (t,subst_term sigma e body)) e1_list b in
  let pred_body = beta_applist sigma (abst_B,proj_list) in
  let body = mkApp (lambda_create env sigma (typ,pred_body),[|dep_pair1|]) in
  let expected_goal = beta_applist sigma (abst_B,List.map fst e2_list) in
  (* Simulate now the normalisation treatment made by Logic.mk_refgoals *)
  let expected_goal = nf_betaiota env sigma expected_goal in
  (* Retype to get universes right *)
  let sigma, expected_goal_ty = Typing.type_of env sigma expected_goal in
  let sigma, _ = Typing.type_of env sigma body in
  (sigma, (body, expected_goal))

(* Like "replace" but decompose dependent equalities                      *)
(* i.e. if equality is "exists t v = exists u w", and goal is "phi(t,u)", *)
(* then it uses the predicate "\x.phi(proj1_sig x,proj2_sig x)", and so   *)
(* on for further iterated sigma-tuples                                   *)

let cutSubstInConcl l2r eqn =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let (lbeq,u,(t,e1,e2)) = find_eq_data_decompose gl eqn in
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
  let (lbeq,u,(t,e1,e2)) = find_eq_data_decompose gl eqn in
  let typ = pf_get_hyp_typ id gl in
  let (e1,e2) = if l2r then (e1,e2) else (e2,e1) in
  let (sigma, (typ, expected)) = subst_tuple_term env sigma e1 e2 typ in
  tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (tclTHENFIRST
    (tclTHENLIST [
       (change_in_hyp None (make_change_arg typ) (id,InHypTypeOnly));
       (replace_core (onHyp id) l2r eqn)
    ])
    (change_in_hyp None (make_change_arg expected) (id,InHypTypeOnly)))
  end

let try_rewrite tac =
  Proofview.tclORELSE tac begin function (e, info) -> match e with
    | Constr_matching.PatternMatchingFailure ->
	tclZEROMSG (str "Not a primitive equality here.")
    | e when catchable_exception e ->
	tclZEROMSG
          (strbrk "Cannot find a well-typed generalization of the goal that makes the proof progress.")
    | e -> Proofview.tclZERO ~info e
  end

let cutSubstClause l2r eqn cls =
  match cls with
    | None ->    cutSubstInConcl l2r eqn
    | Some id -> cutSubstInHyp l2r eqn id

let cutRewriteClause l2r eqn cls = try_rewrite (cutSubstClause l2r eqn cls)
let cutRewriteInHyp l2r eqn id = cutRewriteClause l2r eqn (Some id)
let cutRewriteInConcl l2r eqn = cutRewriteClause l2r eqn None

let substClause l2r c cls =
  Proofview.Goal.enter begin fun gl ->
  let eq = pf_apply get_type_of gl c in
  tclTHENS (cutSubstClause l2r eq cls)
    [Proofview.tclUNIT (); exact_no_check c]
  end

let rewriteClause l2r c cls = try_rewrite (substClause l2r c cls)
let rewriteInHyp l2r c id = rewriteClause l2r c (Some id)
let rewriteInConcl l2r c = rewriteClause l2r c None

(* Naming scheme for rewrite and cutrewrite tactics

      give equality        give proof of equality

    / cutSubstClause       substClause
raw | cutSubstInHyp        substInHyp
    \ cutSubstInConcl      substInConcl

    / cutRewriteClause     rewriteClause
user| cutRewriteInHyp      rewriteInHyp
    \ cutRewriteInConcl    rewriteInConcl

raw = raise typing error or PatternMatchingFailure
user = raise user error specific to rewrite
*)

(**********************************************************************)
(* Substitutions tactics (JCF) *)

let regular_subst_tactic = ref true

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "more regular behavior of tactic subst";
      optkey   = ["Regular";"Subst";"Tactic"];
      optread  = (fun () -> !regular_subst_tactic);
      optwrite = (:=) regular_subst_tactic }

let restrict_to_eq_and_identity eq = (* compatibility *)
  if not (is_global glob_eq eq) &&
    not (is_global glob_identity eq) 
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
    let (_,lhs,rhs) = pi3 (find_eq_data_decompose gl c) in
    if (is_var x lhs) && not (local_occur_var (project gl) x rhs) then raise (FoundHyp (id,rhs,true));
    if (is_var x rhs) && not (local_occur_var (project gl) x lhs) then raise (FoundHyp (id,lhs,false))
  with Constr_matching.PatternMatchingFailure ->
    ()

(* Rewrite "hyp:x=rhs" or "hyp:rhs=x" (if dir=false) everywhere and
   erase hyp and x; proceed by generalizing all dep hyps *)

let subst_one dep_proof_ok x (hyp,rhs,dir) =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.New.project gl in
  let hyps = Proofview.Goal.hyps gl in
  let concl = Proofview.Goal.concl gl in
  (* The set of hypotheses using x *)
  let dephyps =
    List.rev (pi3 (List.fold_right (fun dcl (dest,deps,allhyps) ->
      let id = NamedDecl.get_id dcl in
      if not (Id.equal id hyp)
         && List.exists (fun y -> occur_var_in_decl env sigma y dcl) deps
      then
        let id_dest = if !regular_subst_tactic then dest else MoveLast in
        (dest,id::deps,(id_dest,id)::allhyps)
      else
        (MoveBefore id,deps,allhyps))
      hyps
      (MoveBefore x,[x],[]))) in (* In practice, no dep hyps before x, so MoveBefore x is good enough *)
  (* Decides if x appears in conclusion *)
  let depconcl = occur_var env sigma x concl in
  let need_rewrite = not (List.is_empty dephyps) || depconcl in
  tclTHENLIST
    ((if need_rewrite then
      [revert (List.map snd dephyps);
       general_rewrite dir AllOccurrences true dep_proof_ok (mkVar hyp);
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
          (** [is_eq_x] ensures nf_evar on its side *)
          let hyps = Proofview.Goal.hyps gl in
          let test hyp _ = is_eq_x gl x hyp in
          Context.Named.fold_outside test ~init:() hyps;
          user_err ~hdr:"Subst"
            (str "Cannot find any non-recursive equality over " ++ Id.print x ++
	       str".")
        with FoundHyp res -> res in
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
  CWarnings.create ~name:"deprecated-simple-subst" ~category:"deprecated"
    (fun () -> strbrk"\"simple subst\" is deprecated")

let subst_all ?(flags=default_subst_tactic_flags) () =

  let () =
    if flags.only_leibniz || not flags.rewrite_dependent_proof then
      warn_deprecated_simple_subst ()
  in

  if !regular_subst_tactic then

  (* First step: find hypotheses to treat in linear time *)
  let find_equations gl =
    let env = Proofview.Goal.env gl in
    let sigma = project gl in
    let find_eq_data_decompose = find_eq_data_decompose gl in
    let select_equation_name decl =
      try
        let lbeq,u,(_,x,y) = find_eq_data_decompose (NamedDecl.get_type decl) in
        let u = EInstance.kind sigma u in
        let eq = UnivGen.constr_of_global_univ (lbeq.eq,u) in
        if flags.only_leibniz then restrict_to_eq_and_identity eq;
        match EConstr.kind sigma x, EConstr.kind sigma y with
        | Var z, _  when not (is_evaluable env (EvalVarRef z)) ->
            Some (NamedDecl.get_id decl)
        | _, Var z when not (is_evaluable env (EvalVarRef z)) ->
            Some (NamedDecl.get_id decl)
        | _ ->
            None
      with Constr_matching.PatternMatchingFailure -> None
    in
    let hyps = Proofview.Goal.hyps gl in
    List.rev (List.map_filter select_equation_name hyps)
  in

  (* Second step: treat equations *)
  let process hyp =
    Proofview.Goal.enter begin fun gl ->
    let sigma = project gl in
    let env = Proofview.Goal.env gl in
    let find_eq_data_decompose = find_eq_data_decompose gl in
    let c = pf_get_hyp hyp gl |> NamedDecl.get_type in
    let _,_,(_,x,y) = find_eq_data_decompose c in
    (* J.F.: added to prevent failure on goal containing x=x as an hyp *)
    if EConstr.eq_constr sigma x y then Proofview.tclUNIT () else
      match EConstr.kind sigma x, EConstr.kind sigma y with
      | Var x', _ when not (Termops.local_occur_var sigma x' y) && not (is_evaluable env (EvalVarRef x')) ->
          subst_one flags.rewrite_dependent_proof x' (hyp,y,true)
      | _, Var y' when not (Termops.local_occur_var sigma y' x) && not (is_evaluable env (EvalVarRef y')) ->
          subst_one flags.rewrite_dependent_proof y' (hyp,x,false)
      | _ ->
          Proofview.tclUNIT ()
    end
  in
  Proofview.Goal.enter begin fun gl ->
    let ids = find_equations gl in
    tclMAP process ids
  end

  else

(* Old implementation, not able to manage configurations like a=b, a=t,
   or situations like "a = S b, b = S a", or also accidentally unfolding
   let-ins *)
  Proofview.Goal.enter begin fun gl ->
  let sigma = project gl in
  let find_eq_data_decompose = find_eq_data_decompose gl in
  let test (_,c) =
    try
      let lbeq,u,(_,x,y) = find_eq_data_decompose c in
      let u = EInstance.kind sigma u in
      let eq = UnivGen.constr_of_global_univ (lbeq.eq,u) in
      if flags.only_leibniz then restrict_to_eq_and_identity eq;
      (* J.F.: added to prevent failure on goal containing x=x as an hyp *)
      if EConstr.eq_constr sigma x y then failwith "caught";
      match EConstr.kind sigma x with Var x -> x | _ ->
      match EConstr.kind sigma y with Var y -> y | _ -> failwith "caught"
    with Constr_matching.PatternMatchingFailure -> failwith "caught" in
  let test p = try Some (test p) with Failure _ -> None in
  let hyps = pf_hyps_types gl in
  let ids = List.map_filter test hyps in
  let ids = List.uniquize ids in
  subst_gen flags.rewrite_dependent_proof ids
  end

(* Rewrite the first assumption for which a condition holds
   and gives the direction of the rewrite *)

let cond_eq_term_left c t gl =
  try
    let (_,x,_) = pi3 (find_eq_data_decompose gl t) in
    if pf_conv_x gl c x then true else failwith "not convertible"
  with Constr_matching.PatternMatchingFailure -> failwith "not an equality"

let cond_eq_term_right c t gl =
  try
    let (_,_,x) = pi3 (find_eq_data_decompose gl t) in
    if pf_conv_x gl c x then false else failwith "not convertible"
  with Constr_matching.PatternMatchingFailure -> failwith "not an equality"

let cond_eq_term c t gl =
  try
    let (_,x,y) = pi3 (find_eq_data_decompose gl t) in
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

let _ =
  let gmr l2r with_evars tac c = general_rewrite_clause l2r with_evars tac c in
  Hook.set Tactics.general_rewrite_clause gmr

let _ = Hook.set Tactics.subst_one subst_one
