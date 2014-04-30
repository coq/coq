(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
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
open Termops
open Namegen
open Inductive
open Inductiveops
open Environ
open Libnames
open Globnames
open Reductionops
open Typing
open Retyping
open Tacmach.New
open Logic
open Hipattern
open Tacexpr
open Tacticals.New
open Tactics
open Tacred
open Coqlib
open Declarations
open Indrec
open Clenv
open Clenvtac
open Evd
open Ind_tables
open Eqschemes
open Locus
open Locusops
open Misctypes
open Proofview.Notations

(* Options *)

let discriminate_introduction = ref true

let discr_do_intro () =
  !discriminate_introduction && Flags.version_strictly_greater Flags.V8_2

open Goptions
let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "automatic introduction of hypotheses by discriminate";
      optkey   = ["Discriminate";"Introduction"];
      optread  = (fun () -> !discriminate_introduction);
      optwrite = (:=) discriminate_introduction }

let injection_pattern_l2r_order = ref true

let use_injection_pattern_l2r_order () =
  !injection_pattern_l2r_order
  && Flags.version_strictly_greater Flags.V8_4

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "injection left-to-right pattern order";
      optkey   = ["Injection";"L2R";"Pattern";"Order"];
      optread  = (fun () -> !injection_pattern_l2r_order) ;
      optwrite = (fun b -> injection_pattern_l2r_order := b) }

(* Rewriting tactics *)

let clear ids = Proofview.V82.tactic (clear ids)

let tclNOTSAMEGOAL tac =
  Proofview.V82.tactic (Tacticals.tclNOTSAMEGOAL (Proofview.V82.of_tactic tac))

type dep_proof_flag = bool (* true = support rewriting dependent proofs *)
type freeze_evars_flag = bool (* true = don't instantiate existing evars *)

type orientation = bool

type conditions =
  | Naive (* Only try the first occurence of the lemma (default) *)
  | FirstSolved (* Use the first match whose side-conditions are solved *)
  | AllMatches (* Rewrite all matches whose side-conditions are solved *)

(* Warning : rewriting from left to right only works
   if there exists in the context a theorem named <eqname>_<suffsort>_r
   with type (A:<sort>)(x:A)(P:A->Prop)(P x)->(y:A)(eqname A y x)->(P y).
   If another equality myeq is introduced, then corresponding theorems
   myeq_ind_r, myeq_rec_r and myeq_rect_r have to be proven. See below.
   -- Eduardo (19/8/97)
*)

let rewrite_unif_flags = {
  Unification.modulo_conv_on_closed_terms = None;
  Unification.use_metas_eagerly_in_conv_on_closed_terms = true;
  Unification.modulo_delta = empty_transparent_state;
  Unification.modulo_delta_types = empty_transparent_state;
  Unification.modulo_delta_in_merge = None;
  Unification.check_applied_meta_types = true;
  Unification.resolve_evars = true;
  Unification.use_pattern_unification = true;
  Unification.use_meta_bound_pattern_unification = true;
  Unification.frozen_evars = Evar.Set.empty;
  Unification.restrict_conv_on_strict_subterms = false;
  Unification.modulo_betaiota = false;
  Unification.modulo_eta = true;
  Unification.allow_K_in_toplevel_higher_order_unification = false
    (* allow_K does not matter in practice because calls w_typed_unify *)
}

let freeze_initial_evars sigma flags clause =
  (* We take evars of the type: this may include old evars! For excluding *)
  (* all old evars, including the ones occurring in the rewriting lemma, *)
  (* we would have to take the clenv_value *)
  let newevars = Evd.collect_evars (clenv_type clause) in
  let evars =
    fold_undefined (fun evk _ evars ->
      if Evar.Set.mem evk newevars then evars
      else Evar.Set.add evk evars)
      sigma Evar.Set.empty in
  { flags with Unification.frozen_evars = evars }

let make_flags frzevars sigma flags clause =
  if frzevars then freeze_initial_evars sigma flags clause else flags

let side_tac tac sidetac =
  match sidetac with
  | None -> tac
  | Some sidetac -> tclTHENSFIRSTn tac [|Proofview.tclUNIT ()|] sidetac

let instantiate_lemma_all frzevars env gl c ty l l2r concl =
  let eqclause = pf_apply Clenv.make_clenv_binding gl (c,ty) l in
  let (equiv, args) = decompose_app (Clenv.clenv_type eqclause) in
  let rec split_last_two = function
      | [c1;c2] -> [],(c1, c2)
      | x::y::z ->
	  let l,res = split_last_two (y::z) in x::l, res
      | _ -> error "The term provided is not an applied relation." in
  let others,(c1,c2) = split_last_two args in
  let try_occ (evd', c') =
    clenv_pose_dependent_evars true {eqclause with evd = evd'}
  in
  let flags = make_flags frzevars (Proofview.Goal.sigma gl) rewrite_unif_flags eqclause in
  let occs =
    Unification.w_unify_to_subterm_all ~flags env eqclause.evd
      ((if l2r then c1 else c2),concl)
  in List.map try_occ occs

let instantiate_lemma env gl c ty l l2r concl =
  let ct = pf_type_of gl c in
  let t = try snd (pf_reduce_to_quantified_ind gl ct) with UserError _ -> ct in
  let eqclause = pf_apply Clenv.make_clenv_binding gl (c,t) l in
   [eqclause]

let rewrite_conv_closed_unif_flags = {
  Unification.modulo_conv_on_closed_terms = Some full_transparent_state;
    (* We have this flag for historical reasons, it has e.g. the consequence *)
    (* to rewrite "?x+2" in "y+(1+1)=0" or to rewrite "?x+?x" in "2+(1+1)=0" *)

  Unification.use_metas_eagerly_in_conv_on_closed_terms = true;
    (* Combined with modulo_conv_on_closed_terms, this flag allows since 8.2 *)
    (* to rewrite e.g. "?x+(2+?x)" in "1+(1+2)=0" *)

  Unification.modulo_delta = empty_transparent_state;
  Unification.modulo_delta_types = full_transparent_state;
  Unification.modulo_delta_in_merge = None;
  Unification.check_applied_meta_types = true;
  Unification.resolve_evars = false;
  Unification.use_pattern_unification = true;
    (* To rewrite "?n x y" in "y+x=0" when ?n is *)
    (* a preexisting evar of the goal*)

  Unification.use_meta_bound_pattern_unification = true;

  Unification.frozen_evars = Evar.Set.empty;
    (* This is set dynamically *)

  Unification.restrict_conv_on_strict_subterms = false;
  Unification.modulo_betaiota = false;
  Unification.modulo_eta = true;
  Unification.allow_K_in_toplevel_higher_order_unification = false
}

let rewrite_elim with_evars frzevars c e =
  Proofview.Goal.raw_enter begin fun gl ->
  let flags = make_flags frzevars (Proofview.Goal.sigma gl) rewrite_conv_closed_unif_flags c in
  let elim gl = elimination_clause_scheme with_evars ~flags gl in
  let tac gl = general_elim_clause_gen elim c e gl in
  Proofview.V82.tactic tac
  end

let rewrite_elim_in with_evars frzevars id c e =
  Proofview.Goal.raw_enter begin fun gl ->
  let flags = make_flags frzevars (Proofview.Goal.sigma gl) rewrite_conv_closed_unif_flags c in
  let elim gl = elimination_in_clause_scheme with_evars ~flags id gl in
  let tac gl = general_elim_clause_gen elim c e gl in
  Proofview.V82.tactic tac
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
      tclNOTSAMEGOAL (rewrite_elim with_evars frzevars rew elim)
    | Some id -> rewrite_elim_in with_evars frzevars id rew elim
    end
    begin function
    | PretypeError (env, evd, NoOccurrenceFound (c', _)) ->
      Proofview.tclZERO (PretypeError (env, evd, NoOccurrenceFound (c', cls)))
    | e -> Proofview.tclZERO e
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
         (Proofview.V82.tclEVARS c.evd)
         (general_elim_clause with_evars frzevars cls c elim))
      tac
  in
  Proofview.Goal.raw_enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let instantiate_lemma concl =
      if not all then instantiate_lemma env gl c t l l2r concl
      else instantiate_lemma_all frzevars env gl c t l l2r concl
    in
    let typ = match cls with
    | None -> pf_nf_concl gl
    | Some id -> pf_get_hyp_typ id (Proofview.Goal.assume gl)
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

let (forward_general_rewrite_clause, general_rewrite_clause) = Hook.make ()

(* Do we have a JMeq instance on twice the same domains ? *)

let jmeq_same_dom gl = function
  | None -> true (* already checked in Hipattern.find_eq_data_decompose *)
  | Some t ->
    let rels, t = decompose_prod_assum t in
    let env = Environ.push_rel_context rels (Proofview.Goal.env gl) in
    match decompose_app t with
      | _, [dom1; _; dom2;_] -> is_conv env (Proofview.Goal.sigma gl) dom1 dom2
      | _ -> false

(* find_elim determines which elimination principle is necessary to
   eliminate lbeq on sort_of_gl. *)

let find_elim hdcncl lft2rgt dep cls ot gl =
  let inccl = Option.is_empty cls in
  let hdcncl_is u = eq_constr hdcncl (constr_of_reference u) in
  if (hdcncl_is (Coqlib.glob_eq) ||
      hdcncl_is (Coqlib.glob_jmeq) && jmeq_same_dom gl ot)
     && not dep
     || Flags.version_less_or_equal Flags.V8_2
  then
    match kind_of_term hdcncl with 
      | Ind ind_sp -> 
	let pr1 = 
	  lookup_eliminator ind_sp (elimination_sort_of_clause cls gl) 
	in
        begin match lft2rgt, cls with
        | Some true, None
        | Some false, Some _ ->
	  let c1 = destConst pr1 in 
	  let mp,dp,l = repr_con (constant_of_kn (canonical_con c1)) in 
	  let l' = Label.of_id (add_suffix (Label.to_id l) "_r")  in 
	  let c1' = Global.constant_of_delta_kn (make_kn mp dp l') in
	  begin 
	    try 
	      let _ = Global.lookup_constant c1' in
              mkConst c1', Declareops.no_seff
	    with Not_found -> 
	      let rwr_thm = Label.to_string l' in 
	      error ("Cannot find rewrite principle "^rwr_thm^".")
	  end
	| _ -> pr1, Declareops.no_seff
        end
      | _ -> 
	  (* cannot occur since we checked that we are in presence of 
	     Logic.eq or Jmeq just before *)
	assert false
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
  match kind_of_term hdcncl with
  | Ind ind -> 
      let c, eff = find_scheme scheme_name ind in 
      mkConst c , eff
  | _ -> assert false

let type_of_clause cls gl = match cls with
  | None -> Proofview.Goal.concl gl
  | Some id -> pf_get_hyp_typ id gl

let leibniz_rewrite_ebindings_clause cls lft2rgt tac c t l with_evars frzevars dep_proof_ok hdcncl =
  Proofview.Goal.enter begin fun gl ->
  let isatomic = isProd (whd_zeta hdcncl) in
  let dep_fun = if isatomic then dependent else dependent_no_evar in
  let type_of_cls = type_of_clause cls gl in
  let dep = dep_proof_ok && dep_fun c type_of_cls in
  let (elim,effs) = find_elim hdcncl lft2rgt dep cls (Some t) gl in
  Proofview.tclEFFECTS effs <*>
  general_elim_clause with_evars frzevars tac cls c t l
    (match lft2rgt with None -> false | Some b -> b)
    {elimindex = None; elimbody = (elim,NoBindings)}
  end

let adjust_rewriting_direction args lft2rgt =
  match args with
  | [_] ->
    (* equality to a constant, like in eq_true *)
    (* more natural to see -> as the rewriting to the constant *)
    if not lft2rgt then
      error "Rewriting non-symmetric equality not allowed from right-to-left.";
    None
  | _ ->
    (* other equality *)
    Some lft2rgt

let rewrite_side_tac tac sidetac = side_tac tac (Option.map fst sidetac)

(* Main function for dispatching which kind of rewriting it is about *)

let general_rewrite_ebindings_clause cls lft2rgt occs frzevars dep_proof_ok ?tac
    ((c,l) : constr with_bindings) with_evars =
  if occs != AllOccurrences then (
    rewrite_side_tac (Hook.get forward_general_rewrite_clause cls lft2rgt occs (c,l) ~new_goals:[]) tac)
  else
    Proofview.Goal.raw_enter begin fun gl ->
      let sigma = Proofview.Goal.sigma gl in
      let env = Proofview.Goal.env gl in
    let ctype = get_type_of env sigma c in
    let rels, t = decompose_prod_assum (whd_betaiotazeta sigma ctype) in
      match match_with_equality_type t with
      | Some (hdcncl,args) -> (* Fast path: direct leibniz-like rewrite *)
	  let lft2rgt = adjust_rewriting_direction args lft2rgt in
          leibniz_rewrite_ebindings_clause cls lft2rgt tac c (it_mkProd_or_LetIn t rels)
	    l with_evars frzevars dep_proof_ok hdcncl
      | None ->
	  Proofview.tclORELSE
            begin
	      rewrite_side_tac (Hook.get forward_general_rewrite_clause cls
				   lft2rgt occs (c,l) ~new_goals:[]) tac
            end
            begin function
              | e ->
	          let env' = push_rel_context rels env in
	          let rels',t' = splay_prod_assum env' sigma t in (* Search for underlying eq *)
	          match match_with_equality_type t' with
	            | Some (hdcncl,args) ->
		  let lft2rgt = adjust_rewriting_direction args lft2rgt in
		  leibniz_rewrite_ebindings_clause cls lft2rgt tac c
		    (it_mkProd_or_LetIn t' (rels' @ rels)) l with_evars frzevars dep_proof_ok hdcncl
	            | None -> Proofview.tclZERO e
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

let general_multi_rewrite l2r with_evars ?tac c cl =
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
	  | [] -> Proofview.tclZERO (Errors.UserError ("",Pp.str"Nothing to rewrite."))
	  | id :: l ->
	    tclIFTHENTRYELSEMUST
	     (general_rewrite_ebindings_in l2r AllOccurrences false true ?tac id c with_evars)
	     (do_hyps_atleastonce l)
	in
	let do_hyps =
	  (* If the term to rewrite uses an hypothesis H, don't rewrite in H *)
	  let ids gl =
	    let ids_in_c = Environ.global_vars_set (Global.env()) (fst c) in
            let ids_of_hyps = pf_ids_of_hyps gl in
	    Id.Set.fold (fun id l -> List.remove Id.equal id l) ids_in_c ids_of_hyps
	  in
          Proofview.Goal.raw_enter begin fun gl ->
            do_hyps_atleastonce (ids gl)
          end
	in
	if cl.concl_occs == NoOccurrences then do_hyps else
	  tclIFTHENTRYELSEMUST
	   (general_rewrite_ebindings l2r (occs_of cl.concl_occs) false true ?tac c with_evars)
	   do_hyps

type delayed_open_constr_with_bindings =
    env -> evar_map -> evar_map * constr with_bindings

let general_multi_multi_rewrite with_evars l cl tac =
  let do1 l2r f =
    Proofview.Goal.raw_enter begin fun gl ->
      let sigma = Proofview.Goal.sigma gl in
      let env = Proofview.Goal.env gl in
      let sigma,c = f env sigma in
      tclWITHHOLES with_evars
        (general_multi_rewrite l2r with_evars ?tac c) sigma cl
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
    | (l2r,m,c)::l -> tclTHENFIRST (doN l2r c m) (loop l)
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
    
(* eq,sym_eq : equality on Type and its symmetry theorem
   c2 c1 : c1 is to be replaced by c2
   unsafe : If true, do not check that c1 and c2 are convertible
   tac : Used to prove the equality c1 = c2
   gl : goal *)

let multi_replace clause c2 c1 unsafe try_prove_eq_opt =
  let try_prove_eq =
    match try_prove_eq_opt with
      | None -> Proofview.tclUNIT ()
      | Some tac ->  tclCOMPLETE tac
  in
  Proofview.Goal.raw_enter begin fun gl ->
  let get_type_of = pf_apply get_type_of gl in
  let t1 = get_type_of c1
  and t2 = get_type_of c2 in
  let is_conv = pf_apply is_conv gl in
  if unsafe || (is_conv t1 t2) then
    let e = build_coq_eq () in
    let sym = build_coq_eq_sym () in
    let eq = applist (e, [t1;c1;c2]) in
    if check_setoid clause
    then init_setoid ();
    tclTHENS (assert_as false None eq)
      [onLastHypId (fun id ->
	tclTHEN
	  (tclTRY (general_multi_rewrite false false (mkVar id,NoBindings) clause))
	  (clear [id]));
       tclFIRST
	 [assumption;
	  tclTHEN (Proofview.V82.tactic (apply sym)) assumption;
	  try_prove_eq
	 ]
      ]
  else
    tclFAIL 0 (str"Terms do not have convertible types.")
  end

let replace c2 c1 = multi_replace onConcl c2 c1 false None

let replace_by c2 c1 tac = multi_replace onConcl c2 c1 false (Some tac)

let replace_in_clause_maybe_by c2 c1 cl tac_opt =
  multi_replace cl c2 c1 false tac_opt

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

let injection_on_proofs = ref true

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "injection on prop arguments";
      optkey   = ["Injection";"On";"Proofs"];
      optread  = (fun () -> !injection_on_proofs) ;
      optwrite = (fun b -> injection_on_proofs := b) }


let find_positions env sigma t1 t2 =
  let rec findrec sorts posn t1 t2 =
    let hd1,args1 = whd_betadeltaiota_stack env sigma t1 in
    let hd2,args2 = whd_betadeltaiota_stack env sigma t2 in
    match (kind_of_term hd1, kind_of_term hd2) with

      | Construct sp1, Construct sp2
          when Int.equal (List.length args1) (mis_constructor_nargs_env env sp1)
            ->
	  let sorts =
            Sorts.List.intersect sorts (allowed_sorts env (fst sp1))
          in
          (* both sides are fully applied constructors, so either we descend,
             or we can discriminate here. *)
	  if is_conv env sigma hd1 hd2 then
	    let nrealargs = constructor_nrealargs env sp1 in
	    let rargs1 = List.lastn nrealargs args1 in
	    let rargs2 = List.lastn nrealargs args2 in
            List.flatten
	      (List.map2_i (fun i -> findrec sorts ((sp1,i)::posn))
		0 rargs1 rargs2)
	  else if Sorts.List.mem InType sorts
          then (* see build_discriminator *)
	    raise (DiscrFound (List.rev posn,sp1,sp2))
	  else []

      | _ ->
	  let t1_0 = applist (hd1,args1)
          and t2_0 = applist (hd2,args2) in
          if is_conv env sigma t1_0 t2_0 then
	    []
          else
	    let ty1_0 = get_type_of env sigma t1_0 in
	    let s = get_sort_family_of env sigma ty1_0 in
	    if Sorts.List.mem s sorts
            then [(List.rev posn,t1_0,t2_0)] else []
  in
  try
    let sorts = if !injection_on_proofs then [InSet;InType;InProp]
		else [InSet;InType]
    in
    Inr (findrec sorts [] t1 t2)
  with DiscrFound (path,c1,c2) ->
    Inl (path,c1,c2)

let discriminable env sigma t1 t2 =
  match find_positions env sigma t1 t2 with
    | Inl _ -> true
    | _ -> false

let injectable env sigma t1 t2 =
    match find_positions env sigma t1 t2 with
    | Inl _ | Inr [] | Inr [([],_,_)] -> false
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

(* [descend_then sigma env head dirn]

   returns the number of products introduced, and the environment
   which is active, in the body of the case-branch given by [dirn],
   along with a continuation, which expects to be fed:

    (1) the value of the body of the branch given by [dirn]
    (2) the default-value

    (3) the type of the default-value, which must also be the type of
        the body of the [dirn] branch

   the continuation then constructs the case-split.
 *)

let descend_then sigma env head dirn =
  let IndType (indf,_) =
    try find_rectype env sigma (get_type_of env sigma head)
    with Not_found ->
      error "Cannot project on an inductive type derived from a dependency." in
   let ind,_ = dest_ind_family indf in
  let (mib,mip) = lookup_mind_specif env ind in
  let cstr = get_constructors env indf in
  let dirn_nlams = cstr.(dirn-1).cs_nargs in
  let dirn_env = push_rel_context cstr.(dirn-1).cs_args env in
  (dirn_nlams,
   dirn_env,
   (fun dirnval (dfltval,resty) ->
      let deparsign = make_arity_signature env true indf in
      let p =
	it_mkLambda_or_LetIn (lift (mip.mind_nrealargs+1) resty) deparsign in
      let build_branch i =
	let result = if Int.equal i dirn then dirnval else dfltval in
	it_mkLambda_or_LetIn_name env result cstr.(i-1).cs_args in
      let brl =
        List.map build_branch
          (List.interval 1 (Array.length mip.mind_consnames)) in
      let ci = make_case_info env ind RegularStyle in
      mkCase (ci, p, head, Array.of_list brl)))

(* Now we need to construct the discriminator, given a discriminable
   position.  This boils down to:

   (1) If the position is directly beneath us, then we need to do a
   case-split, with result-type Prop, and stick True and False into
   the branches, as is convenient.

   (2) If the position is not directly beneath us, then we need to
   call descend_then, to descend one step, and then recursively
   construct the discriminator.

 *)

(* [construct_discriminator env dirn headval]
   constructs a case-split on [headval], with the [dirn]-th branch
   giving [True], and all the rest giving False. *)

let construct_discriminator sigma env dirn c sort =
  let IndType(indf,_) =
    try find_rectype env sigma (get_type_of env sigma c)
    with Not_found ->
       (* one can find Rel(k) in case of dependent constructors
          like T := c : (A:Set)A->T and a discrimination
          on (c bool true) = (c bool false)
          CP : changed assert false in a more informative error
       *)
      errorlabstrm "Equality.construct_discriminator"
	(str "Cannot discriminate on inductive constructors with \
		 dependent types.") in
  let (ind,_) = dest_ind_family indf in
  let (mib,mip) = lookup_mind_specif env ind in
  let (true_0,false_0,sort_0) = build_coq_True(),build_coq_False(),Prop Null in
  let deparsign = make_arity_signature env true indf in
  let p = it_mkLambda_or_LetIn (mkSort sort_0) deparsign in
  let cstrs = get_constructors env indf in
  let build_branch i =
    let endpt = if Int.equal i dirn then true_0 else false_0 in
    it_mkLambda_or_LetIn endpt cstrs.(i-1).cs_args in
  let brl =
    List.map build_branch(List.interval 1 (Array.length mip.mind_consnames)) in
  let ci = make_case_info env ind RegularStyle in
  mkCase (ci, p, c, Array.of_list brl)

let rec build_discriminator sigma env dirn c sort = function
  | [] -> construct_discriminator sigma env dirn c sort
  | ((sp,cnum),argnum)::l ->
      let (cnum_nlams,cnum_env,kont) = descend_then sigma env c cnum in
      let newc = mkRel(cnum_nlams-argnum) in
      let subval = build_discriminator sigma cnum_env dirn newc sort l  in
      kont subval (build_coq_False (),mkSort (Prop Null))

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
  Proofview.Goal.raw_enter begin fun gl ->
  let hyp_typ = pf_get_hyp_typ id (Proofview.Goal.assume gl) in
  let hyp_typ = pf_nf_evar gl hyp_typ in
  if is_empty_type hyp_typ
  then
    simplest_elim (mkVar id)
  else
    Proofview.tclZERO (Errors.UserError ("Equality.gen_absurdity" , str "Not the negation of an equality."))
  end

(* Precondition: eq is leibniz equality

   returns ((eq_elim t t1 P i t2), absurd_term)
   where  P=[e:t]discriminator
          absurd_term=False
*)

let ind_scheme_of_eq lbeq =
  let (mib,mip) = Global.lookup_inductive (destInd lbeq.eq) in
  let kind = inductive_sort_family mip in
  (* use ind rather than case by compatibility *)
  let kind =
    if kind == InProp then Elimschemes.ind_scheme_kind_from_prop
    else Elimschemes.ind_scheme_kind_from_type in
  let c, eff = find_scheme kind (destInd lbeq.eq) in
  mkConst c, eff


let discrimination_pf e (t,t1,t2) discriminator lbeq =
  let i            = build_coq_I () in
  let absurd_term  = build_coq_False () in
  let eq_elim, eff = ind_scheme_of_eq lbeq in
  (applist (eq_elim, [t;t1;mkNamedLambda e t discriminator;i;t2]), absurd_term),
  eff

let eq_baseid = Id.of_string "e"

let apply_on_clause (f,t) clause =
  let sigma =  clause.evd in
  let f_clause = mk_clenv_from_env clause.env sigma None (f,t) in
  let argmv =
    (match kind_of_term (last_arg f_clause.templval.Evd.rebus) with
     | Meta mv -> mv
     | _  -> errorlabstrm "" (str "Ill-formed clause applicator.")) in
  clenv_fchain argmv f_clause clause

let discr_positions env sigma (lbeq,eqn,(t,t1,t2)) eq_clause cpath dirn sort =
  let e = next_ident_away eq_baseid (ids_of_context env) in
  let e_env = push_named (e,None,t) env in
  let discriminator =
    build_discriminator sigma e_env dirn (mkVar e) sort cpath in
  let (pf, absurd_term), eff =
    discrimination_pf e (t,t1,t2) discriminator lbeq in
  let pf_ty = mkArrow eqn absurd_term in
  let absurd_clause = apply_on_clause (pf,pf_ty) eq_clause in
  let pf = clenv_value_cast_meta absurd_clause in
  Proofview.tclEFFECTS eff <*>
  tclTHENS (cut_intro absurd_term)
    [onLastHypId gen_absurdity; (Proofview.V82.tactic (refine pf))]

let discrEq (lbeq,_,(t,t1,t2) as u) eq_clause =
  let sigma = eq_clause.evd in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let concl = Proofview.Goal.concl gl in
    match find_positions env sigma t1 t2 with
    | Inr _ ->
	Proofview.tclZERO (Errors.UserError ("discr" , str"Not a discriminable equality."))
    | Inl (cpath, (_,dirn), _) ->
	let sort = pf_apply get_type_of gl concl in
	discr_positions env sigma u eq_clause cpath dirn sort
  end

let onEquality with_evars tac (c,lbindc) =
  Proofview.Goal.raw_enter begin fun gl ->
  let type_of = pf_type_of gl in
  let reduce_to_quantified_ind = pf_apply Tacred.reduce_to_quantified_ind gl in
  let t = type_of c in
  let t' = try snd (reduce_to_quantified_ind t) with UserError _ -> t in
  let eq_clause = pf_apply make_clenv_binding gl (c,t') lbindc in
  let eq_clause' = clenv_pose_dependent_evars with_evars eq_clause in
  let eqn = clenv_type eq_clause' in
  let (eq,eq_args) = find_this_eq_data_decompose gl eqn in
  tclTHEN
    (Proofview.V82.tclEVARS eq_clause'.evd)
    (tac (eq,eqn,eq_args) eq_clause')
  end

let onNegatedEquality with_evars tac =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let ccl = Proofview.Goal.concl gl in
    let env = Proofview.Goal.env gl in
    match kind_of_term (hnf_constr env sigma ccl) with
    | Prod (_,t,u) when is_empty_type u ->
        tclTHEN introf
          (onLastHypId (fun id ->
            onEquality with_evars tac (mkVar id,NoBindings)))
    | _ ->
        Proofview.tclZERO (Errors.UserError ("" , str "Not a negated primitive equality."))
  end

let discrSimpleClause with_evars = function
  | None -> onNegatedEquality with_evars discrEq
  | Some id -> onEquality with_evars discrEq (mkVar id,NoBindings)

let discr with_evars = onEquality with_evars discrEq

let discrClause with_evars = onClause (discrSimpleClause with_evars)

let discrEverywhere with_evars =
(*
  tclORELSE
*)
    (if discr_do_intro () then
      (tclTHEN
	(tclREPEAT introf)
	(tryAllHyps
          (fun id -> tclCOMPLETE (discr with_evars (mkVar id,NoBindings)))))
     else (* <= 8.2 compat *)
       tryAllHypsAndConcl (discrSimpleClause with_evars))
(*    (fun gls ->
       errorlabstrm "DiscrEverywhere" (str"No discriminable equalities."))
*)
let discr_tac with_evars = function
  | None -> discrEverywhere with_evars
  | Some c -> onInductionArg (discr with_evars) c

let discrConcl = discrClause false onConcl
let discrHyp id = discrClause false (onHyp id)

(* returns the sigma type (sigS, sigT) with the respective
    constructor depending on the sort *)
(* J.F.: correction du bug #1167 en accord avec Hugo. *)

let find_sigma_data s = build_sigma_type ()

(* [make_tuple env sigma (rterm,rty) lind] assumes [lind] is the lesser
   index bound in [rty]

   Then we build the term

     [(existT A P (mkRel lind) rterm)] of type [(sigS A P)]

   where [A] is the type of [mkRel lind] and [P] is [\na:A.rty{1/lind}]
 *)

let make_tuple env sigma (rterm,rty) lind =
  assert (dependent (mkRel lind) rty);
  let {intro = exist_term; typ = sig_term} =
    find_sigma_data (get_sort_of env sigma rty) in
  let a = type_of env sigma (mkRel lind) in
  let (na,_,_) = lookup_rel lind env in
  (* We move [lind] to [1] and lift other rels > [lind] by 1 *)
  let rty = lift (1-lind) (liftn lind (lind+1) rty) in
  (* Now [lind] is [mkRel 1] and we abstract on (na:a) *)
  let p = mkLambda (na, a, rty) in
  (applist(exist_term,[a;p;(mkRel lind);rterm]),
   applist(sig_term,[a;p]))

(* check that the free-references of the type of [c] are contained in
   the free-references of the normal-form of that type. Strictly
   computing the exact set of free rels would require full
   normalization but this is not reasonable (e.g. in presence of
   records that contains proofs). We restrict ourself to a "simpl"
   normalization *)

let minimal_free_rels env sigma (c,cty) =
  let cty_rels = free_rels cty in
  let cty' = simpl env sigma cty in
  let rels' = free_rels cty' in
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
    let folder rels i = snd (minimalrec_free_rels_rec rels (c, type_of env sigma (mkRel i)))
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
  let { intro = exist_term } = find_sigma_data sort_of_ty in
  let evdref = ref (Evd.create_goal_evar_defs sigma) in
  let rec sigrec_clausal_form siglen p_i =
    if Int.equal siglen 0 then
      (* is the default value typable with the expected type *)
      let dflt_typ = type_of env sigma dflt in
      try
	let () = evdref := Evarconv.the_conv_x_leq env dflt_typ p_i !evdref in
	let () = evdref := Evarconv.consider_remaining_unif_problems env !evdref in
	dflt
      with Evarconv.UnableToUnify _ ->
	error "Cannot solve a unification problem."
    else
      let (a,p_i_minus_1) = match whd_beta_stack !evdref p_i with
	| (_sigS,[a;p]) -> (a,p)
 	| _ -> anomaly ~label:"sig_clausal_form" (Pp.str "should be a sigma type") in
      let ev = Evarutil.e_new_evar evdref env a in
      let rty = beta_applist(p_i_minus_1,[ev]) in
      let tuple_tail = sigrec_clausal_form (siglen-1) rty in
      match
        Evd.existential_opt_value !evdref
          (destEvar ev)
      with
	| Some w ->
            let w_type = type_of env sigma w in
            if Evarconv.e_cumul env evdref w_type a then
              applist(exist_term,[w_type;p_i_minus_1;w;tuple_tail])
            else
              error "Cannot solve a unification problem."
	| None -> anomaly (Pp.str "Not enough components to build the dependent tuple")
  in
  let scf = sigrec_clausal_form siglen ty in
  Evarutil.nf_evar !evdref scf

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
   [make_iterated_tuple sigma env (term,typ) (z,zty)] is to build the
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
  let (tuple,tuplety) =
    List.fold_left (make_tuple env sigma) (z,zty) sorted_rels
  in
  assert (closed0 tuplety);
  let n = List.length sorted_rels in
  let dfltval = sig_clausal_form env sigma sort_of_zty n tuplety dflt in
  (tuple,tuplety,dfltval)

let rec build_injrec sigma env dflt c = function
  | [] -> make_iterated_tuple env sigma dflt (c,type_of env sigma c)
  | ((sp,cnum),argnum)::l ->
    try
      let (cnum_nlams,cnum_env,kont) = descend_then sigma env c cnum in
      let newc = mkRel(cnum_nlams-argnum) in
      let (subval,tuplety,dfltval) = build_injrec sigma cnum_env dflt newc l in
      (kont subval (dfltval,tuplety),
      tuplety,dfltval)
    with
	UserError _ -> failwith "caught"

let build_injector sigma env dflt c cpath =
  let (injcode,resty,_) = build_injrec sigma env dflt c cpath in
  (injcode,resty)

(*
let try_delta_expand env sigma t =
  let whdt = whd_betadeltaiota env sigma t  in
  let rec hd_rec c  =
    match kind_of_term c with
      | Construct _ -> whdt
      | App (f,_)  -> hd_rec f
      | Cast (c,_,_) -> hd_rec c
      | _  -> t
  in
  hd_rec whdt
*)

(* Given t1=t2 Inj calculates the whd normal forms of t1 and t2 and it
   expands then only when the whdnf has a constructor of an inductive type
   in hd position, otherwise delta expansion is not done *)

let simplify_args env sigma t =
  (* Quick hack to reduce in arguments of eq only *)
  match decompose_app t with
    | eq, [t;c1;c2] -> applist (eq,[t;simpl env sigma c1;simpl env sigma c2])
    | eq, [t1;c1;t2;c2] -> applist (eq,[t1;simpl env sigma c1;t2;simpl env sigma c2])
    | _ -> t

let inject_at_positions env sigma l2r (eq,_,(t,t1,t2)) eq_clause posns tac =
  let e = next_ident_away eq_baseid (ids_of_context env) in
  let e_env = push_named (e, None,t) env in
  let filter (cpath, t1', t2') =
    try
      (* arbitrarily take t1' as the injector default value *)
      let (injbody,resty) = build_injector sigma e_env t1' (mkVar e) cpath in
      let injfun = mkNamedLambda e t injbody in
      let pf = applist(eq.congr,[t;resty;injfun;t1;t2]) in
      let pf_typ = get_type_of env sigma pf in
      let inj_clause = apply_on_clause (pf,pf_typ) eq_clause in
      let pf = clenv_value_cast_meta inj_clause in
      let ty = simplify_args env sigma (clenv_type inj_clause) in
      Some (pf, ty)
    with Failure _ -> None
  in
  let injectors = List.map_filter filter posns in
  if List.is_empty injectors then
    Proofview.tclZERO (Errors.UserError ("Equality.inj" , str "Failed to decompose the equality."))
  else
    Proofview.tclBIND
      (Proofview.Monad.List.map
         (fun (pf,ty) -> tclTHENS (cut ty) [Proofview.tclUNIT (); Proofview.V82.tactic (refine pf)])
         (if l2r then List.rev injectors else injectors))
      (fun _ -> tac (List.length injectors))

exception Not_dep_pair

let eq_dec_scheme_kind_name = ref (fun _ -> failwith "eq_dec_scheme undefined")
let set_eq_dec_scheme_kind k = eq_dec_scheme_kind_name := (fun _ -> k)

let eqdep_dec = qualid_of_string "Coq.Logic.Eqdep_dec"

let inject_if_homogenous_dependent_pair env sigma (eq,_,(t,t1,t2)) =
  Proofview.Goal.raw_enter begin fun gl ->
  (* fetch the informations of the  pair *)
  let ceq = constr_of_global Coqlib.glob_eq in
  let sigTconstr () = (Coqlib.build_sigma_type()).Coqlib.typ in
  let eqTypeDest = fst (destApp t) in
  let _,ar1 = destApp t1 and
      _,ar2 = destApp t2 in
  let ind = destInd ar1.(0) in
  (* check whether the equality deals with dep pairs or not *)
  (* if yes, check if the user has declared the dec principle *)
  (* and compare the fst arguments of the dep pair *)
  let new_eq_args = [|type_of env sigma ar1.(3);ar1.(3);ar2.(3)|] in
  if (eq_constr eqTypeDest (sigTconstr())) &&
    (Ind_tables.check_scheme (!eq_dec_scheme_kind_name()) ind) &&
    (is_conv env sigma ar1.(2) ar2.(2))
  then begin
    Library.require_library [Loc.ghost,eqdep_dec] (Some false);
    let inj2 = Coqlib.coq_constant "inj_pair2_eq_dec is missing"
      ["Logic";"Eqdep_dec"] "inj_pair2_eq_dec" in
    let c, eff = find_scheme (!eq_dec_scheme_kind_name()) ind in
      (* cut with the good equality and prove the requested goal *)
    tclTHENS (tclTHEN (Proofview.tclEFFECTS eff) (cut (mkApp (ceq,new_eq_args))))
      [tclIDTAC; tclTHEN (Proofview.V82.tactic (apply (
        mkApp(inj2,[|ar1.(0);mkConst c;ar1.(1);ar1.(2);ar1.(3);ar2.(3)|])
       ))) (Auto.trivial [] [])
      ]
  (* not a dep eq or no decidable type found *)
  end
  else raise Not_dep_pair
  end

let injEqThen tac l2r (eq,_,(t,t1,t2) as u) eq_clause =
  let sigma = eq_clause.evd in
  let env = eq_clause.env in
  match find_positions env sigma t1 t2 with
  | Inl _ ->
     Proofview.tclZERO (Errors.UserError ("Inj",strbrk"This equality is discriminable. You should use the discriminate tactic to solve the goal."))
  | Inr [] ->
     Proofview.tclZERO (Errors.UserError ("Equality.inj",strbrk"No information can be deduced from this equality and the injectivity of constructors. This may be because the terms are convertible, or due to pattern restrictions in the sort Prop."))
  | Inr [([],_,_)] when Flags.version_strictly_greater Flags.V8_3 ->
     Proofview.tclZERO (Errors.UserError ("Equality.inj" , str"Nothing to inject."))
  | Inr posns ->
     Proofview.tclORELSE
       (inject_if_homogenous_dependent_pair env sigma u)
       begin function
         | Not_dep_pair as e |e when Errors.noncritical e ->
			       inject_at_positions env sigma l2r u eq_clause posns
						   (tac (clenv_value eq_clause))
         | reraise -> Proofview.tclZERO reraise
       end

let postInjEqTac ipats c n =
  match ipats with
  | Some ipats ->
      let clear_tac =
        if use_injection_pattern_l2r_order () && isVar c
        then tclTRY (clear [destVar c])
        else tclIDTAC in
      let ipats =
        if use_injection_pattern_l2r_order ()
        then adjust_intro_patterns n ipats
        else ipats in
      tclTHEN
        (clear_tac)
        (intros_pattern MoveLast ipats)
  | None -> tclIDTAC

let injEq ipats =
  let l2r =
    if use_injection_pattern_l2r_order () && not (Option.is_empty ipats) then true else false
  in
  injEqThen (fun c i -> postInjEqTac ipats c i) l2r

let inj ipats with_evars = onEquality with_evars (injEq ipats)

let injClause ipats with_evars = function
  | None -> onNegatedEquality with_evars (injEq ipats)
  | Some c -> onInductionArg (inj ipats with_evars) c

let injConcl = injClause None false None
let injHyp id = injClause None false (Some (ElimOnIdent (Loc.ghost,id)))

let decompEqThen ntac (lbeq,_,(t,t1,t2) as u) clause =
  Proofview.Goal.enter begin fun gl ->
    let sort = pf_apply get_type_of gl (Proofview.Goal.concl gl) in
    let sigma =  clause.evd in
    let env = Proofview.Goal.env gl in
      match find_positions env sigma t1 t2 with
      | Inl (cpath, (_,dirn), _) ->
	  discr_positions env sigma u clause cpath dirn sort
      | Inr [] -> (* Change: do not fail, simplify clear this trivial hyp *)
        ntac (clenv_value clause) 0
    | Inr posns ->
	inject_at_positions env sigma true u clause posns
          (ntac (clenv_value clause))
  end

let dEqThen with_evars ntac = function
  | None -> onNegatedEquality with_evars (decompEqThen ntac)
  | Some c -> onInductionArg (onEquality with_evars (decompEqThen ntac)) c

let dEq with_evars = dEqThen with_evars (fun c x -> Proofview.tclUNIT ())

let _ = declare_intro_decomp_eq (fun tac -> decompEqThen (fun _ -> tac))

let swap_equality_args = function
  | MonomorphicLeibnizEq (e1,e2) -> [e2;e1]
  | PolymorphicLeibnizEq (t,e1,e2) -> [t;e2;e1]
  | HeterogenousEq (t1,e1,t2,e2) -> [t2;e2;t1;e1]

let swap_equands eqn =
  let (lbeq,eq_args) = find_eq_data eqn in
  applist(lbeq.eq,swap_equality_args eq_args)

let swapEquandsInConcl =
  Proofview.Goal.raw_enter begin fun gl ->
  let (lbeq,eq_args) = find_eq_data (pf_nf_concl gl) in
  let sym_equal = lbeq.sym in
  let args = swap_equality_args eq_args @ [Evarutil.mk_new_meta ()] in
  Proofview.V82.tactic (fun gl -> refine (applist (sym_equal, args)) gl)
  end

(* Refine from [|- P e2] to [|- P e1] and [|- e1=e2:>t] (body is P (Rel 1)) *)

let bareRevSubstInConcl lbeq body (t,e1,e2) =
  Proofview.Goal.raw_enter begin fun gl ->
  (* find substitution scheme *)
  let eq_elim, effs = find_elim lbeq.eq (Some false) false None None gl in
  (* build substitution predicate *)
  let p = lambda_create (Proofview.Goal.env gl) (t,body) in
  (* apply substitution scheme *)
  let args = [t; e1; p; Evarutil.mk_new_meta (); e2; Evarutil.mk_new_meta ()] in
  let tac gl = refine (applist (eq_elim, args)) gl in
  Proofview.V82.tactic tac
  end

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

let decomp_tuple_term env c t =
  let rec decomprec inner_code ex exty =
    let iterated_decomp =
    try
      let {proj1=p1; proj2=p2},(a,p,car,cdr) = find_sigma_data_decompose ex in
      let car_code = applist (p1,[a;p;inner_code])
      and cdr_code = applist (p2,[a;p;inner_code]) in
      let cdrtyp = beta_applist (p,[car]) in
      List.map (fun l -> ((car,a),car_code)::l) (decomprec cdr_code cdr cdrtyp)
    with ConstrMatching.PatternMatchingFailure ->
      []
    in
    [((ex,exty),inner_code)]::iterated_decomp
  in
  decomprec (mkRel 1) c t

let subst_tuple_term env sigma dep_pair1 dep_pair2 b =
  let typ = get_type_of env sigma dep_pair1 in
  (* We find all possible decompositions *)
  let decomps1 = decomp_tuple_term env dep_pair1 typ in
  let decomps2 = decomp_tuple_term env dep_pair2 typ in
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
      (fun (e,t) body -> lambda_create env (t,subst_term e body)) e1_list b in
  let pred_body = beta_applist(abst_B,proj_list) in
  let expected_goal = beta_applist (abst_B,List.map fst e2_list) in
  (* Simulate now the normalisation treatment made by Logic.mk_refgoals *)
  let expected_goal = nf_betaiota sigma expected_goal in
  pred_body,expected_goal

(* Like "replace" but decompose dependent equalities *)

exception NothingToRewrite

let cutSubstInConcl_RL eqn =
  Proofview.Goal.raw_enter begin fun gl ->
  let (lbeq,(t,e1,e2 as eq)) = find_eq_data_decompose gl eqn in
  let concl = pf_nf_concl gl in
  let body,expected_goal = pf_apply subst_tuple_term gl e2 e1 concl in
  if not (dependent (mkRel 1) body) then raise NothingToRewrite;
  tclTHENFIRST
    (bareRevSubstInConcl lbeq body eq)
    (Proofview.V82.tactic (fun gl -> convert_concl expected_goal DEFAULTcast gl))
  end

(* |- (P e1)
     BY CutSubstInConcl_LR (eq T e1 e2)
     |- (P e2)
     |- (eq T e1 e2)
 *)
let cutSubstInConcl_LR eqn =
  tclTHENS (cutSubstInConcl_RL (swap_equands eqn))
     [tclIDTAC; swapEquandsInConcl]

let cutSubstInConcl l2r =if l2r then cutSubstInConcl_LR else cutSubstInConcl_RL

let cutSubstInHyp_LR eqn id =
  Proofview.Goal.enter begin fun gl ->
  let (lbeq,(t,e1,e2 as eq)) = find_eq_data_decompose gl eqn in
  let idtyp = pf_get_hyp_typ id gl in
  let body,expected_goal = pf_apply subst_tuple_term gl e1 e2 idtyp in
  if not (dependent (mkRel 1) body) then raise NothingToRewrite;
  let refine = Proofview.V82.tactic (fun gl -> Tacmach.refine_no_check (mkVar id) gl) in
  let subst = Proofview.V82.of_tactic (tclTHENFIRST (bareRevSubstInConcl lbeq body eq) refine) in
  Proofview.V82.tactic (fun gl -> cut_replacing id expected_goal subst gl)
  end

let cutSubstInHyp_RL eqn id =
  tclTHENS (cutSubstInHyp_LR (swap_equands eqn) id)
     ([tclIDTAC;
       swapEquandsInConcl])

let cutSubstInHyp l2r = if l2r then cutSubstInHyp_LR else cutSubstInHyp_RL

let try_rewrite tac =
  Proofview.tclORELSE tac begin function
    | ConstrMatching.PatternMatchingFailure ->
	tclZEROMSG (str "Not a primitive equality here.")
    | e when catchable_exception e ->
	tclZEROMSG
          (strbrk "Cannot find a well-typed generalization of the goal that makes the proof progress.")
    | NothingToRewrite ->
	tclZEROMSG
          (strbrk "Nothing to rewrite.")
    | e -> Proofview.tclZERO e
  end

let cutSubstClause l2r eqn cls =
  match cls with
    | None ->    cutSubstInConcl l2r eqn
    | Some id -> cutSubstInHyp l2r eqn id

let cutRewriteClause l2r eqn cls = try_rewrite (cutSubstClause l2r eqn cls)
let cutRewriteInHyp l2r eqn id = cutRewriteClause l2r eqn (Some id)
let cutRewriteInConcl l2r eqn = cutRewriteClause l2r eqn None

let substClause l2r c cls =
  Proofview.Goal.raw_enter begin fun gl ->
  let eq = pf_apply get_type_of gl c in
  tclTHENS (cutSubstClause l2r eq cls)
    [Proofview.tclUNIT (); Proofview.V82.tactic (exact_no_check c)]
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

let unfold_body x =
  Proofview.Goal.raw_enter begin fun gl ->
  (** We normalize the given hypothesis immediately. *)
  let hyps = Proofview.Goal.hyps (Proofview.Goal.assume gl) in
  let (_, xval, _) = Context.lookup_named x hyps in
  let xval = match xval with
  | None -> errorlabstrm "unfold_body"
    (pr_id x ++ str" is not a defined hypothesis.")
  | Some xval -> pf_nf_evar gl xval
  in
  afterHyp x begin fun aft ->
  let hl = List.fold_right (fun (y,yval,_) cl -> (y,InHyp) :: cl) aft [] in
  let xvar = mkVar x in
  let rfun _ _ c = replace_term xvar xval c in
  let reducth h = Proofview.V82.tactic (fun gl -> reduct_in_hyp rfun h gl) in
  let reductc = Proofview.V82.tactic (fun gl -> reduct_in_concl (rfun, DEFAULTcast) gl) in
  tclTHENLIST [tclMAP reducth hl; reductc]
  end
  end


let restrict_to_eq_and_identity eq = (* compatibility *)
  if not (eq_constr eq (constr_of_global glob_eq)) &&
    not (eq_constr eq (constr_of_global glob_identity))
  then raise ConstrMatching.PatternMatchingFailure

exception FoundHyp of (Id.t * constr * bool)

(* tests whether hyp [c] is [x = t] or [t = x], [x] not occuring in [t] *)
let is_eq_x gl x (id,_,c) =
  try
    let c = pf_nf_evar gl c in
    let (_,lhs,rhs) = snd (find_eq_data_decompose gl c) in
    if (eq_constr x lhs) && not (occur_term x rhs) then raise (FoundHyp (id,rhs,true));
    if (eq_constr x rhs) && not (occur_term x lhs) then raise (FoundHyp (id,lhs,false))
  with ConstrMatching.PatternMatchingFailure ->
    ()

(* Rewrite "hyp:x=rhs" or "hyp:rhs=x" (if dir=false) everywhere and
   erase hyp and x; proceed by generalizing all dep hyps *)

let subst_one dep_proof_ok x (hyp,rhs,dir) =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let hyps = Proofview.Goal.hyps gl in
  let concl = Proofview.Goal.concl gl in
  (* The set of hypotheses using x *)
  let depdecls =
    let test (id,_,c as dcl) =
      if not (Id.equal id hyp) && occur_var_in_decl env x dcl then Some dcl
      else None in
    List.rev (List.map_filter test hyps) in
  let dephyps = List.map (fun (id,_,_) -> id) depdecls in
  (* Decides if x appears in conclusion *)
  let depconcl = occur_var env x concl in
  (* The set of non-defined hypothesis: they must be abstracted,
     rewritten and reintroduced *)
  let abshyps =
    List.map_filter (function (id, None, _) -> Some (mkVar id) | _ -> None)
      depdecls in
  (* a tactic that either introduce an abstracted and rewritten hyp,
     or introduce a definition where x was replaced *)
  let introtac = function
      (id,None,_) -> intro_using id
    | (id,Some hval,htyp) ->
        letin_tac None (Name id)
	  (replace_term (mkVar x) rhs hval)
	  (Some (replace_term (mkVar x) rhs htyp)) nowhere
  in
  let need_rewrite = not (List.is_empty dephyps) || depconcl in
  tclTHENLIST
    ((if need_rewrite then
      [Proofview.V82.tactic (generalize abshyps);
       general_rewrite dir AllOccurrences true dep_proof_ok (mkVar hyp);
       Proofview.V82.tactic (thin dephyps);
       (tclMAP introtac depdecls)]
      else
       [Proofview.tclUNIT ()]) @
     [tclTRY (clear [x; hyp])])
  end

(* Look for an hypothesis hyp of the form "x=rhs" or "rhs=x", rewrite
   it everywhere, and erase hyp and x; proceed by generalizing all dep hyps *)

let subst_one_var dep_proof_ok x =
  Proofview.Goal.raw_enter begin fun gl ->
    let gl = Proofview.Goal.assume gl in
    let (_,xval,_) = pf_get_hyp x gl in
    (* If x has a body, simply replace x with body and clear x *)
    if not (Option.is_empty xval) then tclTHEN (unfold_body x) (clear [x]) else
      (* x is a variable: *)
      let varx = mkVar x in
      (* Find a non-recursive definition for x *)
      let res =
        try
          (** [is_eq_x] ensures nf_evar on its side *)
          let hyps = Proofview.Goal.hyps gl in
          let test hyp _ = is_eq_x gl varx hyp in
          Context.fold_named_context test ~init:() hyps;
          errorlabstrm "Subst"
            (str "Cannot find any non-recursive equality over " ++ pr_id x ++
	       str".")
        with FoundHyp res -> res in
      subst_one dep_proof_ok x res
  end

let subst_gen dep_proof_ok ids =
  tclTHEN Proofview.V82.nf_evar_goals (tclMAP (subst_one_var dep_proof_ok) ids)

(* For every x, look for an hypothesis hyp of the form "x=rhs" or "rhs=x",
   rewrite it everywhere, and erase hyp and x; proceed by generalizing
   all dep hyps *)

let subst = subst_gen true

type subst_tactic_flags = {
  only_leibniz : bool;
  rewrite_dependent_proof : bool
}

let default_subst_tactic_flags () =
  if Flags.version_strictly_greater Flags.V8_2 then
    { only_leibniz = false; rewrite_dependent_proof = true }
  else
    { only_leibniz = true; rewrite_dependent_proof = false }

let subst_all ?(flags=default_subst_tactic_flags ()) () =
  Proofview.Goal.enter begin fun gl ->
  let find_eq_data_decompose = find_eq_data_decompose gl in
  let test (_,c) =
    try
      let lbeq,(_,x,y) = find_eq_data_decompose c in
      if flags.only_leibniz then restrict_to_eq_and_identity lbeq.eq;
      (* J.F.: added to prevent failure on goal containing x=x as an hyp *)
      if eq_constr x y then failwith "caught";
      match kind_of_term x with Var x -> x | _ ->
      match kind_of_term y with Var y -> y | _ -> failwith "caught"
    with ConstrMatching.PatternMatchingFailure -> failwith "caught"
  in
  let test p = try Some (test p) with Failure _ -> None in
  let hyps = pf_hyps_types gl in
  let ids = List.map_filter test hyps in
  let ids = List.uniquize ids in
  subst_gen flags.rewrite_dependent_proof ids
  end

(* Rewrite the first assumption for which the condition faildir does not fail
   and gives the direction of the rewrite *)

let cond_eq_term_left c t gl =
  try
    let (_,x,_) = snd (find_eq_data_decompose gl t) in
    if pf_conv_x gl c x then true else failwith "not convertible"
  with ConstrMatching.PatternMatchingFailure -> failwith "not an equality"

let cond_eq_term_right c t gl =
  try
    let (_,_,x) = snd (find_eq_data_decompose gl t) in
    if pf_conv_x gl c x then false else failwith "not convertible"
  with ConstrMatching.PatternMatchingFailure -> failwith "not an equality"

let cond_eq_term c t gl =
  try
    let (_,x,y) = snd (find_eq_data_decompose gl t) in
    if pf_conv_x gl c x then true
    else if pf_conv_x gl c y then false
    else failwith "not convertible"
  with ConstrMatching.PatternMatchingFailure -> failwith "not an equality"

let rewrite_multi_assumption_cond cond_eq_term cl =
  let rec arec hyps gl = match hyps with
    | [] -> error "No such assumption."
    | (id,_,t) ::rest ->
	begin
	  try
            let dir = cond_eq_term t gl in
	    general_multi_rewrite dir false (mkVar id,NoBindings) cl
	  with | Failure _ | UserError _ -> arec rest gl
	end
  in
  Proofview.Goal.enter begin fun gl ->
    let hyps = Proofview.Goal.hyps gl in
    arec hyps gl
  end

let replace_multi_term dir_opt c  =
  let cond_eq_fun =
    match dir_opt with
      | None -> cond_eq_term c
      | Some true -> cond_eq_term_left c
      | Some false -> cond_eq_term_right c
  in
  rewrite_multi_assumption_cond cond_eq_fun

let _ =
  let gmr l2r with_evars tac c = general_multi_rewrite l2r with_evars tac c in
  Hook.set Tactics.general_multi_rewrite gmr

let _ = Hook.set Tactics.subst_one subst_one
