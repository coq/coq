(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Compat
open Pp
open Util
open Names
open Nameops
open Sign
open Term
open Termops
open Namegen
open Declarations
open Inductive
open Inductiveops
open Reductionops
open Environ
open Libnames
open Evd
open Pfedit
open Tacred
open Rawterm
open Tacmach
open Proof_type
open Logic
open Evar_refiner
open Clenv
open Clenvtac
open Refiner
open Tacticals
open Hipattern
open Coqlib
open Nametab
open Genarg
open Tacexpr
open Decl_kinds
open Evarutil
open Indrec
open Pretype_errors
open Unification

exception Bound

let rec nb_prod x =
  let rec count n c =
    match kind_of_term c with
        Prod(_,_,t) -> count (n+1) t
      | LetIn(_,a,_,t) -> count n (subst1 a t)
      | Cast(c,_,_) -> count n c
      | _ -> n
  in count 0 x

let inj_with_occurrences e = (all_occurrences_expr,e)

let dloc = dummy_loc

(* Option for 8.2 compatibility *)
open Goptions
let dependent_propositions_elimination = ref true

let use_dependent_propositions_elimination () =
  !dependent_propositions_elimination
  && Flags.version_strictly_greater Flags.V8_2

let _ =
  declare_bool_option
    { optsync  = true;
      optname  = "dependent-propositions-elimination tactic";
      optkey   = ["Dependent";"Propositions";"Elimination"];
      optread  = (fun () -> !dependent_propositions_elimination) ;
      optwrite = (fun b -> dependent_propositions_elimination := b) }

(*********************************************)
(*                 Tactics                   *)
(*********************************************)

(****************************************)
(* General functions                    *)
(****************************************)

let string_of_inductive c =
  try match kind_of_term c with
  | Ind ind_sp ->
      let (mib,mip) = Global.lookup_inductive ind_sp in
      string_of_id mip.mind_typename
  | _ -> raise Bound
  with Bound -> error "Bound head variable."

let rec head_constr_bound t =
  let t = strip_outer_cast t in
  let _,ccl = decompose_prod_assum t in
  let hd,args = decompose_app ccl in
  match kind_of_term hd with
    | Const _ | Ind _ | Construct _ | Var _ -> (hd,args)
    | _ -> raise Bound

let head_constr c =
  try head_constr_bound c with Bound -> error "Bound head variable."

(******************************************)
(*           Primitive tactics            *)
(******************************************)

let introduction    = Tacmach.introduction
let refine          = Tacmach.refine
let convert_concl   = Tacmach.convert_concl
let convert_hyp     = Tacmach.convert_hyp
let thin_body       = Tacmach.thin_body

let error_clear_dependency env id = function
  | Evarutil.OccurHypInSimpleClause None ->
      errorlabstrm "" (pr_id id ++ str " is used in conclusion.")
  | Evarutil.OccurHypInSimpleClause (Some id') ->
      errorlabstrm ""
        (pr_id id ++ strbrk " is used in hypothesis " ++ pr_id id' ++ str".")
  | Evarutil.EvarTypingBreak ev ->
      errorlabstrm ""
        (str "Cannot remove " ++ pr_id id ++
	 strbrk " without breaking the typing of " ++
	 Printer.pr_existential env ev ++ str".")

let thin l gl =
  try thin l gl
  with Evarutil.ClearDependencyError (id,err) ->
    error_clear_dependency (pf_env gl) id err

let internal_cut_gen b d t gl =
  try internal_cut b d t gl
  with Evarutil.ClearDependencyError (id,err) ->
    error_clear_dependency (pf_env gl) id err

let internal_cut = internal_cut_gen false
let internal_cut_replace = internal_cut_gen true

let internal_cut_rev_gen b d t gl =
  try internal_cut_rev b d t gl
  with Evarutil.ClearDependencyError (id,err) ->
    error_clear_dependency (pf_env gl) id err

let internal_cut_rev = internal_cut_rev_gen false
let internal_cut_rev_replace = internal_cut_rev_gen true

(* Moving hypotheses *)
let move_hyp        = Tacmach.move_hyp


(* Renaming hypotheses *)
let rename_hyp      = Tacmach.rename_hyp

(**************************************************************)
(*          Fresh names                                       *)
(**************************************************************)

let fresh_id_in_env avoid id env =
  next_ident_away_in_goal id (avoid@ids_of_named_context (named_context env))

let fresh_id avoid id gl =
  fresh_id_in_env avoid id (pf_env gl)

(**************************************************************)
(*          Fixpoints and CoFixpoints                         *)
(**************************************************************)

(* Refine as a fixpoint *)
let mutual_fix = Tacmach.mutual_fix

let fix ido n gl = match ido with
  | None ->
      mutual_fix (fresh_id [] (Pfedit.get_current_proof_name ()) gl) n [] 0 gl
  | Some id ->
      mutual_fix id n [] 0 gl

(* Refine as a cofixpoint *)
let mutual_cofix = Tacmach.mutual_cofix

let cofix ido gl = match ido with
  | None ->
      mutual_cofix (fresh_id [] (Pfedit.get_current_proof_name ()) gl) [] 0 gl
  | Some id ->
      mutual_cofix id [] 0 gl

(**************************************************************)
(*          Reduction and conversion tactics                  *)
(**************************************************************)

type tactic_reduction = env -> evar_map -> constr -> constr

let pf_reduce_decl redfun where (id,c,ty) gl =
  let redfun' = pf_reduce redfun gl in
  match c with
  | None ->
      if where = InHypValueOnly then
	errorlabstrm "" (pr_id id ++ str "has no value.");
      (id,None,redfun' ty)
  | Some b ->
      let b' = if where <> InHypTypeOnly then redfun' b else b in
      let ty' =	if where <> InHypValueOnly then redfun' ty else ty in
      (id,Some b',ty')

(* Possibly equip a reduction with the occurrences mentioned in an
   occurrence clause *)

let error_illegal_clause () =
  error "\"at\" clause not supported in presence of an occurrence clause."

let error_illegal_non_atomic_clause () =
  error "\"at\" clause not supported in presence of a non atomic \"in\" clause."

let error_occurrences_not_unsupported () =
  error "Occurrences not supported for this reduction tactic."

let bind_change_occurrences occs = function
  | None -> None
  | Some c -> Some (Redexpr.out_with_occurrences (occs,c))

let bind_red_expr_occurrences occs nbcl redexp =
  let has_at_clause = function
    | Unfold l -> List.exists (fun (occl,_) -> occl <> all_occurrences_expr) l
    | Pattern l -> List.exists (fun (occl,_) -> occl <> all_occurrences_expr) l
    | Simpl (Some (occl,_)) -> occl <> all_occurrences_expr
    | _ -> false in
  if occs = all_occurrences_expr then
    if nbcl > 1 && has_at_clause redexp then
      error_illegal_non_atomic_clause ()
    else
      redexp
  else
    match redexp with
    | Unfold (_::_::_) ->
	error_illegal_clause ()
    | Unfold [(occl,c)] ->
	if occl <> all_occurrences_expr then
	  error_illegal_clause ()
	else
	  Unfold [(occs,c)]
    | Pattern (_::_::_) ->
	error_illegal_clause ()
    | Pattern [(occl,c)] ->
	if occl <> all_occurrences_expr then
	  error_illegal_clause ()
	else
	  Pattern [(occs,c)]
    | Simpl (Some (occl,c)) ->
	if occl <> all_occurrences_expr then
	  error_illegal_clause ()
	else
	  Simpl (Some (occs,c))
    | Red _ | Hnf | Cbv _ | Lazy _
    | ExtraRedExpr _ | CbvVm | Fold _ | Simpl None ->
	error_occurrences_not_unsupported ()
    | Unfold [] | Pattern [] ->
	assert false

(* The following two tactics apply an arbitrary
   reduction function either to the conclusion or to a
   certain hypothesis *)

let reduct_in_concl (redfun,sty) gl =
  convert_concl_no_check (pf_reduce redfun gl (pf_concl gl)) sty gl

let reduct_in_hyp redfun (id,where) gl =
  convert_hyp_no_check
    (pf_reduce_decl redfun where (pf_get_hyp gl id) gl) gl

let reduct_option redfun = function
  | Some id -> reduct_in_hyp (fst redfun) id
  | None    -> reduct_in_concl redfun

(* Now we introduce different instances of the previous tacticals *)
let change_and_check cv_pb t env sigma c =
  if is_fconv cv_pb env sigma t c then
    t
  else
    errorlabstrm "convert-check-hyp" (str "Not convertible.")

(* Use cumulativity only if changing the conclusion not a subterm *)
let change_on_subterm cv_pb t = function
  | None -> change_and_check cv_pb t
  | Some occl ->
      contextually false occl
        (fun subst -> change_and_check Reduction.CONV (replace_vars subst t))

let change_in_concl occl t =
  reduct_in_concl ((change_on_subterm Reduction.CUMUL t occl),DEFAULTcast)

let change_in_hyp occl t id  =
  with_check (reduct_in_hyp (change_on_subterm Reduction.CONV t occl) id)

let change_option occl t = function
  | Some id -> change_in_hyp occl t id
  | None -> change_in_concl occl t

let change chg c cls gl =
  let cls = concrete_clause_of cls gl in
  tclMAP (function
    | OnHyp (id,occs,where) ->
       change_option (bind_change_occurrences occs chg) c (Some (id,where))
    | OnConcl occs ->
       change_option (bind_change_occurrences occs chg) c None)
    cls gl

(* Pour usage interne (le niveau User est pris en compte par reduce) *)
let try_red_in_concl    = reduct_in_concl (try_red_product,DEFAULTcast)
let red_in_concl        = reduct_in_concl (red_product,DEFAULTcast)
let red_in_hyp          = reduct_in_hyp   red_product
let red_option          = reduct_option   (red_product,DEFAULTcast)
let hnf_in_concl        = reduct_in_concl (hnf_constr,DEFAULTcast)
let hnf_in_hyp          = reduct_in_hyp   hnf_constr
let hnf_option          = reduct_option   (hnf_constr,DEFAULTcast)
let simpl_in_concl      = reduct_in_concl (simpl,DEFAULTcast)
let simpl_in_hyp        = reduct_in_hyp   simpl
let simpl_option        = reduct_option   (simpl,DEFAULTcast)
let normalise_in_concl  = reduct_in_concl (compute,DEFAULTcast)
let normalise_in_hyp    = reduct_in_hyp   compute
let normalise_option    = reduct_option   (compute,DEFAULTcast)
let normalise_vm_in_concl = reduct_in_concl (Redexpr.cbv_vm,VMcast)
let unfold_in_concl loccname = reduct_in_concl (unfoldn loccname,DEFAULTcast)
let unfold_in_hyp   loccname = reduct_in_hyp   (unfoldn loccname)
let unfold_option   loccname = reduct_option (unfoldn loccname,DEFAULTcast)
let pattern_option l = reduct_option (pattern_occs l,DEFAULTcast)

(* The main reduction function *)

let reduction_clause redexp cl =
  let nbcl = List.length cl in
  List.map (function
    | OnHyp (id,occs,where) ->
	(Some (id,where), bind_red_expr_occurrences occs nbcl redexp)
    | OnConcl occs ->
	(None, bind_red_expr_occurrences occs nbcl redexp)) cl

let reduce redexp cl goal =
  let cl = concrete_clause_of cl goal in
  let redexps = reduction_clause redexp cl in
  let tac = tclMAP (fun (where,redexp) ->
    reduct_option (Redexpr.reduction_of_red_expr redexp) where) redexps in
  match redexp with
  | Fold _ | Pattern _ -> with_check tac goal
  | _ -> tac goal

(* Unfolding occurrences of a constant *)

let unfold_constr = function
  | ConstRef sp -> unfold_in_concl [all_occurrences,EvalConstRef sp]
  | VarRef id -> unfold_in_concl [all_occurrences,EvalVarRef id]
  | _ -> errorlabstrm "unfold_constr" (str "Cannot unfold a non-constant.")

(*******************************************)
(*         Introduction tactics            *)
(*******************************************)

let id_of_name_with_default id = function
  | Anonymous -> id
  | Name id   -> id

let hid = id_of_string "H"
let xid = id_of_string "X"

let default_id_of_sort = function Prop _ -> hid | Type _ -> xid

let default_id env sigma = function
  | (name,None,t) ->
      let dft = default_id_of_sort (Typing.sort_of env sigma t) in
      id_of_name_with_default dft name
  | (name,Some b,_) -> id_of_name_using_hdchar env b name

(* Non primitive introduction tactics are treated by central_intro
   There is possibly renaming, with possibly names to avoid and
   possibly a move to do after the introduction *)

type intro_name_flag =
  | IntroAvoid of identifier list
  | IntroBasedOn of identifier * identifier list
  | IntroMustBe of identifier

let find_name loc decl gl = function
  | IntroAvoid idl ->
      (* this case must be compatible with [find_intro_names] below. *)
      let id = fresh_id idl (default_id (pf_env gl) gl.sigma decl) gl in id
  | IntroBasedOn (id,idl) -> fresh_id idl id gl
  | IntroMustBe id ->
      (* When name is given, we allow to hide a global name *)
      let id' = next_ident_away id (pf_ids_of_hyps gl) in
      if id'<>id then user_err_loc (loc,"",pr_id id ++ str" is already used.");
      id'

(* Returns the names that would be created by intros, without doing
   intros.  This function is supposed to be compatible with an
   iteration of [find_name] above. As [default_id] checks the sort of
   the type to build hyp names, we maintain an environment to be able
   to type dependent hyps. *)
let find_intro_names ctxt gl =
  let _, res = List.fold_right
    (fun decl acc ->
      let wantedname,x,typdecl = decl in
      let env,idl = acc in
      let name = fresh_id idl (default_id env gl.sigma decl) gl in
      let newenv = push_rel (wantedname,x,typdecl) env in
      (newenv,(name::idl)))
    ctxt (pf_env gl , []) in
  List.rev res

let build_intro_tac id = function
  | MoveToEnd true -> introduction id
  | dest -> tclTHEN (introduction id) (move_hyp true id dest)

let rec intro_gen loc name_flag move_flag force_flag dep_flag gl =
  match kind_of_term (pf_concl gl) with
    | Prod (name,t,u) when not dep_flag or (dependent (mkRel 1) u) ->
	build_intro_tac (find_name loc (name,None,t) gl name_flag) move_flag gl
    | LetIn (name,b,t,u) when not dep_flag or (dependent (mkRel 1) u) ->
	build_intro_tac (find_name loc (name,Some b,t) gl name_flag) move_flag
	  gl
    | _ ->
	if not force_flag then raise (RefinerError IntroNeedsProduct);
	try
	  tclTHEN try_red_in_concl
	    (intro_gen loc name_flag move_flag force_flag dep_flag) gl
	with Redelimination ->
	  user_err_loc(loc,"Intro",str "No product even after head-reduction.")

let intro_mustbe_force id = intro_gen dloc (IntroMustBe id) no_move true false
let intro_using id = intro_gen dloc (IntroBasedOn (id,[])) no_move false false
let intro = intro_gen dloc (IntroAvoid []) no_move false false
let introf = intro_gen dloc (IntroAvoid []) no_move true false
let intro_avoiding l = intro_gen dloc (IntroAvoid l) no_move false false

(**** Multiple introduction tactics ****)

let rec intros_using = function
  | []     -> tclIDTAC
  | str::l -> tclTHEN (intro_using str) (intros_using l)

let intros = tclREPEAT intro

let intro_erasing id = tclTHEN (thin [id]) (introduction id)

let intro_forthcoming_gen loc name_flag move_flag dep_flag =
    tclREPEAT (intro_gen loc name_flag  move_flag false dep_flag)

let rec get_next_hyp_position id = function
  | [] -> error ("No such hypothesis: " ^ string_of_id id)
  | (hyp,_,_) :: right ->
      if hyp = id then
	match right with (id,_,_)::_ -> MoveBefore id | [] -> MoveToEnd true
      else
	get_next_hyp_position id right

let thin_for_replacing l gl =
  try Tacmach.thin l gl
  with Evarutil.ClearDependencyError (id,err) -> match err with
  | Evarutil.OccurHypInSimpleClause None ->
      errorlabstrm ""
      (str "Cannot change " ++ pr_id id ++ str ", it is used in conclusion.")
  | Evarutil.OccurHypInSimpleClause (Some id') ->
      errorlabstrm ""
        (str "Cannot change " ++ pr_id id ++
	 strbrk ", it is used in hypothesis " ++ pr_id id' ++ str".")
  | Evarutil.EvarTypingBreak ev ->
      errorlabstrm ""
        (str "Cannot change " ++ pr_id id ++
	 strbrk " without breaking the typing of " ++
	 Printer.pr_existential (pf_env gl) ev ++ str".")

let intro_replacing id gl =
  let next_hyp = get_next_hyp_position id (pf_hyps gl) in
  tclTHENLIST
    [thin_for_replacing [id]; introduction id; move_hyp true id next_hyp] gl

let intros_replacing ids gl =
  let rec introrec = function
    | [] -> tclIDTAC
    | id::tl ->
	tclTHEN (tclORELSE (intro_replacing id) (intro_using id))
           (introrec tl)
  in
  introrec ids gl

(* User-level introduction tactics *)

let intro_move idopt hto = match idopt with
  | None -> intro_gen dloc (IntroAvoid []) hto true false
  | Some id -> intro_gen dloc (IntroMustBe id) hto true false

let pf_lookup_hypothesis_as_renamed env ccl = function
  | AnonHyp n -> Detyping.lookup_index_as_renamed env ccl n
  | NamedHyp id -> Detyping.lookup_name_as_displayed env ccl id

let pf_lookup_hypothesis_as_renamed_gen red h gl =
  let env = pf_env gl in
  let rec aux ccl =
    match pf_lookup_hypothesis_as_renamed env ccl h with
      | None when red ->
          aux
	    ((fst (Redexpr.reduction_of_red_expr (Red true)))
	       env (project gl) ccl)
      | x -> x
  in
  try aux (pf_concl gl)
  with Redelimination -> None

let is_quantified_hypothesis id g =
  match pf_lookup_hypothesis_as_renamed_gen true (NamedHyp id) g with
    | Some _ -> true
    | None -> false

let msg_quantified_hypothesis = function
  | NamedHyp id ->
      str "quantified hypothesis named " ++ pr_id id
  | AnonHyp n ->
      int n ++ str (match n with 1 -> "st" | 2 -> "nd" | _ -> "th") ++
      str " non dependent hypothesis"

let depth_of_quantified_hypothesis red h gl =
  match pf_lookup_hypothesis_as_renamed_gen red h gl with
    | Some depth -> depth
    | None ->
        errorlabstrm "lookup_quantified_hypothesis"
          (str "No " ++ msg_quantified_hypothesis h ++
	  strbrk " in current goal" ++
	  (if red then strbrk " even after head-reduction" else mt ()) ++
	  str".")

let intros_until_gen red h g =
  tclDO (depth_of_quantified_hypothesis red h g) intro g

let intros_until_id id = intros_until_gen true (NamedHyp id)
let intros_until_n_gen red n = intros_until_gen red (AnonHyp n)

let intros_until = intros_until_gen true
let intros_until_n = intros_until_n_gen true
let intros_until_n_wored = intros_until_n_gen false

let tclCHECKVAR id gl = ignore (pf_get_hyp gl id); tclIDTAC gl

let try_intros_until_id_check id =
  tclORELSE (intros_until_id id) (tclCHECKVAR id)

let try_intros_until tac = function
  | NamedHyp id -> tclTHEN (try_intros_until_id_check id) (tac id)
  | AnonHyp n -> tclTHEN (intros_until_n n) (onLastHypId tac)

let rec intros_move = function
  | [] -> tclIDTAC
  | (hyp,destopt) :: rest ->
      tclTHEN (intro_gen dloc (IntroMustBe hyp) destopt false false)
	(intros_move rest)

let dependent_in_decl a (_,c,t) =
  match c with
    | None -> dependent a t
    | Some body -> dependent a body || dependent a t

(* Apply a tactic on a quantified hypothesis, an hypothesis in context
   or a term with bindings *)

let onInductionArg tac = function
  | ElimOnConstr cbl ->
      tac cbl
  | ElimOnAnonHyp n ->
      tclTHEN (intros_until_n n) (onLastHyp (fun c -> tac (c,NoBindings)))
  | ElimOnIdent (_,id) ->
      (* A quantified hypothesis *)
      tclTHEN (try_intros_until_id_check id) (tac (mkVar id,NoBindings))

(**************************)
(*  Refinement tactics    *)
(**************************)

let apply_type hdcty argl gl =
  refine (applist (mkCast (Evarutil.mk_new_meta(),DEFAULTcast, hdcty),argl)) gl

let apply_term hdc argl gl =
  refine (applist (hdc,argl)) gl

let bring_hyps hyps =
  if hyps = [] then Refiner.tclIDTAC
  else
    (fun gl ->
      let newcl = List.fold_right mkNamedProd_or_LetIn hyps (pf_concl gl) in
      let f = mkCast (Evarutil.mk_new_meta(),DEFAULTcast, newcl) in
      refine_no_check (mkApp (f, instance_from_named_context hyps)) gl)

let resolve_classes gl =
  let env = pf_env gl and evd = project gl in
    if Evd.is_empty evd then tclIDTAC gl
    else
      let evd' = Typeclasses.resolve_typeclasses env (Evd.create_evar_defs evd) in
	(tclTHEN (tclEVARS evd') tclNORMEVAR) gl

(**************************)
(*     Cut tactics        *)
(**************************)

let cut c gl =
  match kind_of_term (pf_hnf_type_of gl c) with
    | Sort _ ->
        let id=next_name_away_with_default "H" Anonymous (pf_ids_of_hyps gl) in
        let t = mkProd (Anonymous, c, pf_concl gl) in
          tclTHENFIRST
            (internal_cut_rev id c)
            (tclTHEN (apply_type t [mkVar id]) (thin [id]))
            gl
    | _  -> error "Not a proposition or a type."

let cut_intro t = tclTHENFIRST (cut t) intro

(* [assert_replacing id T tac] adds the subgoals of the proof of [T]
   before the current goal

   id:T0                 id:T0    id:T     
   =====   ------>   tac(=====) + ==== 
    G                     T        G

   It fails if the hypothesis to replace appears in the goal or in
   another hypothesis.
*) 

let assert_replacing id t tac = tclTHENFIRST (internal_cut_replace id t) tac

(* [cut_replacing id T tac] adds the subgoals of the proof of [T]
   after the current goal

   id:T0             id:T       id:T0
   =====   ------>   ==== + tac(=====)
    G                 G          T

   It fails if the hypothesis to replace appears in the goal or in
   another hypothesis.
*)

let cut_replacing id t tac = tclTHENLAST (internal_cut_rev_replace id t) tac

let cut_in_parallel l =
  let rec prec = function
    | [] -> tclIDTAC
    | h::t -> tclTHENFIRST (cut h) (prec t)
  in
    prec (List.rev l)

let error_uninstantiated_metas t clenv =
  let na = meta_name clenv.evd (List.hd (Metaset.elements (metavars_of t))) in
  let id = match na with Name id -> id | _ -> anomaly "unnamed dependent meta"
  in errorlabstrm "" (str "Cannot find an instance for " ++ pr_id id ++ str".")

(* For a clenv expressing some lemma [C[?1:T1,...,?n:Tn] : P] and some
   goal [G], [clenv_refine_in] returns [n+1] subgoals, the [n] last
   ones (resp [n] first ones if [sidecond_first] is [true]) being the
   [Ti] and the first one (resp last one) being [G] whose hypothesis
   [id] is replaced by P using the proof given by [tac] *)

let clenv_refine_in ?(sidecond_first=false) with_evars ?(with_classes=true) id clenv gl =
  let clenv = clenv_pose_dependent_evars with_evars clenv in
  let clenv =
    if with_classes then
      { clenv with evd = Typeclasses.resolve_typeclasses ~fail:(not with_evars) clenv.env clenv.evd }
    else clenv
  in
  let new_hyp_typ = clenv_type clenv in
  if not with_evars & occur_meta new_hyp_typ then
    error_uninstantiated_metas new_hyp_typ clenv;
  let new_hyp_prf = clenv_value clenv in
  tclTHEN
    (tclEVARS clenv.evd)
    ((if sidecond_first then assert_replacing else cut_replacing)
      id new_hyp_typ (refine_no_check new_hyp_prf)) gl

(********************************************)
(*       Elimination tactics                *)
(********************************************)

let last_arg c = match kind_of_term c with
  | App (f,cl) ->
      array_last cl
  | _ -> anomaly "last_arg"

let nth_arg i c =
  if i = -1 then last_arg c else
  match kind_of_term c with
  | App (f,cl) -> cl.(i)
  | _ -> anomaly "nth_arg"

let index_of_ind_arg t =
  let rec aux i j t = match kind_of_term t with
  | Prod (_,t,u) ->
      (* heuristic *)
      if isInd (fst (decompose_app t)) then aux (Some j) (j+1) u
      else aux i (j+1) u
  | _ -> match i with
      | Some i -> i
      | None -> error "Could not find inductive argument of elimination scheme."
  in aux None 0 t

let elim_flags = {
  modulo_conv_on_closed_terms = Some full_transparent_state;
  use_metas_eagerly = true;
  modulo_delta = empty_transparent_state;
  resolve_evars = false;
  use_evars_pattern_unification = true;
  modulo_eta = true
}

let elimination_clause_scheme with_evars allow_K i elimclause indclause gl =
  let indmv =
    (match kind_of_term (nth_arg i elimclause.templval.rebus) with
       | Meta mv -> mv
       | _  -> errorlabstrm "elimination_clause"
             (str "The type of elimination clause is not well-formed."))
  in
  let elimclause' = clenv_fchain ~flags:elim_flags indmv elimclause indclause in
  res_pf elimclause' ~with_evars:with_evars ~allow_K:allow_K ~flags:elim_flags
    gl

(*
 * Elimination tactic with bindings and using an arbitrary
 * elimination constant called elimc. This constant should end
 * with a clause (x:I)(P .. ), where P is a bound variable.
 * The term c is of type t, which is a product ending with a type
 * matching I, lbindc are the expected terms for c arguments
 *)

type eliminator = {
  elimindex : int option;  (* None = find it automatically *)
  elimbody : constr with_bindings
}

let general_elim_clause_gen elimtac indclause elim gl =
  let (elimc,lbindelimc) = elim.elimbody in
  let elimt = pf_type_of gl elimc in
  let i =
    match elim.elimindex with None -> index_of_ind_arg elimt | Some i -> i in
  let elimclause = make_clenv_binding gl (elimc,elimt) lbindelimc in
  elimtac i elimclause indclause gl

let general_elim_clause elimtac (c,lbindc) elim gl =
  let ct = pf_type_of gl c in
  let t = try snd (pf_reduce_to_quantified_ind gl ct) with UserError _ -> ct in
  let indclause  = make_clenv_binding gl (c,t) lbindc  in
    general_elim_clause_gen elimtac indclause elim gl

let general_elim with_evars c e ?(allow_K=true) =
  general_elim_clause (elimination_clause_scheme with_evars allow_K) c e

(* Elimination tactic with bindings but using the default elimination
 * constant associated with the type. *)

let find_eliminator c gl =
  let (ind,t) = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
  let c = lookup_eliminator ind (elimination_sort_of_goal gl) in
  {elimindex = None; elimbody = (c,NoBindings)}

let default_elim with_evars (c,_ as cx) gl =
  general_elim with_evars cx (find_eliminator c gl) gl

let elim_in_context with_evars c = function
  | Some elim ->
      general_elim with_evars c {elimindex = Some (-1); elimbody = elim}
	~allow_K:true
  | None -> default_elim with_evars c

let elim with_evars (c,lbindc as cx) elim =
  match kind_of_term c with
    | Var id when lbindc = NoBindings ->
	tclTHEN (try_intros_until_id_check id)
	  (elim_in_context with_evars cx elim)
    | _ ->
	elim_in_context with_evars cx elim

(* The simplest elimination tactic, with no substitutions at all. *)

let simplest_elim c = default_elim false (c,NoBindings)

(* Elimination in hypothesis *)
(* Typically, elimclause := (eq_ind ?x ?P ?H ?y ?Heq : ?P ?y)
              indclause : forall ..., hyps -> a=b    (to take place of ?Heq)
              id : phi(a)                            (to take place of ?H)
      and the result is to overwrite id with the proof of phi(b)

   but this generalizes to any elimination scheme with one constructor
   (e.g. it could replace id:A->B->C by id:C, knowing A/\B)
*)

let clenv_fchain_in id elim_flags mv elimclause hypclause =
  try clenv_fchain ~allow_K:false ~flags:elim_flags mv elimclause hypclause
  with PretypeError (env,NoOccurrenceFound (op,_)) ->
    (* Set the hypothesis name in the message *)
    raise (PretypeError (env,NoOccurrenceFound (op,Some id)))

let elimination_in_clause_scheme with_evars id i elimclause indclause gl =
  let indmv = destMeta (nth_arg i elimclause.templval.rebus) in
  let hypmv =
    try match list_remove indmv (clenv_independent elimclause) with
      | [a] -> a
      | _ -> failwith ""
    with Failure _ -> errorlabstrm "elimination_clause"
          (str "The type of elimination clause is not well-formed.") in
  let elimclause'  = clenv_fchain indmv elimclause indclause in
  let hyp = mkVar id in
  let hyp_typ = pf_type_of gl hyp in
  let hypclause = mk_clenv_from_n gl (Some 0) (hyp, hyp_typ) in
  let elimclause'' =
    clenv_fchain_in id elim_flags hypmv elimclause' hypclause in
  let new_hyp_typ  = clenv_type elimclause'' in
  if eq_constr hyp_typ new_hyp_typ then
    errorlabstrm "general_rewrite_in"
      (str "Nothing to rewrite in " ++ pr_id id ++ str".");
  clenv_refine_in with_evars id elimclause'' gl

let general_elim_in with_evars id =
  general_elim_clause (elimination_in_clause_scheme with_evars id)

(* Case analysis tactics *)

let general_case_analysis_in_context with_evars (c,lbindc) gl =
  let (mind,_) = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
  let sort = elimination_sort_of_goal gl in
  let elim =
    if occur_term c (pf_concl gl) then
      pf_apply build_case_analysis_scheme gl mind true sort
    else
      pf_apply build_case_analysis_scheme_default gl mind sort in
  general_elim with_evars (c,lbindc)
    {elimindex = None; elimbody = (elim,NoBindings)} gl

let general_case_analysis with_evars (c,lbindc as cx) =
  match kind_of_term c with
    | Var id when lbindc = NoBindings ->
	tclTHEN (try_intros_until_id_check id)
	  (general_case_analysis_in_context with_evars cx)
    | _ ->
	general_case_analysis_in_context with_evars cx

let simplest_case c = general_case_analysis false (c,NoBindings)

(* Apply a tactic below the products of the conclusion of a lemma *)

type conjunction_status =
  | DefinedRecord of constant option list
  | NotADefinedRecordUseScheme of constr

let make_projection sigma params cstr sign elim i n c =
  let elim = match elim with
  | NotADefinedRecordUseScheme elim ->
      let (na,b,t) = List.nth cstr.cs_args i in
      let b = match b with None -> mkRel (i+1) | Some b -> b in
      let branch = it_mkLambda_or_LetIn b cstr.cs_args in
      if
	(* excludes dependent projection types *)
	noccur_between 1 (n-i-1) t
	(* excludes flexible projection types *)
	&& not (isEvar (fst (whd_betaiota_stack sigma t)))
      then
        let t = lift (i+1-n) t in
	Some (beta_applist (elim,params@[t;branch]),t)
      else
	None
  | DefinedRecord l ->
      match List.nth l i with
      | Some proj ->
	  let t = Typeops.type_of_constant (Global.env()) proj in
	  let args = extended_rel_vect 0 sign in
	  Some (beta_applist (mkConst proj,params),prod_applist t (params@[mkApp (c,args)]))
      | None -> None
  in Option.map (fun (abselim,elimt) -> 
    let c = beta_applist (abselim,[mkApp (c,extended_rel_vect 0 sign)]) in
    (it_mkLambda_or_LetIn c sign, it_mkProd_or_LetIn elimt sign)) elim

let descend_in_conjunctions tac exit c gl =
  try
    let (ind,t) = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
    let sign,ccl = decompose_prod_assum t in
    match match_with_tuple ccl with
    | Some (_,_,isrec) ->
	let n = (mis_constr_nargs ind).(0) in
	let sort = elimination_sort_of_goal gl in
	let id = fresh_id [] (id_of_string "H") gl in
	let IndType (indf,_) = pf_apply find_rectype gl ccl in
	let params = snd (dest_ind_family indf) in
	let cstr = (get_constructors (pf_env gl) indf).(0) in
	let elim =
	  try DefinedRecord (Recordops.lookup_projections ind)
	  with Not_found ->
	    let elim = pf_apply build_case_analysis_scheme gl ind false sort in
	    NotADefinedRecordUseScheme elim in
	tclFIRST
	  (list_tabulate (fun i gl ->
	    match make_projection (project gl) params cstr sign elim i n c with
	    | None -> tclFAIL 0 (mt()) gl
	    | Some (p,pt) ->
	    tclTHENS
	      (internal_cut id pt)
	      [refine_no_check p;
	       tclTHEN (tac (not isrec) (mkVar id)) (thin [id])] gl) n)
	  gl
    | None ->
	raise Exit
  with RefinerError _|UserError _|Exit -> exit ()

(****************************************************)
(*            Resolution tactics                    *)
(****************************************************)

let general_apply with_delta with_destruct with_evars (loc,(c,lbind)) gl0 =
  let flags =
    if with_delta then default_unify_flags else default_no_delta_unify_flags in
  (* The actual type of the theorem. It will be matched against the
  goal. If this fails, then the head constant will be unfolded step by
  step. *)
  let concl_nprod = nb_prod (pf_concl gl0) in
  let rec try_main_apply with_destruct c gl =
    let thm_ty0 = nf_betaiota (project gl) (pf_type_of gl c) in
    let try_apply thm_ty nprod =
      let n = nb_prod thm_ty - nprod in
	if n<0 then error "Applied theorem has not enough premisses.";
	let clause = make_clenv_binding_apply gl (Some n) (c,thm_ty) lbind in
	Clenvtac.res_pf clause ~with_evars:with_evars ~flags:flags gl
    in
      try try_apply thm_ty0 concl_nprod
      with PretypeError _|RefinerError _|UserError _|Failure _ as exn ->
	let rec try_red_apply thm_ty =
	  try
            (* Try to head-reduce the conclusion of the theorem *)
            let red_thm = try_red_product (pf_env gl) (project gl) thm_ty in
              try try_apply red_thm concl_nprod
              with PretypeError _|RefinerError _|UserError _|Failure _ ->
		try_red_apply red_thm
	  with Redelimination ->
            (* Last chance: if the head is a variable, apply may try
	       second order unification *)
	    try if concl_nprod <> 0 then try_apply thm_ty 0 else raise Exit
	    with PretypeError _|RefinerError _|UserError _|Failure _|Exit ->
	      if with_destruct then
                descend_in_conjunctions
                  try_main_apply (fun _ -> Loc.raise loc exn) c gl
	      else
		Loc.raise loc exn
	in try_red_apply thm_ty0
  in
  try_main_apply with_destruct c gl0

let rec apply_with_bindings_gen b e = function
  | [] -> tclIDTAC
  | [cb] -> general_apply b b e cb
  | cb::cbl ->
      tclTHENLAST (general_apply b b e cb) (apply_with_bindings_gen b e cbl)

let apply_with_bindings cb = apply_with_bindings_gen false false [dloc,cb]

let eapply_with_bindings cb = apply_with_bindings_gen false true [dloc,cb]

let apply c = apply_with_bindings_gen false false [dloc,(c,NoBindings)]

let eapply c = apply_with_bindings_gen false true [dloc,(c,NoBindings)]

let apply_list = function
  | c::l -> apply_with_bindings (c,ImplicitBindings l)
  | _ -> assert false

(* [apply_in hyp c] replaces

   hyp : forall y1, ti -> t             hyp : rho(u)
   ========================    with     ============  and the =======
   goal                                 goal                  rho(ti)

   assuming that [c] has type [forall x1..xn -> t' -> u] for some [t]
   unifiable with [t'] with unifier [rho]
*)

let find_matching_clause unifier clause =
  let rec find clause =
    try unifier clause
    with exn when catchable_exception exn ->
    try find (clenv_push_prod clause)
    with NotExtensibleClause -> failwith "Cannot apply"
  in find clause

let progress_with_clause flags innerclause clause =
  let ordered_metas = List.rev (clenv_independent clause) in
  if ordered_metas = [] then error "Statement without assumptions.";
  let f mv =
    find_matching_clause (clenv_fchain mv ~flags clause) innerclause in
  try list_try_find f ordered_metas
  with Failure _ -> error "Unable to unify."

let apply_in_once_main flags innerclause (d,lbind) gl =
  let thm = nf_betaiota gl.sigma (pf_type_of gl d) in
  let rec aux clause =
    try progress_with_clause flags innerclause clause
    with err ->
    try aux (clenv_push_prod clause)
    with NotExtensibleClause -> raise err in
  aux (make_clenv_binding gl (d,thm) lbind)

let apply_in_once sidecond_first with_delta with_destruct with_evars id
  (loc,(d,lbind)) gl0 =
  let flags =
    if with_delta then default_unify_flags else default_no_delta_unify_flags in
  let t' = pf_get_hyp_typ gl0 id in
  let innerclause = mk_clenv_from_n gl0 (Some 0) (mkVar id,t') in
  let rec aux with_destruct c gl =
    try
      let clause = apply_in_once_main flags innerclause (c,lbind) gl in
      clenv_refine_in ~sidecond_first with_evars id clause gl
    with exn when with_destruct ->
      descend_in_conjunctions aux (fun _ -> raise exn) c gl
  in
  aux with_destruct d gl0

(* A useful resolution tactic which, if c:A->B, transforms |- C into
   |- B -> C and |- A

   -------------------
   Gamma |- c : A -> B      Gamma |- ?2 : A
   ----------------------------------------
           Gamma |- B                        Gamma |- ?1 : B -> C
           -----------------------------------------------------
                             Gamma |- ? : C

 Ltac lapply c :=
  let ty := check c in
  match eval hnf in ty with
    ?A -> ?B => cut B; [ idtac | apply c ]
  end.
*)

let cut_and_apply c gl =
  let goal_constr = pf_concl gl in
    match kind_of_term (pf_hnf_constr gl (pf_type_of gl c)) with
      | Prod (_,c1,c2) when not (dependent (mkRel 1) c2) ->
	  tclTHENLAST
	    (apply_type (mkProd (Anonymous,c2,goal_constr)) [mkMeta(new_meta())])
	    (apply_term c [mkMeta (new_meta())]) gl
      | _ -> error "lapply needs a non-dependent product."

(********************************************************************)
(*               Exact tactics                                      *)
(********************************************************************)

let exact_check c gl =
  let concl = (pf_concl gl) in
  let ct = pf_type_of gl c in
  if pf_conv_x_leq gl ct concl then
    refine_no_check c gl
  else
    error "Not an exact proof."

let exact_no_check = refine_no_check

let vm_cast_no_check c gl =
  let concl = pf_concl gl in
  refine_no_check (Term.mkCast(c,Term.VMcast,concl)) gl


let exact_proof c gl =
  (* on experimente la synthese d'ise dans exact *)
  let c = Constrintern.interp_casted_constr (project gl) (pf_env gl) c (pf_concl gl)
  in refine_no_check c gl

let (assumption : tactic) = fun gl ->
  let concl =  pf_concl gl in
  let hyps = pf_hyps gl in
  let rec arec only_eq = function
    | [] ->
        if only_eq then arec false hyps else error "No such assumption."
    | (id,c,t)::rest ->
	if (only_eq & eq_constr t concl)
          or (not only_eq & pf_conv_x_leq gl t concl)
        then refine_no_check (mkVar id) gl
	else arec only_eq rest
  in
  arec true hyps

(*****************************************************************)
(*          Modification of a local context                      *)
(*****************************************************************)

(* This tactic enables the user to remove hypotheses from the signature.
 * Some care is taken to prevent him from removing variables that are
 * subsequently used in other hypotheses or in the conclusion of the
 * goal. *)

let clear ids = (* avant seul dyn_clear n'echouait pas en [] *)
  if ids=[] then tclIDTAC else thin ids

let clear_body = thin_body

let clear_wildcards ids =
  tclMAP (fun (loc,id) gl ->
    try with_check (Tacmach.thin_no_check [id]) gl
    with ClearDependencyError (id,err) ->
      (* Intercept standard [thin] error message *)
      Loc.raise loc
        (error_clear_dependency (pf_env gl) (id_of_string "_") err))
    ids

(*   Takes a list of booleans, and introduces all the variables
 *  quantified in the goal which are associated with a value
 *  true  in the boolean list. *)

let rec intros_clearing = function
  | []          -> tclIDTAC
  | (false::tl) -> tclTHEN intro (intros_clearing tl)
  | (true::tl)  ->
      tclTHENLIST
        [ intro; onLastHypId (fun id -> clear [id]); intros_clearing tl]

(* Modifying/Adding an hypothesis  *)

let specialize mopt (c,lbind) g =
  let term =
    if lbind = NoBindings then c
    else
      let clause = make_clenv_binding g (c,pf_type_of g c) lbind in
      let clause = clenv_unify_meta_types clause in
      let (thd,tstack) = whd_stack clause.evd (clenv_value clause) in
      let nargs = List.length tstack in
      let tstack = match mopt with
	| Some m ->
	    if m < nargs then list_firstn m tstack else tstack
	| None ->
	    let rec chk = function
	      | [] -> []
	      | t::l -> if occur_meta t then [] else t :: chk l
	    in chk tstack
      in
      let term = applist(thd,List.map (nf_evar clause.evd) tstack) in
      if occur_meta term then
	errorlabstrm "" (str "Cannot infer an instance for " ++
          pr_name (meta_name clause.evd (List.hd (collect_metas term))) ++
	  str ".");
      term
  in
  match kind_of_term (fst(decompose_app (snd(decompose_lam_assum c)))) with
       | Var id when List.mem id (pf_ids_of_hyps g) ->
	     tclTHENFIRST
	       (fun g -> internal_cut_replace id (pf_type_of g term) g)
	       (exact_no_check term) g
       | _ -> tclTHENLAST
                 (fun g -> cut (pf_type_of g term) g)
                 (exact_no_check term) g

(* Keeping only a few hypotheses *)

let keep hyps gl =
  let env = Global.env() in
  let ccl = pf_concl gl in
  let cl,_ =
    fold_named_context_reverse (fun (clear,keep) (hyp,_,_ as decl) ->
      if List.mem hyp hyps
	or List.exists (occur_var_in_decl env hyp) keep
	or occur_var env hyp ccl
      then (clear,decl::keep)
      else (hyp::clear,keep))
      ~init:([],[]) (pf_env gl)
  in thin cl gl

(************************)
(* Introduction tactics *)
(************************)

let check_number_of_constructors expctdnumopt i nconstr =
  if i=0 then error "The constructors are numbered starting from 1.";
  begin match expctdnumopt with
    | Some n when n <> nconstr ->
	error ("Not an inductive goal with "^
	       string_of_int n^plural n " constructor"^".")
    | _ -> ()
  end;
  if i > nconstr then error "Not enough constructors."

let constructor_tac with_evars expctdnumopt i lbind gl =
  let cl = pf_concl gl in
  let (mind,redcl) = pf_reduce_to_quantified_ind gl cl in
  let nconstr =
    Array.length (snd (Global.lookup_inductive mind)).mind_consnames in
  check_number_of_constructors expctdnumopt i nconstr;
  let cons = mkConstruct (ith_constructor_of_inductive mind i) in
  let apply_tac = general_apply true false with_evars (dloc,(cons,lbind)) in
  (tclTHENLIST
     [convert_concl_no_check redcl DEFAULTcast; intros; apply_tac]) gl

let one_constructor i lbind = constructor_tac false None i lbind

(* Try to apply the constructor of the inductive definition followed by
   a tactic t given as an argument.
   Should be generalize in Constructor (Fun c : I -> tactic)
 *)

let any_constructor with_evars tacopt gl =
  let t = match tacopt with None -> tclIDTAC | Some t -> t in
  let mind = fst (pf_reduce_to_quantified_ind gl (pf_concl gl)) in
  let nconstr =
    Array.length (snd (Global.lookup_inductive mind)).mind_consnames in
  if nconstr = 0 then error "The type has no constructors.";
  tclFIRST
    (List.map
      (fun i -> tclTHEN (constructor_tac with_evars None i NoBindings) t)
      (interval 1 nconstr)) gl

let left_with_bindings  with_evars = constructor_tac with_evars (Some 2) 1
let right_with_bindings with_evars = constructor_tac with_evars (Some 2) 2
let split_with_bindings with_evars l =
  tclMAP (constructor_tac with_evars (Some 1) 1) l

let left           = left_with_bindings false
let simplest_left  = left NoBindings

let right          = right_with_bindings false
let simplest_right = right NoBindings

let split          = constructor_tac false (Some 1) 1
let simplest_split = split NoBindings

(*****************************)
(* Decomposing introductions *)
(*****************************)

let forward_general_multi_rewrite =
  ref (fun _ -> failwith "general_multi_rewrite undefined")

let register_general_multi_rewrite f =
  forward_general_multi_rewrite := f

let error_unexpected_extra_pattern loc nb pat =
  let s1,s2,s3 = match pat with
  | IntroIdentifier _ -> "name", (plural nb " introduction pattern"), "no"
  | _ -> "introduction pattern", "", "none" in
  user_err_loc (loc,"",str "Unexpected " ++ str s1 ++ str " (" ++
    (if nb = 0 then (str s3 ++ str s2) else
      (str "at most " ++ int nb ++ str s2)) ++ spc () ++
       str (if nb = 1 then "was" else "were") ++
      strbrk " expected in the branch).")

let intro_or_and_pattern loc b ll l' tac id gl =
    let c = mkVar id in
    let ind,_ = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
    let nv = mis_constr_nargs ind in
    let bracketed = b or not (l'=[]) in
    let rec adjust_names_length nb n = function
      | [] when n = 0 or not bracketed -> []
      | [] -> (dloc,IntroAnonymous) :: adjust_names_length nb (n-1) []
      | (loc',pat) :: _ as l when n = 0 ->
	  if bracketed then error_unexpected_extra_pattern loc' nb pat;
	  l
      | ip :: l -> ip :: adjust_names_length nb (n-1) l in
    let ll = fix_empty_or_and_pattern (Array.length nv) ll in
    check_or_and_pattern_size loc ll (Array.length nv);
    tclTHENLASTn
      (tclTHEN (simplest_case c) (clear [id]))
      (array_map2 (fun n l -> tac ((adjust_names_length n n l)@l'))
	nv (Array.of_list ll))
      gl

let rewrite_hyp l2r id gl =
  let rew_on l2r =
    !forward_general_multi_rewrite l2r false (mkVar id,NoBindings) in
  let clear_var_and_eq c =
    tclTRY (tclTHEN (clear [id]) (tclTRY (clear [destVar c]))) in
  let t = pf_whd_betadeltaiota gl (pf_type_of gl (mkVar id)) in
  (* TODO: detect setoid equality? better detect the different equalities *)
  match match_with_equality_type t with
  | Some (hdcncl,[_;lhs;rhs]) ->
      if l2r & isVar lhs & not (occur_var (pf_env gl) (destVar lhs) rhs) then
	tclTHEN (rew_on l2r allHypsAndConcl) (clear_var_and_eq lhs) gl
      else if not l2r & isVar rhs & not (occur_var (pf_env gl) (destVar rhs) lhs) then
	tclTHEN (rew_on l2r allHypsAndConcl) (clear_var_and_eq rhs) gl
      else
	tclTHEN (rew_on l2r onConcl) (tclTRY (clear [id])) gl
  | Some (hdcncl,[c]) ->
      let l2r = not l2r in (* equality of the form eq_true *)
      if isVar c then
	tclTHEN (rew_on l2r allHypsAndConcl) (clear_var_and_eq c) gl
      else
	tclTHEN (rew_on l2r onConcl) (tclTRY (clear [id])) gl
  | _ ->
      error "Cannot find a known equation."

let rec explicit_intro_names = function
| (_, IntroIdentifier id) :: l ->
    id :: explicit_intro_names l
| (_, (IntroWildcard | IntroAnonymous | IntroFresh _
      | IntroRewrite _ | IntroForthcoming _)) :: l -> explicit_intro_names l
| (_, IntroOrAndPattern ll) :: l' ->
    List.flatten (List.map (fun l -> explicit_intro_names (l@l')) ll)
| [] ->
    []

  (* We delay thinning until the completion of the whole intros tactic
     to ensure that dependent hypotheses are cleared in the right
     dependency order (see bug #1000); we use fresh names, not used in
     the tactic, for the hyps to clear *)
let rec intros_patterns b avoid thin destopt = function
  | (loc, IntroWildcard) :: l ->
      tclTHEN
        (intro_gen loc (IntroAvoid(avoid@explicit_intro_names l))
	  no_move true false)
        (onLastHypId (fun id ->
	  tclORELSE
	    (tclTHEN (clear [id]) (intros_patterns b avoid thin destopt l))
	    (intros_patterns b avoid ((loc,id)::thin) destopt l)))
  | (loc, IntroIdentifier id) :: l ->
      tclTHEN
        (intro_gen loc (IntroMustBe id) destopt true false)
        (intros_patterns b avoid thin destopt l)
  | (loc, IntroAnonymous) :: l ->
      tclTHEN
        (intro_gen loc (IntroAvoid (avoid@explicit_intro_names l))
	  destopt true false)
        (intros_patterns b avoid thin destopt l)
  | (loc, IntroFresh id) :: l ->
      tclTHEN
        (intro_gen loc (IntroBasedOn (id, avoid@explicit_intro_names l))
	  destopt true false)
        (intros_patterns b avoid thin destopt l)
  | (loc, IntroForthcoming onlydeps) :: l ->
      tclTHEN
        (intro_forthcoming_gen loc (IntroAvoid (avoid@explicit_intro_names l))
	  destopt onlydeps)
        (intros_patterns b avoid thin destopt l)
  | (loc, IntroOrAndPattern ll) :: l' ->
      tclTHEN
        introf
        (onLastHypId
	  (intro_or_and_pattern loc b ll l'
	    (intros_patterns b avoid thin destopt)))
  | (loc, IntroRewrite l2r) :: l ->
      tclTHEN
        (intro_gen loc (IntroAvoid(avoid@explicit_intro_names l))
	  no_move true false)
        (onLastHypId (fun id ->
	  tclTHENLAST (* Skip the side conditions of the rewriting step *)
	    (rewrite_hyp l2r id)
	    (intros_patterns b avoid thin destopt l)))
  | [] -> clear_wildcards thin

let intros_pattern = intros_patterns false [] []

let intro_pattern destopt pat = intros_patterns false [] [] destopt [dloc,pat]

let intro_patterns = function
  | [] -> tclREPEAT intro
  | l  -> intros_pattern no_move l

(**************************)
(*   Other cut tactics    *)
(**************************)

let make_id s = fresh_id [] (default_id_of_sort s)

let prepare_intros s ipat gl = match ipat with
  | None -> make_id s gl, tclIDTAC
  | Some (loc,ipat) -> match ipat with
  | IntroIdentifier id -> id, tclIDTAC
  | IntroAnonymous -> make_id s gl, tclIDTAC
  | IntroFresh id -> fresh_id [] id gl, tclIDTAC
  | IntroWildcard -> let id = make_id s gl in id, clear_wildcards [dloc,id]
  | IntroRewrite l2r ->
      let id = make_id s gl in
      id, !forward_general_multi_rewrite l2r false (mkVar id,NoBindings) allHypsAndConcl
  | IntroOrAndPattern ll -> make_id s gl,
      onLastHypId
	(intro_or_and_pattern loc true ll []
	  (intros_patterns true [] [] no_move))
  | IntroForthcoming _ -> user_err_loc
      (loc,"",str "Introduction pattern for one hypothesis expected")

let ipat_of_name = function
  | Anonymous -> None
  | Name id -> Some (dloc, IntroIdentifier id)

let allow_replace c gl = function (* A rather arbitrary condition... *)
  | Some (_, IntroIdentifier id) ->
      fst (decompose_app ((strip_lam_assum c))) = mkVar id
  | _ ->
      false

let assert_as first ipat c gl =
  match kind_of_term (pf_hnf_type_of gl c) with
  | Sort s ->
      let id,tac = prepare_intros s ipat gl in
      let repl = allow_replace c gl ipat in
      tclTHENS
	((if first then internal_cut_gen else internal_cut_rev_gen) repl id c)
	(if first then [tclIDTAC; tac] else [tac; tclIDTAC]) gl
  | _  -> error "Not a proposition or a type."

let assert_tac na = assert_as true (ipat_of_name na)

(* apply in as *)

let as_tac id ipat = match ipat with
  | Some (loc,IntroRewrite l2r) ->
      !forward_general_multi_rewrite l2r false (mkVar id,NoBindings) allHypsAndConcl
  | Some (loc,IntroOrAndPattern ll) ->
      intro_or_and_pattern loc true ll [] (intros_patterns true [] [] no_move)
        id
  | Some (loc,
      (IntroIdentifier _ | IntroAnonymous | IntroFresh _ |
       IntroWildcard | IntroForthcoming _)) ->
      user_err_loc (loc,"", str "Disjunctive/conjunctive pattern expected")
  | None -> tclIDTAC

let tclMAPLAST tacfun l =
  List.fold_right (fun x -> tclTHENLAST (tacfun x)) l tclIDTAC

let tclMAPFIRST tacfun l =
  List.fold_right (fun x -> tclTHENFIRST (tacfun x)) l tclIDTAC

let general_apply_in sidecond_first with_delta with_destruct with_evars 
    id lemmas ipat =
  if sidecond_first then
    (* Skip the side conditions of the applied lemma *)
    tclTHENLAST
      (tclMAPLAST
	(apply_in_once sidecond_first with_delta with_destruct with_evars id) 
	lemmas)
      (as_tac id ipat)
  else 
    tclTHENFIRST
      (tclMAPFIRST
	(apply_in_once sidecond_first with_delta with_destruct with_evars id) 
	lemmas)
      (as_tac id ipat)

let apply_in simple with_evars id lemmas ipat =
  general_apply_in false simple simple with_evars id lemmas ipat

let simple_apply_in id c =
  general_apply_in false false false false id [dloc,(c,NoBindings)] None

(**************************)
(*   Generalize tactics   *)
(**************************)

let generalized_name c t ids cl = function
  | Name id as na ->
      if List.mem id ids then
	errorlabstrm "" (pr_id id ++ str " is already used");
      na
  | Anonymous ->
      match kind_of_term c with
      | Var id ->
	 (* Keep the name even if not occurring: may be used by intros later *)
	  Name id
      | _ ->
	  if noccurn 1 cl then Anonymous else
	    (* On ne s'etait pas casse la tete : on avait pris pour nom de
               variable la premiere lettre du type, meme si "c" avait ete une
               constante dont on aurait pu prendre directement le nom *)
	    named_hd (Global.env()) t Anonymous

let generalize_goal gl i ((occs,c,b),na) cl =
  let t = pf_type_of gl c in
  let decls,cl = decompose_prod_n_assum i cl in
  let dummy_prod = it_mkProd_or_LetIn mkProp decls in
  let newdecls,_ = decompose_prod_n_assum i (subst_term c dummy_prod) in
  let cl' = subst_term_occ occs c (it_mkProd_or_LetIn cl newdecls) in
  let na = generalized_name c t (pf_ids_of_hyps gl) cl' na in
    mkProd_or_LetIn (na,b,t) cl'

let generalize_dep ?(with_let=false) c gl =
  let env = pf_env gl in
  let sign = pf_hyps gl in
  let init_ids = ids_of_named_context (Global.named_context()) in
  let rec seek d toquant =
    if List.exists (fun (id,_,_) -> occur_var_in_decl env id d) toquant
      or dependent_in_decl c d then
      d::toquant
    else
      toquant in
  let to_quantify = Sign.fold_named_context seek sign ~init:[] in
  let to_quantify_rev = List.rev to_quantify in
  let qhyps = List.map (fun (id,_,_) -> id) to_quantify_rev in
  let tothin = List.filter (fun id -> not (List.mem id init_ids)) qhyps in
  let tothin' =
    match kind_of_term c with
      | Var id when mem_named_context id sign & not (List.mem id init_ids)
	  -> id::tothin
      | _ -> tothin
  in
  let cl' = it_mkNamedProd_or_LetIn (pf_concl gl) to_quantify in
  let body = 
    if with_let then
      match kind_of_term c with 
      | Var id -> pi2 (pf_get_hyp gl id)
      | _ -> None
    else None
  in
  let cl'' = generalize_goal gl 0 ((all_occurrences,c,body),Anonymous) cl' in
  let args = Array.to_list (instance_from_named_context to_quantify_rev) in
  tclTHEN
    (apply_type cl'' (if body = None then c::args else args))
    (thin (List.rev tothin'))
    gl

let generalize_gen_let lconstr gl =
  let newcl =
    list_fold_right_i (generalize_goal gl) 0 lconstr (pf_concl gl) in
  apply_type newcl (list_map_filter (fun ((_,c,b),_) -> 
    if b = None then Some c else None) lconstr) gl

let generalize_gen lconstr =
  generalize_gen_let (List.map (fun ((occs,c),na) ->
    (occs,c,None),na) lconstr)
    
let generalize l =
  generalize_gen_let (List.map (fun c -> ((all_occurrences,c,None),Anonymous)) l)

let pf_get_hyp_val gl id =
  let (_, b, _) = pf_get_hyp gl id in
    b

let revert hyps gl = 
  let lconstr = List.map (fun id -> 
    ((all_occurrences, mkVar id, pf_get_hyp_val gl id), Anonymous)) 
    hyps 
  in tclTHEN (generalize_gen_let lconstr) (clear hyps) gl

(* Faudra-t-il une version avec plusieurs args de generalize_dep ?
Cela peut-être troublant de faire "Generalize Dependent H n" dans
"n:nat; H:n=n |- P(n)" et d'échouer parce que H a disparu après la
généralisation dépendante par n.

let quantify lconstr =
 List.fold_right
   (fun com tac -> tclTHEN tac (tactic_com generalize_dep c))
   lconstr
   tclIDTAC
*)

(* A dependent cut rule à la sequent calculus
   ------------------------------------------
   Sera simplifiable le jour où il y aura un let in primitif dans constr

   [letin_tac b na c (occ_hyp,occ_ccl) gl] transforms
   [...x1:T1(c),...,x2:T2(c),... |- G(c)] into
   [...x:T;Heqx:(x=c);x1:T1(x),...,x2:T2(x),... |- G(x)] if [b] is false or
   [...x:=c:T;x1:T1(x),...,x2:T2(x),... |- G(x)] if [b] is true

   [occ_hyp,occ_ccl] tells which occurrences of [c] have to be substituted;
   if [occ_hyp = []] and [occ_ccl = None] then [c] is substituted
   wherever it occurs, otherwise [c] is substituted only in hyps
   present in [occ_hyps] at the specified occurrences (everywhere if
   the list of occurrences is empty), and in the goal at the specified
   occurrences if [occ_goal] is not [None];

   if name = Anonymous, the name is build from the first letter of the type;

   The tactic first quantify the goal over x1, x2,... then substitute then
   re-intro x1, x2,... at their initial place ([marks] is internally
   used to remember the place of x1, x2, ...: it is the list of hypotheses on
   the left of each x1, ...).
*)

let out_arg = function
  | ArgVar _ -> anomaly "Unevaluated or_var variable"
  | ArgArg x -> x

let occurrences_of_hyp id cls =
  let rec hyp_occ = function
      [] -> None
    | (((b,occs),id'),hl)::_ when id=id' -> Some ((b,List.map out_arg occs),hl)
    | _::l -> hyp_occ l in
  match cls.onhyps with
      None -> Some (all_occurrences,InHyp)
    | Some l -> hyp_occ l

let occurrences_of_goal cls =
  if cls.concl_occs = no_occurrences_expr then None
  else Some (on_snd (List.map out_arg) cls.concl_occs)

let in_every_hyp cls = (cls.onhyps=None)

(*
(* Implementation with generalisation then re-intro: introduces noise *)
(* in proofs *)

let letin_abstract id c occs gl =
  let env = pf_env gl in
  let compute_dependency _ (hyp,_,_ as d) ctxt =
    let d' =
      try
	match occurrences_of_hyp hyp occs with
	  | None -> raise Not_found
	  | Some occ ->
              let newdecl = subst_term_occ_decl occ c d in
              if occ = [] & d = newdecl then
		if not (in_every_hyp occs)
		then raise (RefinerError (DoesNotOccurIn (c,hyp)))
		else raise Not_found
              else
		(subst1_named_decl (mkVar id) newdecl, true)
	with Not_found ->
	  (d,List.exists
	      (fun ((id,_,_),dep) -> dep && occur_var_in_decl env id d) ctxt)
    in d'::ctxt
  in
  let ctxt' = fold_named_context compute_dependency env ~init:[] in
  let compute_marks ((depdecls,marks as accu),lhyp) ((hyp,_,_) as d,b) =
    if b then ((d::depdecls,(hyp,lhyp)::marks), lhyp)
    else (accu, Some hyp) in
  let (depdecls,marks),_ = List.fold_left compute_marks (([],[]),None) ctxt' in
  let ccl = match occurrences_of_goal occs with
    | None -> pf_concl gl
    | Some occ -> subst1 (mkVar id) (subst_term_occ occ c (pf_concl gl))
  in
  (depdecls,marks,ccl)

let letin_tac with_eq name c occs gl =
  let x = id_of_name_using_hdchar (Global.env()) (pf_type_of gl c) name in
  let id =
    if name = Anonymous then fresh_id [] x gl else
      if not (mem_named_context x (pf_hyps gl)) then x else
	error ("The variable "^(string_of_id x)^" is already declared") in
  let (depdecls,marks,ccl)= letin_abstract id c occs gl in
  let t = pf_type_of gl c in
  let tmpcl = List.fold_right mkNamedProd_or_LetIn depdecls ccl in
  let args = Array.to_list (instance_from_named_context depdecls) in
  let newcl = mkNamedLetIn id c t tmpcl in
  let lastlhyp = if marks=[] then None else snd (List.hd marks) in
  tclTHENLIST
    [ apply_type newcl args;
      thin (List.map (fun (id,_,_) -> id) depdecls);
      intro_gen (IntroMustBe id) lastlhyp false;
      if with_eq then tclIDTAC else thin_body [id];
      intros_move marks ] gl
*)

(* Implementation without generalisation: abbrev will be lost in hyps in *)
(* in the extracted proof *)

let letin_abstract id c (occs,check_occs) gl =
  let env = pf_env gl in
  let compute_dependency _ (hyp,_,_ as d) depdecls =
    match occurrences_of_hyp hyp occs with
      | None -> depdecls
      | Some occ ->
          let newdecl = subst_term_occ_decl occ c d in
          if occ = (all_occurrences,InHyp) & d = newdecl then
	    if check_occs & not (in_every_hyp occs)
	    then raise (RefinerError (DoesNotOccurIn (c,hyp)))
	    else depdecls
          else
	    (subst1_named_decl (mkVar id) newdecl)::depdecls in
  let depdecls = fold_named_context compute_dependency env ~init:[] in
  let ccl = match occurrences_of_goal occs with
    | None -> pf_concl gl
    | Some occ -> subst1 (mkVar id) (subst_term_occ occ c (pf_concl gl)) in
  let lastlhyp =
    if depdecls = [] then no_move else MoveAfter(pi1(list_last depdecls)) in
  (depdecls,lastlhyp,ccl)

let letin_tac_gen with_eq name c ty occs gl =
  let id =
    let x = id_of_name_using_hdchar (Global.env()) (pf_type_of gl c) name in
    if name = Anonymous then fresh_id [] x gl else
      if not (mem_named_context x (pf_hyps gl)) then x else
	error ("The variable "^(string_of_id x)^" is already declared.") in
  let (depdecls,lastlhyp,ccl)= letin_abstract id c occs gl in
  let t = match ty with Some t -> t | None -> pf_type_of gl c in
  let newcl,eq_tac = match with_eq with
    | Some (lr,(loc,ido)) ->
      let heq = match ido with
        | IntroAnonymous -> fresh_id [id] (add_prefix "Heq" id) gl
	| IntroFresh heq_base -> fresh_id [id] heq_base gl
        | IntroIdentifier id -> id
	| _ -> error"Expect an introduction pattern naming one hypothesis." in
      let eqdata = build_coq_eq_data () in
      let args = if lr then [t;mkVar id;c] else [t;c;mkVar id]in
      let eq = applist (eqdata.eq,args) in
      let refl = applist (eqdata.refl, [t;mkVar id]) in
      mkNamedLetIn id c t (mkLetIn (Name heq, refl, eq, ccl)),
      tclTHEN
	(intro_gen loc (IntroMustBe heq) lastlhyp true false)
	(thin_body [heq;id])
    | None ->
	mkNamedLetIn id c t ccl, tclIDTAC in
  tclTHENLIST
    [ convert_concl_no_check newcl DEFAULTcast;
      intro_gen dloc (IntroMustBe id) lastlhyp true false;
      eq_tac;
      tclMAP convert_hyp_no_check depdecls ] gl

let letin_tac with_eq name c ty occs =
  letin_tac_gen with_eq name c ty (occs,true)

(* Tactics "pose proof" (usetac=None) and "assert" (otherwise) *)
let forward usetac ipat c gl =
  match usetac with
  | None ->
      let t = pf_type_of gl c in
      tclTHENFIRST (assert_as true ipat t) (exact_no_check c) gl
  | Some tac ->
      tclTHENFIRST (assert_as true ipat c) tac gl

let pose_proof na c = forward None (ipat_of_name na) c
let assert_by na t tac = forward (Some tac) (ipat_of_name na) t

(*****************************)
(* Ad hoc unfold             *)
(*****************************)

(* The two following functions should already exist, but found nowhere *)
(* Unfolds x by its definition everywhere *)
let unfold_body x gl =
  let hyps = pf_hyps gl in
  let xval =
    match Sign.lookup_named x hyps with
        (_,Some xval,_) -> xval
      | _ -> errorlabstrm "unfold_body"
          (pr_id x ++ str" is not a defined hypothesis.") in
  let aft = afterHyp x gl in
  let hl = List.fold_right (fun (y,yval,_) cl -> (y,InHyp) :: cl) aft [] in
  let xvar = mkVar x in
  let rfun _ _ c = replace_term xvar xval c in
  tclTHENLIST
    [tclMAP (fun h -> reduct_in_hyp rfun h) hl;
     reduct_in_concl (rfun,DEFAULTcast)] gl

(* Unfolds x by its definition everywhere and clear x. This may raise
   an error if x is not defined. *)
let unfold_all x gl =
  let (_,xval,_) = pf_get_hyp gl x in
  (* If x has a body, simply replace x with body and clear x *)
  if xval <> None then tclTHEN (unfold_body x) (clear [x]) gl
  else tclIDTAC gl

(*****************************)
(* High-level induction      *)
(*****************************)

(*
 * A "natural" induction tactic
 *
  - [H0:T0, ..., Hi:Ti, hyp0:P->I(args), Hi+1:Ti+1, ..., Hn:Tn |-G] is the goal
  - [hyp0] is the induction hypothesis
  - we extract from [args] the variables which are not rigid parameters
    of the inductive type, this is [indvars] (other terms are forgotten);
    [indhyps] are the ones which actually are declared in context
    (done in [find_atomic_param_of_ind])
  - we look for all hyps depending of [hyp0] or one of [indvars]:
    this is [dephyps] of types [deptyps] respectively
  - [statuslist] tells for each hyps in [dephyps] after which other hyp
    fixed in the context they must be moved (when induction is done)
  - [hyp0succ] is the name of the hyp fixed in the context after which to
    move the subterms of [hyp0succ] in the i-th branch where it is supposed
    to be the i-th constructor of the inductive type.

  Strategy: (cf in [induction_from_context])
  - requantify and clear all [dephyps]
  - apply induction on [hyp0]
  - clear [indhyps] and [hyp0]
  - in the i-th subgoal, intro the arguments of the i-th constructor
    of the inductive type after [hyp0succ] (done in
    [induct_discharge]) let the induction hypotheses on top of the
    hyps because they may depend on variables between [hyp0] and the
    top. A counterpart is that the dep hyps programmed to be intro-ed
    on top must now be intro-ed after the induction hypotheses
  - move each of [dephyps] at the right place following the
    [statuslist]

 *)

let check_unused_names names =
  if names <> [] & Flags.is_verbose () then
    msg_warning
      (str"Unused introduction " ++ str (plural (List.length names) "pattern")
       ++ str": " ++ prlist_with_sep spc pr_intro_pattern names)

let rec first_name_buggy avoid gl (loc,pat) = match pat with
  | IntroOrAndPattern [] -> no_move
  | IntroOrAndPattern ([]::l) ->
      first_name_buggy avoid gl (loc,IntroOrAndPattern l)
  | IntroOrAndPattern ((p::_)::_) -> first_name_buggy avoid gl p
  | IntroWildcard -> no_move
  | IntroRewrite _ -> no_move
  | IntroIdentifier id -> MoveAfter id
  | IntroAnonymous | IntroFresh _ | IntroForthcoming _ -> (* buggy *) no_move

let rec consume_pattern avoid id isdep gl = function
  | [] -> ((dloc, IntroIdentifier (fresh_id avoid id gl)), [])
  | (loc,IntroAnonymous)::names ->
      let avoid = avoid@explicit_intro_names names in
      ((loc,IntroIdentifier (fresh_id avoid id gl)), names)
  | (loc,IntroForthcoming true)::names when not isdep ->
      consume_pattern avoid id isdep gl names
  | (loc,IntroForthcoming _)::names as fullpat ->
      let avoid = avoid@explicit_intro_names names in
      ((loc,IntroIdentifier (fresh_id avoid id gl)), fullpat)
  | (loc,IntroFresh id')::names ->
      let avoid = avoid@explicit_intro_names names in
      ((loc,IntroIdentifier (fresh_id avoid id' gl)), names)
  | pat::names -> (pat,names)

let re_intro_dependent_hypotheses (lstatus,rstatus) tophyp =
  let newlstatus = (* if some IH has taken place at the top of hyps *)
    List.map (function (hyp,MoveToEnd true) -> (hyp,tophyp) | x -> x) lstatus
  in
  tclTHEN
    (intros_move rstatus)
    (intros_move newlstatus)

let update destopt tophyp = if destopt = no_move then tophyp else destopt

let safe_dest_intros_patterns avoid dest pat gl =
  try intros_patterns true avoid [] dest pat gl
  with UserError ("move_hyp",_) ->
    (* May happen if the lemma has dependent arguments that has resolved
       only after cook_sign is called, e.g. as in 
       "dec:forall x, {x=0}+{x<>0};  a:A  |- if dec a then True else False"
       for argument a of dec which will be found only lately *)
    intros_patterns true avoid [] no_move pat gl

type elim_arg_kind = RecArg | IndArg | OtherArg

let induct_discharge destopt avoid' tac (avoid,ra) names gl =
  let avoid = avoid @ avoid' in
  let rec peel_tac ra names tophyp gl =
    match ra with
    | (RecArg,deprec,recvarname) ::
        (IndArg,depind,hyprecname) :: ra' ->
        let recpat,names = match names with
          | [loc,IntroIdentifier id as pat] ->
              let id' = next_ident_away (add_prefix "IH" id) avoid in
	      (pat, [dloc, IntroIdentifier id'])
          | _ -> consume_pattern avoid recvarname deprec gl names in
        let hyprec,names = consume_pattern avoid hyprecname depind gl names in
        (* IH stays at top: we need to update tophyp *)
        (* This is buggy for intro-or-patterns with different first hypnames *)
        (* Would need to pass peel_tac as a continuation of intros_patterns *)
        (* (or to have hypotheses classified by blocks...) *)
        let newtophyp =
	  if tophyp=no_move then first_name_buggy avoid gl hyprec else tophyp
	in
        tclTHENLIST
	  [ safe_dest_intros_patterns avoid (update destopt tophyp) [recpat];
	    safe_dest_intros_patterns avoid no_move [hyprec];
	    peel_tac ra' names newtophyp] gl
    | (IndArg,dep,hyprecname) :: ra' ->
	(* Rem: does not happen in Coq schemes, only in user-defined schemes *)
        let pat,names = consume_pattern avoid hyprecname dep gl names in
	tclTHEN (safe_dest_intros_patterns avoid (update destopt tophyp) [pat])
          (peel_tac ra' names tophyp) gl
    | (RecArg,dep,recvarname) :: ra' ->
        let pat,names = consume_pattern avoid recvarname dep gl names in
	tclTHEN (safe_dest_intros_patterns avoid (update destopt tophyp) [pat])
          (peel_tac ra' names tophyp) gl
    | (OtherArg,_,_) :: ra' ->
        let pat,names = match names with
          | [] -> (dloc, IntroAnonymous), []
          | pat::names -> pat,names in
	tclTHEN (safe_dest_intros_patterns avoid (update destopt tophyp) [pat])
          (peel_tac ra' names tophyp) gl
    | [] ->
        check_unused_names names;
        tac tophyp gl
  in
  peel_tac ra names no_move gl

(* - le recalcul de indtyp à chaque itération de atomize_one est pour ne pas
     s'embêter à regarder si un letin_tac ne fait pas des
     substitutions aussi sur l'argument voisin *)

(* Marche pas... faut prendre en compte l'occurrence précise... *)

let atomize_param_of_ind (indref,nparams,_) hyp0 gl =
  let tmptyp0 = pf_get_hyp_typ gl hyp0 in
  let typ0 = pf_apply reduce_to_quantified_ref gl indref tmptyp0 in
  let prods, indtyp = decompose_prod typ0 in
  let argl = snd (decompose_app indtyp) in
  let params = list_firstn nparams argl in
  (* le gl est important pour ne pas préévaluer *)
  let rec atomize_one i avoid gl =
    if i<>nparams then
      let tmptyp0 = pf_get_hyp_typ gl hyp0 in
      (* If argl <> [], we expect typ0 not to be quantified, in order to
         avoid bound parameters... then we call pf_reduce_to_atomic_ind *)
      let indtyp = pf_apply reduce_to_atomic_ref gl indref tmptyp0 in
      let argl = snd (decompose_app indtyp) in
      let c = List.nth argl (i-1) in
      match kind_of_term c with
	| Var id when not (List.exists (occur_var (pf_env gl) id) avoid) ->
	    atomize_one (i-1) ((mkVar id)::avoid) gl
	| Var id ->
	    let x = fresh_id [] id gl in
	    tclTHEN
	      (letin_tac None (Name x) (mkVar id) None allHypsAndConcl)
	      (atomize_one (i-1) ((mkVar x)::avoid)) gl
	| _ ->
	    let id = id_of_name_using_hdchar (Global.env()) (pf_type_of gl c)
		       Anonymous in
	    let x = fresh_id [] id gl in
	    tclTHEN
	      (letin_tac None (Name x) c None allHypsAndConcl)
	      (atomize_one (i-1) ((mkVar x)::avoid)) gl
    else
      tclIDTAC gl
  in
  atomize_one (List.length argl) params gl

let find_atomic_param_of_ind nparams indtyp =
  let argl = snd (decompose_app indtyp) in
  let argv = Array.of_list argl in
  let params = list_firstn nparams argl in
  let indvars = ref Idset.empty in
  for i = nparams to (Array.length argv)-1 do
    match kind_of_term argv.(i) with
      | Var id
          when not (List.exists (occur_var (Global.env()) id) params) ->
	  indvars := Idset.add id !indvars
      | _ -> ()
  done;
  Idset.elements !indvars;


(* [cook_sign] builds the lists [indhyps] of hyps that must be
   erased, the lists of hyps to be generalize [(hdeps,tdeps)] on the
   goal together with the places [(lstatus,rstatus)] where to re-intro
   them after induction. To know where to re-intro the dep hyp, we
   remember the name of the hypothesis [lhyp] after which (if the dep
   hyp is more recent than [hyp0]) or [rhyp] before which (if older
   than [hyp0]) its equivalent must be moved when the induction has
   been applied. Since computation of dependencies and [rhyp] is from
   more ancient (on the right) to more recent hyp (on the left) but
   the computation of [lhyp] progresses from the other way, [cook_hyp]
   is in two passes (an alternative would have been to write an
   higher-order algorithm). We use references to reduce
   the accumulation of arguments.

   To summarize, the situation looks like this

   Goal(n,x) -| H6:(Q n); x:A; H5:True; H4:(le O n); H3:(P n); H2:True; n:nat
                Left                                                    Right

   Induction hypothesis is H4 ([hyp0])
   Variable parameters of (le O n) is the singleton list with "n" ([indvars])
   Part of [indvars] really in context is the same ([indhyps])
   The dependent hyps are H3 and H6 ([dephyps])
   For H3 the memorized places are H5 ([lhyp]) and H2 ([rhyp])
    because these names are among the hyp which are fixed through the induction
   For H6 the neighbours are None ([lhyp]) and H5 ([rhyp])
   For H3, because on the right of H4, we remember rhyp (here H2)
   For H6, because on the left of H4, we remember lhyp (here None)
   For H4, we remember lhyp (here H5)

   The right neighbour is then translated into the left neighbour
   because move_hyp tactic needs the name of the hyp _after_ which we
   move the hyp to move.

   But, say in the 2nd subgoal of the hypotheses, the goal will be

   (m:nat)((P m)->(Q m)->(Goal m)) -> (P Sm)->   (Q Sm)->   (Goal Sm)
     ^^^^^^^^^^^^^^^^^^^^^^^^^^^       ^^^^
         both go where H4 was       goes where  goes where
                                      H3 was      H6 was

   We have to intro and move m and the recursive hyp first, but then
   where to move H3 ??? Only the hyp on its right is relevant, but we
   have to translate it into the name of the hyp on the left

   Note: this case where some hyp(s) in [dephyps] has(have) the same
   left neighbour as [hyp0] is the only problematic case with right
   neighbours. For the other cases (e.g. an hyp H1:(R n) between n and H2
   would have posed no problem. But for uniformity, we decided to use
   the right hyp for all hyps on the right of H4.

   Others solutions are welcome

   PC 9 fev 06: Adapted to accept multi argument principle with no
   main arg hyp. hyp0 is now optional, meaning that it is possible
   that there is no main induction hypotheses. In this case, we
   consider the last "parameter" (in [indvars]) as the limit between
   "left" and "right", BUT it must be included in indhyps.

   Other solutions are still welcome

*)

exception Shunt of identifier move_location

let cook_sign hyp0_opt indvars env =
  let hyp0,inhyps =
  match hyp0_opt with
  | None -> List.hd (List.rev indvars), []
  | Some (hyp0,at_least_in_hyps) -> hyp0, at_least_in_hyps in
  (* First phase from L to R: get [indhyps], [decldep] and [statuslist]
     for the hypotheses before (= more ancient than) hyp0 (see above) *)
  let allindhyps = hyp0::indvars in
  let indhyps = ref [] in
  let decldeps = ref [] in
  let ldeps = ref [] in
  let rstatus = ref [] in
  let lstatus = ref [] in
  let before = ref true in
  let seek_deps env (hyp,_,_ as decl) rhyp =
    if hyp = hyp0 then begin
      before:=false;
      (* If there was no main induction hypotheses, then hyp is one of
         indvars too, so add it to indhyps. *)
      (if hyp0_opt=None then indhyps := hyp::!indhyps);
      MoveToEnd false (* fake value *)
    end else if List.mem hyp indvars then begin
      (* warning: hyp can still occur after induction *)
      (* e.g. if the goal (t hyp hyp0) with other occs of hyp in t *)
      indhyps := hyp::!indhyps;
      rhyp
    end else
      if inhyps <> [] && List.mem hyp inhyps || inhyps = [] &&
	(List.exists (fun id -> occur_var_in_decl env id decl) allindhyps ||
         List.exists (fun (id,_,_) -> occur_var_in_decl env id decl) !decldeps)
      then begin
	decldeps := decl::!decldeps;
	if !before then
	  rstatus := (hyp,rhyp)::!rstatus
	else
	  ldeps := hyp::!ldeps; (* status computed in 2nd phase *)
	MoveBefore hyp end
      else
	MoveBefore hyp
  in
  let _ = fold_named_context seek_deps env ~init:(MoveToEnd false) in
  (* 2nd phase from R to L: get left hyp of [hyp0] and [lhyps] *)
  let compute_lstatus lhyp (hyp,_,_) =
    if hyp = hyp0 then raise (Shunt lhyp);
    if List.mem hyp !ldeps then begin
      lstatus := (hyp,lhyp)::!lstatus;
      lhyp
    end else
      if List.mem hyp !indhyps then lhyp else MoveAfter hyp
  in
  try
    let _ =
      fold_named_context_reverse compute_lstatus ~init:(MoveToEnd true) env in
    raise (Shunt (MoveToEnd true)) (* ?? FIXME *)
  with Shunt lhyp0 ->
    let statuslists = (!lstatus,List.rev !rstatus) in
    (statuslists, (if hyp0_opt=None then MoveToEnd true else lhyp0),
     !indhyps, !decldeps)


(*
   The general form of an induction principle is the following:

   forall prm1 prm2 ... prmp,                          (induction parameters)
   forall Q1...,(Qi:Ti_1 -> Ti_2 ->...-> Ti_ni),...Qq, (predicates)
   branch1, branch2, ... , branchr,                    (branches of the principle)
   forall (x1:Ti_1) (x2:Ti_2) ... (xni:Ti_ni),         (induction arguments)
   (HI: I prm1..prmp x1...xni)                         (optional main induction arg)
   -> (Qi x1...xni HI        (f prm1...prmp x1...xni)).(conclusion)
                   ^^        ^^^^^^^^^^^^^^^^^^^^^^^^
               optional        optional argument added if
               even if HI    principle generated by functional
             present above   induction, only if HI does not exist
             [indarg]                  [farg]

  HI is not present when the induction principle does not come directly from an
  inductive type (like when it is generated by functional induction for
  example). HI is present otherwise BUT may not appear in the conclusion
  (dependent principle). HI and (f...) cannot be both present.

  Principles taken from functional induction have the final (f...).*)

(* [rel_contexts] and [rel_declaration] actually contain triples, and
   lists are actually in reverse order to fit [compose_prod]. *)
type elim_scheme = {
  elimc: constr with_bindings option;
  elimt: types;
  indref: global_reference option;
  index: int;              (* index of the elimination type in the scheme *)
  params: rel_context;     (* (prm1,tprm1);(prm2,tprm2)...(prmp,tprmp) *)
  nparams: int;            (* number of parameters *)
  predicates: rel_context; (* (Qq, (Tq_1 -> Tq_2 ->...-> Tq_nq)), (Q1,...) *)
  npredicates: int;        (* Number of predicates *)
  branches: rel_context;   (* branchr,...,branch1 *)
  nbranches: int;          (* Number of branches *)
  args: rel_context;       (* (xni, Ti_ni) ... (x1, Ti_1) *)
  nargs: int;              (* number of arguments *)
  indarg: rel_declaration option; (* Some (H,I prm1..prmp x1...xni)
				     if HI is in premisses, None otherwise *)
  concl: types;            (* Qi x1...xni HI (f...), HI and (f...)
			      are optional and mutually exclusive *)
  indarg_in_concl: bool;   (* true if HI appears at the end of conclusion *)
  farg_in_concl: bool;     (* true if (f...) appears at the end of conclusion *)
}

let empty_scheme =
  {
    elimc = None;
    elimt = mkProp;
    indref = None;
    index = -1;
    params = [];
    nparams = 0;
    predicates = [];
    npredicates = 0;
    branches = [];
    nbranches = 0;
    args = [];
    nargs = 0;
    indarg = None;
    concl = mkProp;
    indarg_in_concl = false;
    farg_in_concl = false;
  }

let make_base n id =
  if n=0 or n=1 then id
  else
    (* This extends the name to accept new digits if it already ends with *)
    (* digits *)
    id_of_string (atompart_of_id (make_ident (string_of_id id) (Some 0)))

(* Builds two different names from an optional inductive type and a
   number, also deals with a list of names to avoid. If the inductive
   type is None, then hyprecname is IHi where i is a number. *)
let make_up_names n ind_opt cname =
  let is_hyp = atompart_of_id cname = "H" in
  let base = string_of_id (make_base n cname) in
  let ind_prefix = "IH" in
  let base_ind =
    if is_hyp then
      match ind_opt with
	| None -> id_of_string ind_prefix
	| Some ind_id -> add_prefix ind_prefix (Nametab.basename_of_global ind_id)
    else add_prefix ind_prefix cname in
  let hyprecname = make_base n base_ind in
  let avoid =
    if n=1 (* Only one recursive argument *) or n=0 then []
    else
      (* Forbid to use cname, cname0, hyprecname and hyprecname0 *)
      (* in order to get names such as f1, f2, ... *)
      let avoid =
        (make_ident (string_of_id hyprecname) None) ::
        (make_ident (string_of_id hyprecname) (Some 0)) :: [] in
      if atompart_of_id cname <> "H" then
        (make_ident base (Some 0)) :: (make_ident base None) :: avoid
      else avoid in
  id_of_string base, hyprecname, avoid

let error_ind_scheme s =
  let s = if s <> "" then s^" " else s in
  error ("Cannot recognize "^s^"an induction scheme.")

let coq_eq = Lazy.lazy_from_fun Coqlib.build_coq_eq
let coq_eq_refl = lazy ((Coqlib.build_coq_eq_data ()).Coqlib.refl)

let coq_heq = lazy (Coqlib.coq_constant "mkHEq" ["Logic";"JMeq"] "JMeq")
let coq_heq_refl = lazy (Coqlib.coq_constant "mkHEq" ["Logic";"JMeq"] "JMeq_refl")

let mkEq t x y = 
  mkApp (Lazy.force coq_eq, [| refresh_universes_strict t; x; y |])
    
let mkRefl t x = 
  mkApp (Lazy.force coq_eq_refl, [| refresh_universes_strict t; x |])

let mkHEq t x u y =
  mkApp (Lazy.force coq_heq,
	[| refresh_universes_strict t; x; refresh_universes_strict u; y |])
    
let mkHRefl t x =
  mkApp (Lazy.force coq_heq_refl,
	[| refresh_universes_strict t; x |])

let lift_togethern n l =
  let l', _ =
    List.fold_right
      (fun x (acc, n) ->
	(lift n x :: acc, succ n))
      l ([], n)
  in l'

let lift_list l = List.map (lift 1) l

let ids_of_constr ?(all=false) vars c =
  let rec aux vars c =
    match kind_of_term c with
    | Var id -> Idset.add id vars
    | App (f, args) -> 
	(match kind_of_term f with
	| Construct (ind,_)
	| Ind ind ->
            let (mib,mip) = Global.lookup_inductive ind in
	      array_fold_left_from
		(if all then 0 else mib.Declarations.mind_nparams)
		aux vars args
	| _ -> fold_constr aux vars c)
    | _ -> fold_constr aux vars c
  in aux vars c
    
let decompose_indapp f args =
  match kind_of_term f with
  | Construct (ind,_) 
  | Ind ind ->
      let (mib,mip) = Global.lookup_inductive ind in
      let first = mib.Declarations.mind_nparams_rec in
      let pars, args = array_chop first args in
	mkApp (f, pars), args
  | _ -> f, args

let mk_term_eq env sigma ty t ty' t' =
  if Reductionops.is_conv env sigma ty ty' then
    mkEq ty t t', mkRefl ty' t'
  else
    mkHEq ty t ty' t', mkHRefl ty' t'

let make_abstract_generalize gl id concl dep ctx body c eqs args refls =
  let meta = Evarutil.new_meta() in
  let eqslen = List.length eqs in
  let term, typ = mkVar id, pf_get_hyp_typ gl id in
    (* Abstract by the "generalized" hypothesis equality proof if necessary. *)
  let abshypeq, abshypt =
    if dep then
      let eq, refl = mk_term_eq (push_rel_context ctx (pf_env gl)) (project gl) (lift 1 c) (mkRel 1) typ term in
	mkProd (Anonymous, eq, lift 1 concl), [| refl |]
    else concl, [||]
  in
    (* Abstract by equalitites *)
  let eqs = lift_togethern 1 eqs in (* lift together and past genarg *)
  let abseqs = it_mkProd_or_LetIn (lift eqslen abshypeq) (List.map (fun x -> (Anonymous, None, x)) eqs) in
    (* Abstract by the "generalized" hypothesis. *)
  let genarg = mkProd_or_LetIn (Name id, body, c) abseqs in
    (* Abstract by the extension of the context *)
  let genctyp = it_mkProd_or_LetIn genarg ctx in
    (* The goal will become this product. *)
  let genc = mkCast (mkMeta meta, DEFAULTcast, genctyp) in
    (* Apply the old arguments giving the proper instantiation of the hyp *)
  let instc = mkApp (genc, Array.of_list args) in
    (* Then apply to the original instanciated hyp. *)
  let instc = Option.cata (fun _ -> instc) (mkApp (instc, [| mkVar id |])) body in
    (* Apply the reflexivity proofs on the indices. *)
  let appeqs = mkApp (instc, Array.of_list refls) in
    (* Finaly, apply the reflexivity proof for the original hyp, to get a term of type gl again. *)
    mkApp (appeqs, abshypt)

let hyps_of_vars env sign nogen hyps =
  if Idset.is_empty hyps then [] 
  else
    let (_,lh) =
      Sign.fold_named_context_reverse
        (fun (hs,hl) (x,_,_ as d) ->
	  if Idset.mem x nogen then (hs,hl)
	  else if Idset.mem x hs then (hs,x::hl)
	  else
	    let xvars = global_vars_set_of_decl env d in
	      if not (Idset.equal (Idset.diff xvars hs) Idset.empty) then
		(Idset.add x hs, x :: hl)
	      else (hs, hl))
        ~init:(hyps,[])
        sign 
    in lh

exception Seen

let linear vars args = 
  let seen = ref vars in
    try 
      Array.iter (fun i -> 
	let rels = ids_of_constr ~all:true Idset.empty i in
	let seen' = 
	  Idset.fold (fun id acc ->
	    if Idset.mem id acc then raise Seen
	    else Idset.add id acc)
	    rels !seen
	in seen := seen')
	args;
      true
    with Seen -> false

let abstract_args gl generalize_vars dep id defined f args =
  let sigma = project gl in
  let env = pf_env gl in
  let concl = pf_concl gl in
  let dep = dep || dependent (mkVar id) concl in
  let avoid = ref [] in
  let get_id name =
    let id = fresh_id !avoid (match name with Name n -> n | Anonymous -> id_of_string "gen_x") gl in
      avoid := id :: !avoid; id
  in
    (* Build application generalized w.r.t. the argument plus the necessary eqs.
       From env |- c : forall G, T and args : G we build
       (T[G'], G' : ctx, env ; G' |- args' : G, eqs := G'_i = G_i, refls : G' = G, vars to generalize)
       
       eqs are not lifted w.r.t. each other yet. (* will be needed when going to dependent indexes *)
    *)
  let aux (prod, ctx, ctxenv, c, args, eqs, refls, nongenvars, vars, env) arg =
    let (name, _, ty), arity =
      let rel, c = Reductionops.splay_prod_n env sigma 1 prod in
	List.hd rel, c
    in
    let argty = pf_type_of gl arg in
    let argty = refresh_universes_strict argty in 
    let lenctx = List.length ctx in
    let liftargty = lift lenctx argty in
    let leq = constr_cmp Reduction.CUMUL liftargty ty in
      match kind_of_term arg with
      | Var id when leq && not (Idset.mem id nongenvars) ->
      	  (subst1 arg arity, ctx, ctxenv, mkApp (c, [|arg|]), args, eqs, refls,
      	  Idset.add id nongenvars, Idset.remove id vars, env)
      | _ ->
	  let name = get_id name in
	  let decl = (Name name, None, ty) in
	  let ctx = decl :: ctx in
	  let c' = mkApp (lift 1 c, [|mkRel 1|]) in
	  let args = arg :: args in
	  let liftarg = lift (List.length ctx) arg in
	  let eq, refl =
	    if leq then
	      mkEq (lift 1 ty) (mkRel 1) liftarg, mkRefl (lift (-lenctx) ty) arg
	    else
	      mkHEq (lift 1 ty) (mkRel 1) liftargty liftarg, mkHRefl argty arg
	  in
	  let eqs = eq :: lift_list eqs in
	  let refls = refl :: refls in
	  let argvars = ids_of_constr vars arg in
	    (arity, ctx, push_rel decl ctxenv, c', args, eqs, refls, 
	    nongenvars, Idset.union argvars vars, env)
  in 
  let f', args' = decompose_indapp f args in
  let dogen, f', args' =
    let parvars = ids_of_constr ~all:true Idset.empty f' in
      if not (linear parvars args') then true, f, args
      else
	match array_find_i (fun i x -> not (isVar x)) args' with
	| None -> false, f', args'
	| Some nonvar ->
	    let before, after = array_chop nonvar args' in
	      true, mkApp (f', before), after
  in
    if dogen then
      let arity, ctx, ctxenv, c', args, eqs, refls, nogen, vars, env = 
	Array.fold_left aux (pf_type_of gl f',[],env,f',[],[],[],Idset.empty,Idset.empty,env) args'
      in
      let args, refls = List.rev args, List.rev refls in
      let vars = 
	if generalize_vars then
	  let nogen = Idset.add id nogen in
	    hyps_of_vars (pf_env gl) (pf_hyps gl) nogen vars
	else []
      in
      let body, c' = if defined then Some c', Retyping.get_type_of ctxenv Evd.empty c' else None, c' in
	Some (make_abstract_generalize gl id concl dep ctx body c' eqs args refls,
	     dep, succ (List.length ctx), vars)
    else None
      
let abstract_generalize ?(generalize_vars=true) ?(force_dep=false) id gl =
  Coqlib.check_required_library ["Coq";"Logic";"JMeq"];
  let f, args, def, id, oldid = 
    let oldid = pf_get_new_id id gl in
    let (_, b, t) = pf_get_hyp gl id in
      match b with
      | None -> let f, args = decompose_app t in
		  f, args, false, id, oldid
      | Some t -> 
	  let f, args = decompose_app t in
	    f, args, true, id, oldid
  in
  if args = [] then tclIDTAC gl
  else 
    let args = Array.of_list args in
    let newc = abstract_args gl generalize_vars force_dep id def f args in
      match newc with
      | None -> tclIDTAC gl
      | Some (newc, dep, n, vars) -> 
	  let tac =
	    if dep then
	      tclTHENLIST [refine newc; rename_hyp [(id, oldid)]; tclDO n intro; 
			   generalize_dep ~with_let:true (mkVar oldid)]	      
	    else
	      tclTHENLIST [refine newc; clear [id]; tclDO n intro]
	  in 
	    if vars = [] then tac gl
	    else tclTHEN tac 
	      (fun gl -> tclFIRST [revert vars ;
				   tclMAP (fun id -> 
				     tclTRY (generalize_dep ~with_let:true (mkVar id))) vars] gl) gl

let specialize_eqs id gl =
  let env = pf_env gl in
  let ty = pf_get_hyp_typ gl id in
  let evars = ref (create_evar_defs (project gl)) in
  let unif env evars c1 c2 = Evarconv.e_conv env evars c2 c1 in
  let rec aux in_eqs ctx acc ty =
    match kind_of_term ty with
    | Prod (na, t, b) -> 
	(match kind_of_term t with
	| App (eq, [| eqty; x; y |]) when eq_constr eq (Lazy.force coq_eq) ->
	    let c = if noccur_between 1 (List.length ctx) x then y else x in
	    let pt = mkApp (Lazy.force coq_eq, [| eqty; c; c |]) in
	    let p = mkApp (Lazy.force coq_eq_refl, [| eqty; c |]) in
	      if unif (push_rel_context ctx env) evars pt t then
		aux true ctx (mkApp (acc, [| p |])) (subst1 p b)
	      else acc, in_eqs, ctx, ty
	| App (heq, [| eqty; x; eqty'; y |]) when eq_constr heq (Lazy.force coq_heq) ->
	    let eqt, c = if noccur_between 1 (List.length ctx) x then eqty', y else eqty, x in
	    let pt = mkApp (Lazy.force coq_heq, [| eqt; c; eqt; c |]) in
	    let p = mkApp (Lazy.force coq_heq_refl, [| eqt; c |]) in
	      if unif (push_rel_context ctx env) evars pt t then
		aux true ctx (mkApp (acc, [| p |])) (subst1 p b)
	      else acc, in_eqs, ctx, ty
	| _ -> 
	    if in_eqs then acc, in_eqs, ctx, ty
	    else 
	      let e = e_new_evar evars (push_rel_context ctx env) t in
		aux false ((na, Some e, t) :: ctx) (mkApp (lift 1 acc, [| mkRel 1 |])) b)
    | t -> acc, in_eqs, ctx, ty
  in 
  let acc, worked, ctx, ty = aux false [] (mkVar id) ty in
  let ctx' = nf_rel_context_evar !evars ctx in
  let ctx'' = List.map (fun (n,b,t as decl) ->
    match b with
    | Some k when isEvar k -> (n,None,t)
    | b -> decl) ctx'
  in
  let ty' = it_mkProd_or_LetIn ty ctx'' in
  let acc' = it_mkLambda_or_LetIn acc ctx'' in
  let ty' = Tacred.whd_simpl env !evars ty' 
  and acc' = Tacred.whd_simpl env !evars acc' in
  let ty' = Evarutil.nf_evar !evars ty' in
    if worked then
      tclTHENFIRST (Tacmach.internal_cut true id ty')
	(exact_no_check (refresh_universes_strict acc')) gl
    else tclFAIL 0 (str "Nothing to do in hypothesis " ++ pr_id id) gl
      

let specialize_eqs id gl =
  if try ignore(clear [id] gl); false with _ -> true then
    tclFAIL 0 (str "Specialization not allowed on dependent hypotheses") gl 
  else specialize_eqs id gl

let occur_rel n c =
  let res = not (noccurn n c) in
  res

(* cuts a list in two parts, first of size n. Size must be greater than n *)
let cut_list n l =
  let rec cut_list_aux acc n l =
    if n<=0 then acc,l
    else match l with
      | [] -> assert false
      | e::l' -> cut_list_aux (acc@[e]) (n-1) l' in
  let res = cut_list_aux [] n l in
  res


(* This function splits the products of the induction scheme [elimt] into four
   parts:
   - branches, easily detectable (they are not referred by rels in the subterm)
   - what was found before branches (acc1) that is: parameters and predicates
   - what was found after branches (acc3) that is: args and indarg if any
   if there is no branch, we try to fill in acc3 with args/indargs.
   We also return the conclusion.
*)
let decompose_paramspred_branch_args elimt =
  let rec cut_noccur elimt acc2 : rel_context * rel_context * types =
    match kind_of_term elimt with
      | Prod(nme,tpe,elimt') ->
	  let hd_tpe,_ = decompose_app ((strip_prod_assum tpe)) in
	  if not (occur_rel 1 elimt') && isRel hd_tpe
	  then cut_noccur elimt' ((nme,None,tpe)::acc2)
	  else let acc3,ccl = decompose_prod_assum elimt in acc2 , acc3 , ccl
      | App(_, _) | Rel _ -> acc2 , [] , elimt
      | _ -> error_ind_scheme "" in
  let rec cut_occur elimt acc1 : rel_context * rel_context * rel_context * types =
    match kind_of_term elimt with
      | Prod(nme,tpe,c) when occur_rel 1 c -> cut_occur c ((nme,None,tpe)::acc1)
      | Prod(nme,tpe,c) -> let acc2,acc3,ccl = cut_noccur elimt [] in acc1,acc2,acc3,ccl
      | App(_, _) | Rel _ -> acc1,[],[],elimt
      | _ -> error_ind_scheme "" in
  let acc1, acc2 , acc3, ccl = cut_occur elimt [] in
  (* Particular treatment when dealing with a dependent empty type elim scheme:
     if there is no branch, then acc1 contains all hyps which is wrong (acc1
     should contain parameters and predicate only). This happens for an empty
     type (See for example Empty_set_ind, as False would actually be ok). Then
     we must find the predicate of the conclusion to separate params_pred from
     args. We suppose there is only one predicate here. *)
  if List.length acc2 <> 0 then acc1, acc2 , acc3, ccl
  else
    let hyps,ccl = decompose_prod_assum elimt in
    let hd_ccl_pred,_ = decompose_app ccl in
    match kind_of_term hd_ccl_pred with
      | Rel i  -> let acc3,acc1 = cut_list (i-1) hyps in acc1 , [] , acc3 , ccl
      | _ -> error_ind_scheme ""


let exchange_hd_app subst_hd t =
  let hd,args= decompose_app t in mkApp (subst_hd,Array.of_list args)



(* [rebuild_elimtype_from_scheme scheme] rebuilds the type of an
   eliminator from its [scheme_info]. The idea is to build variants of
   eliminator by modifying their scheme_info, then rebuild the
   eliminator type, then prove it (with tactics). *)
let rebuild_elimtype_from_scheme (scheme:elim_scheme): types =
  let hiconcl =
    match scheme.indarg with
      | None -> scheme.concl
      | Some x -> mkProd_or_LetIn x scheme.concl in
  let xihiconcl = it_mkProd_or_LetIn hiconcl scheme.args in
  let brconcl = it_mkProd_or_LetIn xihiconcl scheme.branches in
  let predconcl = it_mkProd_or_LetIn brconcl scheme.predicates in
  let paramconcl = it_mkProd_or_LetIn predconcl scheme.params in
  paramconcl


exception NoLastArg
exception NoLastArgCcl

(* Builds an elim_scheme from its type and calling form (const+binding). We
   first separate branches.  We obtain branches, hyps before (params + preds),
   hyps after (args <+ indarg if present>) and conclusion.  Then we proceed as
   follows:

   - separate parameters and predicates in params_preds. For that we build:
 forall (x1:Ti_1)(xni:Ti_ni) (HI:I prm1..prmp x1...xni), DUMMY x1...xni HI/farg
                             ^^^^^^^^^^^^^^^^^^^^^^^^^                  ^^^^^^^
                                       optional                           opt
     Free rels appearing in this term are parameters (branches should not
     appear, and the only predicate would have been Qi but we replaced it by
     DUMMY). We guess this heuristic catches all params.  TODO: generalize to
     the case where args are merged with branches (?) and/or where several
     predicates are cited in the conclusion.

   - finish to fill in the elim_scheme: indarg/farg/args and finally indref. *)
let compute_elim_sig ?elimc elimt =
  let params_preds,branches,args_indargs,conclusion =
    decompose_paramspred_branch_args elimt in

  let ccl = exchange_hd_app (mkVar (id_of_string "__QI_DUMMY__")) conclusion in
  let concl_with_args = it_mkProd_or_LetIn ccl args_indargs in
  let nparams = Intset.cardinal (free_rels concl_with_args) in
  let preds,params = cut_list (List.length params_preds - nparams) params_preds in

  (* A first approximation, further analysis will tweak it *)
  let res = ref { empty_scheme with
    (* This fields are ok: *)
    elimc = elimc; elimt = elimt; concl = conclusion;
    predicates = preds; npredicates = List.length preds;
    branches = branches; nbranches = List.length branches;
    farg_in_concl = isApp ccl && isApp (last_arg ccl);
    params = params; nparams = nparams;
    (* all other fields are unsure at this point. Including these:*)
    args = args_indargs; nargs = List.length args_indargs; } in
  try
    (* Order of tests below is important. Each of them exits if successful. *)
    (* 1- First see if (f x...) is in the conclusion. *)
    if !res.farg_in_concl
    then begin
      res := { !res with
	indarg = None;
	indarg_in_concl = false; farg_in_concl = true };
      raise Exit
    end;
    (* 2- If no args_indargs (=!res.nargs at this point) then no indarg *)
    if !res.nargs=0 then raise Exit;
    (* 3- Look at last arg: is it the indarg? *)
    ignore (
      match List.hd args_indargs with
	| hiname,Some _,hi -> error_ind_scheme ""
	| hiname,None,hi ->
	    let hi_ind, hi_args = decompose_app hi in
	    let hi_is_ind = (* hi est d'un type globalisable *)
	      match kind_of_term hi_ind with
		| Ind (mind,_)  -> true
		| Var _ -> true
		| Const _ -> true
		| Construct _ -> true
		| _ -> false in
	    let hi_args_enough = (* hi a le bon nbre d'arguments *)
	      List.length hi_args = List.length params + !res.nargs -1 in
	    (* FIXME: Ces deux tests ne sont pas suffisants. *)
	    if not (hi_is_ind & hi_args_enough) then raise Exit (* No indarg *)
	    else (* Last arg is the indarg *)
	      res := {!res with
		indarg = Some (List.hd !res.args);
		indarg_in_concl = occur_rel 1 ccl;
		args = List.tl !res.args; nargs = !res.nargs - 1;
	      };
	    raise Exit);
    raise Exit(* exit anyway *)
  with Exit -> (* Ending by computing indrev: *)
    match !res.indarg with
      | None -> !res (* No indref *)
      | Some ( _,Some _,_) -> error_ind_scheme ""
      | Some ( _,None,ind) ->
	  let indhd,indargs = decompose_app ind in
	  try {!res with indref = Some (global_of_constr indhd) }
	  with _ -> error "Cannot find the inductive type of the inductive scheme.";;

let compute_scheme_signature scheme names_info ind_type_guess =
  let f,l = decompose_app scheme.concl in
  (* Vérifier que les arguments de Qi sont bien les xi. *)
  match scheme.indarg with
    | Some (_,Some _,_) -> error "Strange letin, cannot recognize an induction scheme."
    | None -> (* Non standard scheme *)
	let is_pred n c =
	  let hd = fst (decompose_app c) in match kind_of_term hd with
	    | Rel q when n < q & q <= n+scheme.npredicates -> IndArg
	    | _ when hd = ind_type_guess & not scheme.farg_in_concl -> RecArg
	    | _ -> OtherArg in
	let rec check_branch p c =
	  match kind_of_term c with
	    | Prod (_,t,c) ->
		(is_pred p t, dependent (mkRel 1) c) :: check_branch (p+1) c
	    | LetIn (_,_,_,c) ->
		(OtherArg, dependent (mkRel 1) c) :: check_branch (p+1) c
	    | _ when is_pred p c = IndArg -> []
	    | _ -> raise Exit in
	let rec find_branches p lbrch =
	  match lbrch with
	    | (_,None,t)::brs ->
		(try
		  let lchck_brch = check_branch p t in
		  let n = List.fold_left
		    (fun n (b,_) -> if b=RecArg then n+1 else n) 0 lchck_brch in
		  let recvarname, hyprecname, avoid =
		    make_up_names n scheme.indref names_info in
		  let namesign =
		    List.map (fun (b,dep) ->
		      (b,dep,if b=IndArg then hyprecname else recvarname))
		      lchck_brch in
		  (avoid,namesign) :: find_branches (p+1) brs
		with Exit-> error_ind_scheme "the branches of")
	    | (_,Some _,_)::_ -> error_ind_scheme "the branches of"
	    | [] -> [] in
	Array.of_list (find_branches 0 (List.rev scheme.branches))

    | Some ( _,None,ind) -> (* Standard scheme from an inductive type *)
	let indhd,indargs = decompose_app ind in
	let is_pred n c =
	  let hd = fst (decompose_app c) in match kind_of_term hd with
	    | Rel q when n < q & q <= n+scheme.npredicates -> IndArg
	    | _ when hd = indhd -> RecArg
	    | _ -> OtherArg in
	let rec check_branch p c = match kind_of_term c with
	  | Prod (_,t,c) ->
	      (is_pred p t, dependent (mkRel 1) c) :: check_branch (p+1) c
	  | LetIn (_,_,_,c) ->
	      (OtherArg, dependent (mkRel 1) c) :: check_branch (p+1) c
	  | _ when is_pred p c = IndArg -> []
	  | _ -> raise Exit in
	let rec find_branches p lbrch =
	  match lbrch with
	    | (_,None,t)::brs ->
		(try
		  let lchck_brch = check_branch p t in
		  let n = List.fold_left
		    (fun n (b,_) -> if b=RecArg then n+1 else n) 0 lchck_brch in
		  let recvarname, hyprecname, avoid =
		    make_up_names n scheme.indref names_info in
		  let namesign =
		    List.map (fun (b,dep) ->
		      (b,dep,if b=IndArg then hyprecname else recvarname))
		      lchck_brch in
		  (avoid,namesign) :: find_branches (p+1) brs
		with Exit -> error_ind_scheme "the branches of")
	    | (_,Some _,_)::_ -> error_ind_scheme "the branches of"
	    | [] ->
		(* Check again conclusion *)

		let ccl_arg_ok = is_pred (p + scheme.nargs + 1) f = IndArg in
		let ind_is_ok =
		  list_lastn scheme.nargs indargs
		  = extended_rel_list 0 scheme.args in
		if not (ccl_arg_ok & ind_is_ok) then
		  error_ind_scheme "the conclusion of";
		[]
	in
	Array.of_list (find_branches 0 (List.rev scheme.branches))

(* Check that the elimination scheme has a form similar to the
   elimination schemes built by Coq. Schemes may have the standard
   form computed from an inductive type OR (feb. 2006) a non standard
   form. That is: with no main induction argument and with an optional
   extra final argument of the form (f x y ...) in the conclusion. In
   the non standard case, naming of generated hypos is slightly
   different. *)
let compute_elim_signature ((elimc,elimt),ind_type_guess) names_info =
  let scheme = compute_elim_sig ~elimc:elimc elimt in
  compute_scheme_signature scheme names_info ind_type_guess, scheme

let guess_elim isrec hyp0 gl =
  let tmptyp0 =	pf_get_hyp_typ gl hyp0 in
  let mind,_ = pf_reduce_to_quantified_ind gl tmptyp0 in
  let s = elimination_sort_of_goal gl in
  let elimc =
    if isrec then lookup_eliminator mind s
    else
      if use_dependent_propositions_elimination () &&
	dependent_no_evar (mkVar hyp0) (pf_concl gl)
      then
	pf_apply build_case_analysis_scheme gl mind true s
      else
	pf_apply build_case_analysis_scheme_default gl mind s in
  let elimt = pf_type_of gl elimc in
  ((elimc, NoBindings), elimt), mkInd mind

let given_elim hyp0 (elimc,lbind as e) gl =
  let tmptyp0 = pf_get_hyp_typ gl hyp0 in
  let ind_type_guess,_ = decompose_app ((strip_prod tmptyp0)) in
  (e, pf_type_of gl elimc), ind_type_guess

let find_elim isrec elim hyp0 gl =
  match elim with
    | None -> guess_elim isrec hyp0 gl
    | Some e -> given_elim hyp0 e gl

type scheme_signature =
    (identifier list * (elim_arg_kind * bool * identifier) list) array

type eliminator_source =
  | ElimUsing of (eliminator * types) * scheme_signature
  | ElimOver of bool * identifier

let find_induction_type isrec elim hyp0 gl =
  let scheme,elim =
    match elim with
    | None ->
	let (elimc,elimt),_ = guess_elim isrec hyp0 gl in
	let scheme = compute_elim_sig ~elimc elimt in
	(* We drop the scheme waiting to know if it is dependent *)
	scheme, ElimOver (isrec,hyp0)
    | Some e ->
	let (elimc,elimt),ind_guess = given_elim hyp0 e gl in
	let scheme = compute_elim_sig ~elimc elimt in
	if scheme.indarg = None then error "Cannot find induction type";
	let indsign = compute_scheme_signature scheme hyp0 ind_guess in
	let elim = ({elimindex = Some(-1); elimbody = elimc},elimt) in
	scheme, ElimUsing (elim,indsign) in
  Option.get scheme.indref,scheme.nparams, elim

let find_elim_signature isrec elim hyp0 gl =
  compute_elim_signature (find_elim isrec elim hyp0 gl) hyp0

let is_functional_induction elim gl =
  match elim with
  | Some elimc ->
      let scheme = compute_elim_sig ~elimc (pf_type_of gl (fst elimc)) in
      (* The test is not safe: with non-functional induction on non-standard
         induction scheme, this may fail *)
      scheme.indarg = None
  | None ->
      false

(* Wait the last moment to guess the eliminator so as to know if we
   need a dependent one or not *)

let get_eliminator elim gl = match elim with
  | ElimUsing (elim,indsign) ->
      (* bugged, should be computed *) true, elim, indsign
  | ElimOver (isrec,id) ->
      let (elimc,elimt),_ as elims = guess_elim isrec id gl in
      isrec, ({elimindex = None; elimbody = elimc}, elimt),
      fst (compute_elim_signature elims id)

(* Instantiate all meta variables of elimclause using lid, some elts
   of lid are parameters (first ones), the other are
   arguments. Returns the clause obtained.  *)
let recolle_clenv nparams lid elimclause gl =
  let _,arr = destApp elimclause.templval.rebus in
  let lindmv =
    Array.map
      (fun x ->
	match kind_of_term x with
	  | Meta mv -> mv
	  | _  -> errorlabstrm "elimination_clause"
              (str "The type of the elimination clause is not well-formed."))
      arr in
  let nmv = Array.length lindmv in
  let lidparams,lidargs = cut_list nparams lid in
  let nidargs = List.length lidargs in
  (* parameters correspond to first elts of lid. *)
  let clauses_params =
    list_map_i (fun i id -> mkVar id , pf_get_hyp_typ gl id , lindmv.(i))
      0 lidparams in
  (* arguments correspond to last elts of lid. *)
  let clauses_args =
    list_map_i
      (fun i id -> mkVar id , pf_get_hyp_typ gl id , lindmv.(nmv-nidargs+i))
      0 lidargs in
  let clauses = clauses_params@clauses_args in
  (* iteration of clenv_fchain with all infos we have. *)
  List.fold_right
    (fun e acc ->
      let x,y,i = e in
      (* from_n (Some 0) means that x should be taken "as is" without
         trying to unify (which would lead to trying to apply it to
         evars if y is a product). *)
      let indclause  = mk_clenv_from_n gl (Some 0) (x,y) in
      let elimclause' = clenv_fchain i acc indclause in
      elimclause')
    (List.rev clauses)
    elimclause

(* Unification of the goal and the principle applied to meta variables:
   (elimc ?i ?j ?k...?l). This solves partly meta variables (and may
    produce new ones). Then refine with the resulting term with holes.
*)
let induction_tac_felim with_evars indvars nparams elim gl =
  let {elimbody=(elimc,lbindelimc)},elimt = elim in
  (* elimclause contains this: (elimc ?i ?j ?k...?l) *)
  let elimclause =
    make_clenv_binding gl (mkCast (elimc,DEFAULTcast, elimt),elimt) lbindelimc in
  (* elimclause' is built from elimclause by instanciating all args and params. *)
  let elimclause' = recolle_clenv nparams indvars elimclause gl in
  (* one last resolution (useless?) *)
  let resolved = clenv_unique_resolver true elimclause' gl in
  clenv_refine with_evars resolved gl

(* Apply induction "in place" replacing the hypothesis on which
   induction applies with the induction hypotheses *)

let apply_induction_with_discharge induct_tac elim indhyps destopt avoid names tac gl =
  let isrec, elim, indsign = get_eliminator elim gl in
  let names = compute_induction_names (Array.length indsign) names in
  (if isrec then tclTHENFIRSTn else tclTHENLASTn)
    (tclTHEN (induct_tac elim) (tclTRY (thin indhyps)))
    (array_map2 (induct_discharge destopt avoid tac) indsign names) gl

(* Apply induction "in place" taking into account dependent
   hypotheses from the context *)

let apply_induction_in_context hyp0 elim indvars names induct_tac gl =
  let env = pf_env gl in
  let statuslists,lhyp0,indhyps,deps = cook_sign hyp0 indvars env in
  let deps = List.map (on_pi3 refresh_universes_strict) deps in
  let tmpcl = it_mkNamedProd_or_LetIn (pf_concl gl) deps in
  let dephyps = List.map (fun (id,_,_) -> id) deps in
  let deps_cstr =
    List.fold_left
      (fun a (id,b,_) -> if b = None then (mkVar id)::a else a) [] deps in
  tclTHENLIST
    [
      (* Generalize dependent hyps (but not args) *)
      if deps = [] then tclIDTAC else apply_type tmpcl deps_cstr;
      (* clear dependent hyps *)
      thin dephyps;
      (* side-conditions in elim (resp case) schemes come last (resp first) *)
      apply_induction_with_discharge
	induct_tac elim (List.rev indhyps) lhyp0 (List.rev dephyps) names
        (re_intro_dependent_hypotheses statuslists)
    ]
    gl

(* Induction with several induction arguments, main differences with
   induction_from_context is that there is no main induction argument,
   so we choose one to be the positioning reference. On the other hand,
   all args and params must be given, so we help a bit the unifier by
   making the "pattern" by hand before calling induction_tac_felim
   FIXME: REUNIF AVEC induction_tac_felim? *)
let induction_from_context_l with_evars elim_info lid names gl =
  let indsign,scheme = elim_info in
  (* number of all args, counting farg and indarg if present. *)
  let nargs_indarg_farg = scheme.nargs
    + (if scheme.farg_in_concl then 1 else 0)
    + (if scheme.indarg <> None then 1 else 0) in
  (* Number of given induction args must be exact. *)
  if List.length lid <> nargs_indarg_farg + scheme.nparams then
      error "Not the right number of arguments given to induction scheme.";
  (* hyp0 is used for re-introducing hyps at the right place afterward.
     We chose the first element of the list of variables on which to
     induct. It is probably the first of them appearing in the
     context. *)
  let hyp0,indvars,lid_params =
    match lid with
      | []  -> anomaly "induction_from_context_l"
      | e::l ->
	  let nargs_without_first = nargs_indarg_farg - 1 in
	  let ivs,lp = cut_list nargs_without_first l in
	  e, ivs, lp in
  (* terms to patternify we must patternify indarg or farg if present in concl *)
  let lid_in_pattern =
    if scheme.indarg <> None & not scheme.indarg_in_concl then List.rev indvars
    else List.rev (hyp0::indvars) in
  let lidcstr = List.map (fun x -> mkVar x) lid_in_pattern in
  let realindvars = (* hyp0 is a real induction arg if it is not the
		       farg in the conclusion of the induction scheme *)
    List.rev ((if scheme.farg_in_concl then indvars else hyp0::indvars) @ lid_params) in
  let induct_tac elim = tclTHENLIST [
    (* pattern to make the predicate appear. *)
    reduce (Pattern (List.map inj_with_occurrences lidcstr)) onConcl;
    (* Induction by "refine (indscheme ?i ?j ?k...)" + resolution of all
       possible holes using arguments given by the user (but the
       functional one). *)
    (* FIXME: Tester ca avec un principe dependant et non-dependant *)
    induction_tac_felim with_evars realindvars scheme.nparams elim
  ] in
  let elim = ElimUsing (({elimindex = Some scheme.index; elimbody = Option.get scheme.elimc}, scheme.elimt), indsign) in
  apply_induction_in_context
    None elim (hyp0::indvars) names induct_tac gl

(* Unification between ((elimc:elimt) ?i ?j ?k ?l ... ?m) and the
   hypothesis on which the induction is made *)
let induction_tac with_evars elim (varname,lbind) typ gl =
  let ({elimindex=i;elimbody=(elimc,lbindelimc)},elimt) = elim in
  let indclause = make_clenv_binding gl (mkVar varname,typ) lbind  in
  let i = match i with None -> index_of_ind_arg elimt | Some i -> i in
  let elimclause =
    make_clenv_binding gl
      (mkCast (elimc,DEFAULTcast,elimt),elimt) lbindelimc in
  elimination_clause_scheme with_evars true i elimclause indclause gl

let induction_from_context isrec with_evars (indref,nparams,elim) (hyp0,lbind) names
  inhyps gl =
  let tmptyp0 =	pf_get_hyp_typ gl hyp0 in
  let typ0 = pf_apply reduce_to_quantified_ref gl indref tmptyp0 in
  let indvars = find_atomic_param_of_ind nparams ((strip_prod typ0)) in
  let induct_tac elim = tclTHENLIST [
    induction_tac with_evars elim (hyp0,lbind) typ0;
    tclTRY (unfold_body hyp0);
    thin [hyp0]
  ] in
  apply_induction_in_context
    (Some (hyp0,inhyps)) elim indvars names induct_tac gl

let induction_with_atomization_of_ind_arg isrec with_evars elim names (hyp0,lbind) inhyps gl =
  let elim_info = find_induction_type isrec elim hyp0 gl in
  tclTHEN
    (atomize_param_of_ind elim_info hyp0)
    (induction_from_context isrec with_evars elim_info
      (hyp0,lbind) names inhyps) gl

(* Induction on a list of induction arguments. Analyse the elim
   scheme (which is mandatory for multiple ind args), check that all
   parameters and arguments are given (mandatory too). *)
let induction_without_atomization isrec with_evars elim names lid gl =
  let (indsign,scheme as elim_info) =
    find_elim_signature isrec elim (List.hd lid) gl in
  let awaited_nargs =
    scheme.nparams + scheme.nargs
    + (if scheme.farg_in_concl then 1 else 0)
    + (if scheme.indarg <> None then 1 else 0)
  in
  let nlid = List.length lid in
  if nlid <> awaited_nargs
  then error "Not the right number of induction arguments."
  else induction_from_context_l with_evars elim_info lid names gl

let has_selected_occurrences = function
  | None -> false
  | Some cls ->
      cls.concl_occs <> all_occurrences_expr ||
	cls.onhyps <> None && List.exists (fun ((occs,_),hl) ->
          occs <> all_occurrences_expr || hl <> InHyp) (Option.get cls.onhyps)

(* assume that no occurrences are selected *)
let clear_unselected_context id inhyps cls gl =
  match cls with
  | None -> tclIDTAC gl
  | Some cls ->
      if occur_var (pf_env gl) id (pf_concl gl) &&
	 cls.concl_occs = no_occurrences_expr
      then errorlabstrm ""
	    (str "Conclusion must be mentioned: it depends on " ++ pr_id id
	     ++ str ".");
      match cls.onhyps with
      | Some hyps ->
	  let to_erase (id',_,_ as d) =
	    if List.mem id' inhyps then (* if selected, do not erase *) None
	    else
	      (* erase if not selected and dependent on id or selected hyps *)
	      let test id = occur_var_in_decl (pf_env gl) id d in
	      if List.exists test (id::inhyps) then Some id' else None in
	  let ids = list_map_filter to_erase (pf_hyps gl) in
	  thin ids gl
      | None -> tclIDTAC gl

let new_induct_gen isrec with_evars elim (eqname,names) (c,lbind) cls gl =
  let inhyps = match cls with
  | Some {onhyps=Some hyps} -> List.map (fun ((_,id),_) -> id) hyps
  | _ -> [] in
  match kind_of_term c with
    | Var id when not (mem_named_context id (Global.named_context()))
	        & lbind = NoBindings & not with_evars & eqname = None
                & not (has_selected_occurrences cls) ->
	tclTHEN
          (clear_unselected_context id inhyps cls)
	  (induction_with_atomization_of_ind_arg
	    isrec with_evars elim names (id,lbind) inhyps) gl
    | _        ->
	let x = id_of_name_using_hdchar (Global.env()) (pf_type_of gl c)
		  Anonymous in
	let id = fresh_id [] x gl in
	(* We need the equality name now *)
	let with_eq = Option.map (fun eq -> (false,eq)) eqname in
	(* TODO: if ind has predicate parameters, use JMeq instead of eq *)
	tclTHEN
	  (letin_tac_gen with_eq (Name id) c None (Option.default allHypsAndConcl cls,false))
	  (induction_with_atomization_of_ind_arg
	     isrec with_evars elim names (id,lbind) inhyps) gl

(* Induction on a list of arguments. First make induction arguments
   atomic (using letins), then do induction. The specificity here is
   that all arguments and parameters of the scheme are given
   (mandatory for the moment), so we don't need to deal with
    parameters of the inductive type as in new_induct_gen. *)
let new_induct_gen_l isrec with_evars elim (eqname,names) lc gl =
  if eqname <> None then
    errorlabstrm "" (str "Do not know what to do with " ++
      pr_intro_pattern (Option.get eqname));
  let newlc = ref [] in
  let letids = ref [] in
  let rec atomize_list l gl =
    match l with
      | [] -> tclIDTAC gl
      | c::l' ->
	  match kind_of_term c with
	    | Var id when not (mem_named_context id (Global.named_context()))
		& not with_evars ->
		let _ = newlc:= id::!newlc in
		atomize_list l' gl

	    | _ ->
		let x =
		  id_of_name_using_hdchar (Global.env()) (pf_type_of gl c) Anonymous in

		let id = fresh_id [] x gl in
		let newl' = List.map (replace_term c (mkVar id)) l' in
		let _ = newlc:=id::!newlc in
		let _ = letids:=id::!letids in
		tclTHEN
		  (letin_tac None (Name id) c None allHypsAndConcl)
		  (atomize_list newl') gl in
  tclTHENLIST
    [
      (atomize_list lc);
      (fun gl' -> (* recompute each time to have the new value of newlc *)
	induction_without_atomization isrec with_evars elim names !newlc gl') ;
      (* after induction, try to unfold all letins created by atomize_list
         FIXME: unfold_all does not exist anywhere else? *)
      (fun gl' -> (* recompute each time to have the new value of letids *)
	tclMAP (fun x -> tclTRY (unfold_all x)) !letids gl')
    ]
    gl

(* Induction either over a term, over a quantified premisse, or over
   several quantified premisses (like with functional induction
   principles).
   TODO: really unify induction with one and induction with several
   args *)
let induct_destruct isrec with_evars (lc,elim,names,cls) gl =
  assert (List.length lc > 0); (* ensured by syntax, but if called inside caml? *)
  if List.length lc = 1 && not (is_functional_induction elim gl) then
    (* standard induction *)
    onInductionArg
      (fun c -> new_induct_gen isrec with_evars elim names c cls)
      (List.hd lc) gl
  else begin
    (* functional induction *)
    (* Several induction hyps: induction scheme is mandatory *)
    if elim = None
    then
      errorlabstrm "" (strbrk "Induction scheme must be given when several induction hypotheses are given.\n" ++
      str "Example: induction x1 x2 x3 using my_scheme.");
    if cls <> None then
      error "'in' clause not supported here.";
    if List.length lc = 1 then
      (* Hook to recover standard induction on non-standard induction schemes *)
      (* will be removable when is_functional_induction will be more clever *)
      onInductionArg
	(fun (c,lbind) ->
	  if lbind <> NoBindings then
	    error "'with' clause not supported here.";
	  new_induct_gen_l isrec with_evars elim names [c])
	(List.hd lc) gl
    else
      let newlc =
	List.map (fun x ->
	  match x with (* FIXME: should we deal with ElimOnIdent? *)
	  | ElimOnConstr (x,NoBindings) -> x
	  | _ -> error "Don't know where to find some argument.")
	  lc in
      new_induct_gen_l isrec with_evars elim names newlc gl
  end

let induction_destruct isrec with_evars = function
  | [],_ -> tclIDTAC
  | [a,b,c],cl -> induct_destruct isrec with_evars (a,b,c,cl)
  | (a,b,c)::l,cl ->
      tclTHEN
        (induct_destruct isrec with_evars (a,b,c,cl))
        (tclMAP (fun (a,b,c) -> induct_destruct false with_evars (a,b,c,cl)) l)

let new_induct ev lc e idl cls = induct_destruct true ev (lc,e,idl,cls)
let new_destruct ev lc e idl cls = induct_destruct false ev (lc,e,idl,cls)

(* The registered tactic, which calls the default elimination
 * if no elimination constant is provided. *)

(* Induction tactics *)

(* This was Induction before 6.3 (induction only in quantified premisses) *)
let simple_induct_id s = tclTHEN (intros_until_id s) (onLastHyp simplest_elim)
let simple_induct_nodep n = tclTHEN (intros_until_n n) (onLastHyp simplest_elim)

let simple_induct = function
  | NamedHyp id -> simple_induct_id id
  | AnonHyp n -> simple_induct_nodep n

(* Destruction tactics *)

let simple_destruct_id s    =
  (tclTHEN (intros_until_id s) (onLastHyp simplest_case))
let simple_destruct_nodep n =
  (tclTHEN (intros_until_n n)    (onLastHyp simplest_case))

let simple_destruct = function
  | NamedHyp id -> simple_destruct_id id
  | AnonHyp n -> simple_destruct_nodep n

(*
 *  Eliminations giving the type instead of the proof.
 * These tactics use the default elimination constant and
 * no substitutions at all.
 * May be they should be integrated into Elim ...
 *)

let elim_scheme_type elim t gl =
  let clause = mk_clenv_type_of gl elim in
  match kind_of_term (last_arg clause.templval.rebus) with
    | Meta mv ->
        let clause' =
	  (* t is inductive, then CUMUL or CONV is irrelevant *)
	  clenv_unify true Reduction.CUMUL t
            (clenv_meta_type clause mv) clause in
	res_pf clause' ~allow_K:true gl
    | _ -> anomaly "elim_scheme_type"

let elim_type t gl =
  let (ind,t) = pf_reduce_to_atomic_ind gl t in
  let elimc = lookup_eliminator ind (elimination_sort_of_goal gl) in
  elim_scheme_type elimc t gl

let case_type t gl =
  let (ind,t) = pf_reduce_to_atomic_ind gl t in
  let elimc = pf_apply build_case_analysis_scheme_default gl ind (elimination_sort_of_goal gl) in
  elim_scheme_type elimc t gl


(* Some eliminations frequently used *)

(* These elimination tactics are particularly adapted for sequent
   calculus.  They take a clause as argument, and yield the
   elimination rule if the clause is of the form (Some id) and a
   suitable introduction rule otherwise. They do not depend on
   the name of the eliminated constant, so they can be also
   used on ad-hoc disjunctions and conjunctions introduced by
   the user.
   -- Eduardo Gimenez (11/8/97)

   HH (29/5/99) replaces failures by specific error messages
 *)

let andE id gl =
  let t = pf_get_hyp_typ gl id in
  if is_conjunction (pf_hnf_constr gl t) then
    (tclTHEN (simplest_elim (mkVar id)) (tclDO 2 intro)) gl
  else
    errorlabstrm "andE"
      (str("Tactic andE expects "^(string_of_id id)^" is a conjunction."))

let dAnd cls =
  onClause
    (function
      | None    -> simplest_split
      | Some id -> andE id)
    cls

let orE id gl =
  let t = pf_get_hyp_typ gl id in
  if is_disjunction (pf_hnf_constr gl t) then
    (tclTHEN (simplest_elim (mkVar id)) intro) gl
  else
    errorlabstrm "orE"
      (str("Tactic orE expects "^(string_of_id id)^" is a disjunction."))

let dorE b cls =
  onClause
    (function
      | Some id -> orE id
      | None    -> (if b then right else left) NoBindings)
    cls

let impE id gl =
  let t = pf_get_hyp_typ gl id in
  if is_imp_term (pf_hnf_constr gl t) then
    let (dom, _, rng) = destProd (pf_hnf_constr gl t) in
    tclTHENLAST
      (cut_intro rng)
      (apply_term (mkVar id) [mkMeta (new_meta())]) gl
  else
    errorlabstrm "impE"
      (str("Tactic impE expects "^(string_of_id id)^
	      " is a an implication."))

let dImp cls =
  onClause
    (function
      | None    -> intro
      | Some id -> impE id)
    cls

(************************************************)
(*  Tactics related with logic connectives      *)
(************************************************)

(* Reflexivity tactics *)

let setoid_reflexivity = ref (fun _ -> assert false)
let register_setoid_reflexivity f = setoid_reflexivity := f

let reflexivity_red allowred gl =
  (* PL: usual reflexivity don't perform any reduction when searching
     for an equality, but we may need to do some when called back from
     inside setoid_reflexivity (see Optimize cases in setoid_replace.ml). *)
  let concl = if not allowred then pf_concl gl
  else whd_betadeltaiota (pf_env gl) (project gl) (pf_concl gl)
  in
    match match_with_equality_type concl with
    | None -> raise NoEquationFound
    | Some _ -> one_constructor 1 NoBindings gl

let reflexivity gl =
  try reflexivity_red false gl with NoEquationFound -> !setoid_reflexivity gl

let intros_reflexivity  = (tclTHEN intros reflexivity)

(* Symmetry tactics *)

(* This tactic first tries to apply a constant named sym_eq, where eq
   is the name of the equality predicate. If this constant is not
   defined and the conclusion is a=b, it solves the goal doing (Cut
   b=a;Intro H;Case H;Constructor 1) *)

let setoid_symmetry = ref (fun _ -> assert false)
let register_setoid_symmetry f = setoid_symmetry := f

(* This is probably not very useful any longer *)
let prove_symmetry hdcncl eq_kind =
  let symc =
    match eq_kind with
    | MonomorphicLeibnizEq (c1,c2) -> mkApp(hdcncl,[|c2;c1|])
    | PolymorphicLeibnizEq (typ,c1,c2) -> mkApp(hdcncl,[|typ;c2;c1|])
    | HeterogenousEq (t1,c1,t2,c2) -> mkApp(hdcncl,[|t2;c2;t1;c1|]) in
  tclTHENFIRST (cut symc)
    (tclTHENLIST
      [ intro;
        onLastHyp simplest_case;
	one_constructor 1 NoBindings ])

let symmetry_red allowred gl =
  (* PL: usual symmetry don't perform any reduction when searching
     for an equality, but we may need to do some when called back from
     inside setoid_reflexivity (see Optimize cases in setoid_replace.ml). *)
  let concl =
    if not allowred then pf_concl gl else pf_whd_betadeltaiota gl (pf_concl gl)
  in
  match match_with_equation concl with
  | Some eq_data,_,_ ->
      tclTHEN
        (convert_concl_no_check concl DEFAULTcast)
      (apply eq_data.sym) gl
  | None,eq,eq_kind -> prove_symmetry eq eq_kind gl

let symmetry gl =
  try symmetry_red false gl with NoEquationFound -> !setoid_symmetry gl

let setoid_symmetry_in = ref (fun _ _ -> assert false)
let register_setoid_symmetry_in f = setoid_symmetry_in := f

let symmetry_in id gl =
  let ctype = pf_type_of gl (mkVar id) in
  let sign,t = decompose_prod_assum ctype in
  try
    let _,hdcncl,eq = match_with_equation t in
    let symccl = match eq with
      | MonomorphicLeibnizEq (c1,c2) -> mkApp (hdcncl, [| c2; c1 |])
      | PolymorphicLeibnizEq (typ,c1,c2) -> mkApp (hdcncl, [| typ; c2; c1 |])
      | HeterogenousEq (t1,c1,t2,c2) -> mkApp (hdcncl, [| t2; c2; t1; c1 |]) in
    tclTHENS (cut (it_mkProd_or_LetIn symccl sign))
      [ intro_replacing id;
        tclTHENLIST [ intros; symmetry; apply (mkVar id); assumption ] ]
      gl
  with NoEquationFound -> !setoid_symmetry_in id gl

let intros_symmetry =
  onClause
    (function
      | None -> tclTHEN intros symmetry
      | Some id -> symmetry_in id)

(* Transitivity tactics *)

(* This tactic first tries to apply a constant named trans_eq, where eq
   is the name of the equality predicate. If this constant is not
   defined and the conclusion is a=b, it solves the goal doing
   Cut x1=x2;
       [Cut x2=x3; [Intros e1 e2; Case e2;Assumption
                    | Idtac]
       | Idtac]
   --Eduardo (19/8/97)
*)

let setoid_transitivity = ref (fun _ _ -> assert false)
let register_setoid_transitivity f = setoid_transitivity := f

(* This is probably not very useful any longer *)
let prove_transitivity hdcncl eq_kind t gl =
  let eq1,eq2 =
    match eq_kind with
    | MonomorphicLeibnizEq (c1,c2) ->
      (mkApp (hdcncl, [| c1; t|]), mkApp (hdcncl, [| t; c2 |]))
  | PolymorphicLeibnizEq (typ,c1,c2) ->
      (mkApp (hdcncl, [| typ; c1; t |]), mkApp (hdcncl, [| typ; t; c2 |]))
  | HeterogenousEq (typ1,c1,typ2,c2) ->
      let typt = pf_type_of gl t in
      (mkApp(hdcncl, [| typ1; c1; typt ;t |]),
       mkApp(hdcncl, [| typt; t; typ2; c2 |])) in
  tclTHENFIRST (cut eq2)
    (tclTHENFIRST (cut eq1)
      (tclTHENLIST
	[ tclDO 2 intro;
	  onLastHyp simplest_case;
	  assumption ])) gl

let transitivity_red allowred t gl =
  (* PL: usual transitivity don't perform any reduction when searching
     for an equality, but we may need to do some when called back from
     inside setoid_reflexivity (see Optimize cases in setoid_replace.ml). *)
  let concl =
    if not allowred then pf_concl gl else pf_whd_betadeltaiota gl (pf_concl gl)
  in
  match match_with_equation concl with
  | Some eq_data,_,_ ->
      tclTHEN
        (convert_concl_no_check concl DEFAULTcast)
        (match t with
	 | None -> eapply eq_data.trans
	 | Some t -> apply_list [eq_data.trans;t]) gl
  | None,eq,eq_kind ->
      match t with
      | None -> error "etransitivity not supported for this relation."
      | Some t -> prove_transitivity eq eq_kind t gl

let transitivity_gen t gl =
  try transitivity_red false t gl
  with NoEquationFound -> !setoid_transitivity t gl

let etransitivity = transitivity_gen None
let transitivity t = transitivity_gen (Some t)

let intros_transitivity  n  = tclTHEN intros (transitivity_gen n)

(* tactical to save as name a subproof such that the generalisation of
   the current goal, abstracted with respect to the local signature,
   is solved by tac *)

let interpretable_as_section_decl d1 d2 = match d1,d2 with
  | (_,Some _,_), (_,None,_) -> false
  | (_,Some b1,t1), (_,Some b2,t2) -> eq_constr b1 b2 & eq_constr t1 t2
  | (_,None,t1), (_,_,t2) -> eq_constr t1 t2

let abstract_subproof id tac gl =
  let current_sign = Global.named_context()
  and global_sign = pf_hyps gl in
  let sign,secsign =
    List.fold_right
      (fun (id,_,_ as d) (s1,s2) ->
	if mem_named_context id current_sign &
          interpretable_as_section_decl (Sign.lookup_named id current_sign) d
        then (s1,push_named_context_val d s2)
	else (add_named_decl d s1,s2))
      global_sign (empty_named_context,empty_named_context_val) in
  let id = next_global_ident_away id (pf_ids_of_hyps gl) in
  let concl = it_mkNamedProd_or_LetIn (pf_concl gl) sign in
  let concl =
    try flush_and_check_evars (project gl) concl
    with Uninstantiated_evar _ ->
      error "\"abstract\" cannot handle existentials." in
  let const = Pfedit.build_constant_by_tactic secsign concl
    (tclCOMPLETE (tclTHEN (tclDO (List.length sign) intro) tac)) in
  let cd = Entries.DefinitionEntry const in
  let lem = mkConst (Declare.declare_constant ~internal:Declare.KernelSilent id (cd,IsProof Lemma)) in
  exact_no_check
    (applist (lem,List.rev (Array.to_list (instance_from_named_context sign))))
    gl

let tclABSTRACT name_op tac gl =
  let s = match name_op with
    | Some s -> s
    | None   -> add_suffix (get_current_proof_name ()) "_subproof"
  in
  abstract_subproof s tac gl


let admit_as_an_axiom gl =
  let current_sign = Global.named_context()
  and global_sign = pf_hyps gl in
  let sign,secsign =
    List.fold_right
      (fun (id,_,_ as d) (s1,s2) ->
	 if mem_named_context id current_sign &
           interpretable_as_section_decl (Sign.lookup_named id current_sign) d
         then (s1,add_named_decl d s2)
	 else (add_named_decl d s1,s2))
      global_sign (empty_named_context,empty_named_context) in
  let name = add_suffix (get_current_proof_name ()) "_admitted" in
  let na = next_global_ident_away name (pf_ids_of_hyps gl) in
  let concl = it_mkNamedProd_or_LetIn (pf_concl gl) sign in
  if occur_existential concl then error"\"admit\" cannot handle existentials.";
  let axiom =
    let cd = Entries.ParameterEntry (concl,false) in
    let con = Declare.declare_constant ~internal:Declare.KernelSilent na (cd,IsAssumption Logical) in
    constr_of_global (ConstRef con)
  in
  exact_no_check
    (applist (axiom,
              List.rev (Array.to_list (instance_from_named_context sign))))
    gl

let unify ?(state=full_transparent_state) x y gl =
  try
    let flags =
      {default_unify_flags with
	modulo_delta = state;
	modulo_conv_on_closed_terms = Some state}
    in
    let evd = w_unify false (pf_env gl) Reduction.CONV
      ~flags x y (Evd.create_evar_defs (project gl))
    in tclEVARS evd gl
  with _ -> tclFAIL 0 (str"Not unifiable") gl
