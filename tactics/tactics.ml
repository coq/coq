(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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
open Context
open Termops
open Find_subterm
open Namegen
open Declarations
open Inductiveops
open Reductionops
open Environ
open Globnames
open Evd
open Pfedit
open Tacred
open Genredexpr
open Tacmach
open Logic
open Clenv
open Refiner
open Tacticals
open Hipattern
open Coqlib
open Tacexpr
open Decl_kinds
open Evarutil
open Indrec
open Pretype_errors
open Unification
open Locus
open Locusops
open Misctypes
open Proofview.Notations

let nb_prod x =
  let rec count n c =
    match kind_of_term c with
        Prod(_,_,t) -> count (n+1) t
      | LetIn(_,a,_,t) -> count n (subst1 a t)
      | Cast(c,_,_) -> count n c
      | _ -> n
  in count 0 x

let inj_with_occurrences e = (AllOccurrences,e)

let dloc = Loc.ghost

let typ_of = Retyping.get_type_of

(* Option for 8.4 compatibility *)
open Goptions
let legacy_elim_if_not_fully_applied_argument = ref false

let use_legacy_elim_if_not_fully_applied_argument () =
  !legacy_elim_if_not_fully_applied_argument
  || Flags.version_less_or_equal Flags.V8_4

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "partially applied elimination argument legacy";
      optkey   = ["Legacy";"Partially";"Applied";"Elimination";"Argument"];
      optread  = (fun () -> !legacy_elim_if_not_fully_applied_argument) ;
      optwrite = (fun b -> legacy_elim_if_not_fully_applied_argument := b) }

(* Option for 8.2 compatibility *)
let dependent_propositions_elimination = ref true

let use_dependent_propositions_elimination () =
  !dependent_propositions_elimination
  && Flags.version_strictly_greater Flags.V8_2

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "dependent-propositions-elimination tactic";
      optkey   = ["Dependent";"Propositions";"Elimination"];
      optread  = (fun () -> !dependent_propositions_elimination) ;
      optwrite = (fun b -> dependent_propositions_elimination := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "trigger bugged context matching compatibility";
      optkey   = ["Tactic";"Compat";"Context"];
      optread  = (fun () -> !Flags.tactic_context_compat) ;
      optwrite = (fun b -> Flags.tactic_context_compat := b) }

let apply_solve_class_goals = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optsync = true; Goptions.optdepr = false;
  Goptions.optname =
    "Perform typeclass resolution on apply-generated subgoals.";
  Goptions.optkey = ["Typeclass";"Resolution";"After";"Apply"];
  Goptions.optread = (fun () -> !apply_solve_class_goals);
  Goptions.optwrite = (fun a -> apply_solve_class_goals:=a);
}

let clear_hyp_by_default = ref false

let use_clear_hyp_by_default () = !clear_hyp_by_default

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "default clearing of hypotheses after use";
      optkey   = ["Default";"Clearing";"Used";"Hypotheses"];
      optread  = (fun () -> !clear_hyp_by_default) ;
      optwrite = (fun b -> clear_hyp_by_default := b) }

(*********************************************)
(*                 Tactics                   *)
(*********************************************)

(******************************************)
(*           Primitive tactics            *)
(******************************************)

(** This tactic creates a partial proof realizing the introduction rule, but
    does not check anything. *)
let unsafe_intro env store (id, c, t) b =
  Proofview.Refine.refine ~unsafe:true begin fun sigma ->
    let ctx = named_context_val env in
    let nctx = push_named_context_val (id, c, t) ctx in
    let inst = List.map (fun (id, _, _) -> mkVar id) (named_context env) in
    let ninst = mkRel 1 :: inst in
    let nb = subst1 (mkVar id) b in
    let sigma, ev = new_evar_instance nctx sigma nb ~store ninst in
    sigma, mkNamedLambda_or_LetIn (id, c, t) ev
  end

let introduction ?(check=true) id =
  Proofview.Goal.enter begin fun gl ->
    let gl = Proofview.Goal.assume gl in
    let concl = Proofview.Goal.concl gl in
    let sigma = Proofview.Goal.sigma gl in
    let hyps = Proofview.Goal.hyps gl in
    let store = Proofview.Goal.extra gl in
    let env = Proofview.Goal.env gl in
    let () = if check && mem_named_context id hyps then
      error ("Variable " ^ Id.to_string id ^ " is already declared.")
    in
    match kind_of_term (whd_evar sigma concl) with
    | Prod (_, t, b) -> unsafe_intro env store (id, None, t) b
    | LetIn (_, c, t, b) -> unsafe_intro env store (id, Some c, t) b
    | _ -> raise (RefinerError IntroNeedsProduct)
  end

let refine          = Tacmach.refine

let convert_concl ?(check=true) ty k =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let store = Proofview.Goal.extra gl in
    let conclty = Proofview.Goal.raw_concl gl in
    Proofview.Refine.refine ~unsafe:true begin fun sigma ->
      let sigma =
        if check then begin
          ignore (Typing.type_of env sigma ty);
          let sigma,b = Reductionops.infer_conv env sigma ty conclty in
          if not b then error "Not convertible.";
          sigma
        end else sigma in
      let (sigma,x) = Evarutil.new_evar env sigma ~principal:true ~store ty in
      (sigma, if k == DEFAULTcast then x else mkCast(x,k,conclty))
    end
  end

let convert_hyp ?(check=true) d =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let ty = Proofview.Goal.raw_concl gl in
    let store = Proofview.Goal.extra gl in
    let sign = convert_hyp check (named_context_val env) sigma d in
    let env = reset_with_named_context sign env in
    Proofview.Refine.refine ~unsafe:true (fun sigma -> Evarutil.new_evar env sigma ~principal:true ~store ty)
  end

let convert_concl_no_check = convert_concl ~check:false
let convert_hyp_no_check = convert_hyp ~check:false

let convert_gen pb x y =
  Proofview.Goal.enter begin fun gl ->
    try
      let sigma = Tacmach.New.pf_apply Evd.conversion gl pb x y in
      Proofview.Unsafe.tclEVARS sigma
    with (* Reduction.NotConvertible *) _ ->
      (** FIXME: Sometimes an anomaly is raised from conversion *)
      Tacticals.New.tclFAIL 0 (str "Not convertible")
end

let convert x y = convert_gen Reduction.CONV x y
let convert_leq x y = convert_gen Reduction.CUMUL x y

let clear_dependency_msg env sigma id = function
  | Evarutil.OccurHypInSimpleClause None ->
      pr_id id ++ str " is used in conclusion."
  | Evarutil.OccurHypInSimpleClause (Some id') ->
      pr_id id ++ strbrk " is used in hypothesis " ++ pr_id id' ++ str"."
  | Evarutil.EvarTypingBreak ev ->
      str "Cannot remove " ++ pr_id id ++
      strbrk " without breaking the typing of " ++
      Printer.pr_existential env sigma ev ++ str"."

let error_clear_dependency env sigma id err =
  errorlabstrm "" (clear_dependency_msg env sigma id err)

let replacing_dependency_msg env sigma id = function
  | Evarutil.OccurHypInSimpleClause None ->
      str "Cannot change " ++ pr_id id ++ str ", it is used in conclusion."
  | Evarutil.OccurHypInSimpleClause (Some id') ->
      str "Cannot change " ++ pr_id id ++
      strbrk ", it is used in hypothesis " ++ pr_id id' ++ str"."
  | Evarutil.EvarTypingBreak ev ->
      str "Cannot change " ++ pr_id id ++
      strbrk " without breaking the typing of " ++
      Printer.pr_existential env sigma ev ++ str"."

let error_replacing_dependency env sigma id err =
  errorlabstrm "" (replacing_dependency_msg env sigma id err)

let thin l gl =
  try thin l gl
  with Evarutil.ClearDependencyError (id,err) ->
    error_clear_dependency (pf_env gl) (project gl) id err

let thin_for_replacing l gl =
  try Tacmach.thin l gl
  with Evarutil.ClearDependencyError (id,err) ->
    error_replacing_dependency (pf_env gl) (project gl) id err

let apply_clear_request clear_flag dft c =
  let check_isvar c =
    if not (isVar c) then
      error "keep/clear modifiers apply only to hypothesis names." in
  let clear = match clear_flag with
    | None -> dft && isVar c
    | Some clear -> check_isvar c; clear in
  if clear then Proofview.V82.tactic (thin [destVar c])
  else Tacticals.New.tclIDTAC

(* Moving hypotheses *)
let move_hyp id dest gl = Tacmach.move_hyp id dest gl

(* Renaming hypotheses *)
let rename_hyp repl =
  let fold accu (src, dst) = match accu with
  | None -> None
  | Some (srcs, dsts) ->
    if Id.Set.mem src srcs then None
    else if Id.Set.mem dst dsts then None
    else
      let srcs = Id.Set.add src srcs in
      let dsts = Id.Set.add dst dsts in
      Some (srcs, dsts)
  in
  let init = Some (Id.Set.empty, Id.Set.empty) in
  let dom = List.fold_left fold init repl in
  match dom with
  | None -> Tacticals.New.tclZEROMSG (str "Not a one-to-one name mapping")
  | Some (src, dst) ->
    Proofview.Goal.enter begin fun gl ->
      let gl = Proofview.Goal.assume gl in
      let hyps = Proofview.Goal.hyps gl in
      let concl = Proofview.Goal.concl gl in
      let store = Proofview.Goal.extra gl in
      (** Check that we do not mess variables *)
      let fold accu (id, _, _) = Id.Set.add id accu in
      let vars = List.fold_left fold Id.Set.empty hyps in
      let () =
        if not (Id.Set.subset src vars) then
          let hyp = Id.Set.choose (Id.Set.diff src vars) in
          raise (RefinerError (NoSuchHyp hyp))
      in
      let mods = Id.Set.diff vars src in
      let () =
        try
          let elt = Id.Set.choose (Id.Set.inter dst mods) in
          Errors.errorlabstrm "" (pr_id elt ++ str " is already used")
        with Not_found -> ()
      in
      (** All is well *)
      let make_subst (src, dst) = (src, mkVar dst) in
      let subst = List.map make_subst repl in
      let subst c = Vars.replace_vars subst c in
      let map (id, body, t) =
        let id = try List.assoc_f Id.equal id repl with Not_found -> id in
        (id, Option.map subst body, subst t)
      in
      let nhyps = List.map map hyps in
      let nconcl = subst concl in
      let nctx = Environ.val_of_named_context nhyps in
      let instance = List.map (fun (id, _, _) -> mkVar id) hyps in
      Proofview.Refine.refine ~unsafe:true begin fun sigma ->
        Evarutil.new_evar_instance nctx sigma nconcl ~store instance
      end
    end

(**************************************************************)
(*          Fresh names                                       *)
(**************************************************************)

let fresh_id_in_env avoid id env =
  next_ident_away_in_goal id (avoid@ids_of_named_context (named_context env))

let fresh_id avoid id gl =
  fresh_id_in_env avoid id (pf_env gl)

let new_fresh_id avoid id gl =
  fresh_id_in_env avoid id (Proofview.Goal.env gl)

let id_of_name_with_default id = function
  | Anonymous -> id
  | Name id   -> id

let default_id_of_sort s =
  if Sorts.is_small s then default_small_ident else default_type_ident

let default_id env sigma = function
  | (name,None,t) ->
      let dft = default_id_of_sort (Retyping.get_sort_of env sigma t) in
      id_of_name_with_default dft name
  | (name,Some b,_) -> id_of_name_using_hdchar env b name

(* Non primitive introduction tactics are treated by intro_then_gen
   There is possibly renaming, with possibly names to avoid and
   possibly a move to do after the introduction *)

type name_flag =
  | NamingAvoid of Id.t list
  | NamingBasedOn of Id.t * Id.t list
  | NamingMustBe of Loc.t * Id.t

let naming_of_name = function
  | Anonymous -> NamingAvoid []
  | Name id -> NamingMustBe (dloc,id)

let find_name mayrepl decl naming gl = match naming with
  | NamingAvoid idl ->
      (* this case must be compatible with [find_intro_names] below. *)
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      new_fresh_id idl (default_id env sigma decl) gl
  | NamingBasedOn (id,idl) ->  new_fresh_id idl id gl
  | NamingMustBe (loc,id) ->
      (* When name is given, we allow to hide a global name *)
      let ids_of_hyps = Tacmach.New.pf_ids_of_hyps gl in
      let id' = next_ident_away id ids_of_hyps in
      if not mayrepl && not (Id.equal id' id) then
        user_err_loc (loc,"",pr_id id ++ str" is already used.");
      id

(**************************************************************)
(*            Cut rule                                        *)
(**************************************************************)

let assert_before_then_gen b naming t tac =
  Proofview.Goal.enter begin fun gl ->
    let id = find_name b (Anonymous,None,t) naming gl in
    Tacticals.New.tclTHENLAST
      (Proofview.V82.tactic
         (fun gl ->
           try internal_cut b id t gl
           with Evarutil.ClearDependencyError (id,err) ->
             error_replacing_dependency (pf_env gl) (project gl) id err))
      (tac id)
  end

let assert_before_gen b naming t =
  assert_before_then_gen b naming t (fun _ -> Proofview.tclUNIT ())

let assert_before na = assert_before_gen false (naming_of_name na)
let assert_before_replacing id = assert_before_gen true (NamingMustBe (dloc,id))

let assert_after_then_gen b naming t tac =
  Proofview.Goal.enter begin fun gl ->
    let id = find_name b (Anonymous,None,t) naming gl in
    Tacticals.New.tclTHENFIRST
      (Proofview.V82.tactic
         (fun gl ->
           try internal_cut_rev b id t gl
           with Evarutil.ClearDependencyError (id,err) ->
             error_replacing_dependency (pf_env gl) (project gl) id err))
      (tac id)
  end

let assert_after_gen b naming t =
  assert_after_then_gen b naming t (fun _ -> (Proofview.tclUNIT ()))

let assert_after na = assert_after_gen false (naming_of_name na)
let assert_after_replacing id = assert_after_gen true (NamingMustBe (dloc,id))

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
      if where == InHypValueOnly then
	errorlabstrm "" (pr_id id ++ str "has no value.");
      (id,None,redfun' ty)
  | Some b ->
      let b' = if where != InHypTypeOnly then redfun' b else b in
      let ty' =	if where != InHypValueOnly then redfun' ty else ty in
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
    | Unfold l -> List.exists (fun (occl,_) -> occl != AllOccurrences) l
    | Pattern l -> List.exists (fun (occl,_) -> occl != AllOccurrences) l
    | Simpl (_,Some (occl,_)) -> occl != AllOccurrences
    | _ -> false in
  if occs == AllOccurrences then
    if nbcl > 1 && has_at_clause redexp then
      error_illegal_non_atomic_clause ()
    else
      redexp
  else
    match redexp with
    | Unfold (_::_::_) ->
	error_illegal_clause ()
    | Unfold [(occl,c)] ->
	if occl != AllOccurrences then
	  error_illegal_clause ()
	else
	  Unfold [(occs,c)]
    | Pattern (_::_::_) ->
	error_illegal_clause ()
    | Pattern [(occl,c)] ->
	if occl != AllOccurrences then
	  error_illegal_clause ()
	else
	  Pattern [(occs,c)]
    | Simpl (f,Some (occl,c)) ->
	if occl != AllOccurrences then
	  error_illegal_clause ()
	else
	  Simpl (f,Some (occs,c))
    | CbvVm (Some (occl,c)) ->
        if occl != AllOccurrences then
          error_illegal_clause ()
        else
          CbvVm (Some (occs,c))
    | CbvNative (Some (occl,c)) ->
        if occl != AllOccurrences then
          error_illegal_clause ()
        else
          CbvNative (Some (occs,c))
    | Red _ | Hnf | Cbv _ | Lazy _ | Cbn _
    | ExtraRedExpr _ | Fold _ | Simpl (_,None) | CbvVm None | CbvNative None ->
	error_occurrences_not_unsupported ()
    | Unfold [] | Pattern [] ->
	assert false

(* The following two tactics apply an arbitrary
   reduction function either to the conclusion or to a
   certain hypothesis *)

let reduct_in_concl (redfun,sty) gl =
  Proofview.V82.of_tactic (convert_concl_no_check (pf_reduce redfun gl (pf_concl gl)) sty) gl

let reduct_in_hyp ?(check=false) redfun (id,where) gl =
  Proofview.V82.of_tactic (convert_hyp ~check
    (pf_reduce_decl redfun where (pf_get_hyp gl id) gl)) gl

let revert_cast (redfun,kind as r) =
  if kind == DEFAULTcast then (redfun,REVERTcast) else r

let reduct_option ?(check=false) redfun = function
  | Some id -> reduct_in_hyp ~check (fst redfun) id
  | None    -> reduct_in_concl (revert_cast redfun)

(** Tactic reduction modulo evars (for universes essentially) *)

let pf_e_reduce_decl redfun where (id,c,ty) gl =
  let sigma = project gl in
  let redfun = redfun (pf_env gl) in
  match c with
  | None ->
      if where == InHypValueOnly then
	errorlabstrm "" (pr_id id ++ str "has no value.");
    let sigma, ty' = redfun sigma ty in
      sigma, (id,None,ty')
  | Some b ->
      let sigma, b' = if where != InHypTypeOnly then redfun sigma b else sigma, b in
      let sigma, ty' = if where != InHypValueOnly then redfun sigma ty else sigma, ty in
	sigma, (id,Some b',ty')

let e_reduct_in_concl (redfun,sty) gl =
  Proofview.V82.of_tactic
    (let sigma, c' = (pf_apply redfun gl (pf_concl gl)) in
       Proofview.Unsafe.tclEVARS sigma <*> 
	 convert_concl_no_check c' sty) gl

let e_reduct_in_hyp ?(check=false) redfun (id,where) gl =
  Proofview.V82.of_tactic 
    (let sigma, decl' = pf_e_reduce_decl redfun where (pf_get_hyp gl id) gl in
       Proofview.Unsafe.tclEVARS sigma <*> 
	 convert_hyp ~check decl') gl

let e_reduct_option ?(check=false) redfun = function
  | Some id -> e_reduct_in_hyp ~check (fst redfun) id
  | None    -> e_reduct_in_concl (revert_cast redfun)

(** Versions with evars to maintain the unification of universes resulting
    from conversions. *)

let tclWITHEVARS f k =
  Proofview.Goal.enter begin fun gl ->
  let evm, c' = f gl in
  Tacticals.New.tclTHEN (Proofview.Unsafe.tclEVARS evm) (k c')
  end

let e_change_in_concl (redfun,sty) =
  tclWITHEVARS
    (fun gl -> redfun (Proofview.Goal.env gl) (Proofview.Goal.sigma gl)
        (Proofview.Goal.raw_concl gl))
    (fun c -> convert_concl_no_check c sty)

let e_pf_change_decl (redfun : bool -> e_reduction_function) where (id,c,ty) env sigma =
  match c with
  | None ->
      if where == InHypValueOnly then
	errorlabstrm "" (pr_id id ++ str "has no value.");
    let sigma',ty' = redfun false env sigma ty in
      sigma', (id,None,ty')
  | Some b ->
      let sigma',b' = if where != InHypTypeOnly then redfun true env sigma b else sigma, b in
      let sigma',ty' = if where != InHypValueOnly then redfun false env sigma ty else sigma', ty in
	sigma', (id,Some b',ty')

let e_change_in_hyp redfun (id,where) =
  tclWITHEVARS
    (fun gl -> e_pf_change_decl redfun where
      (Tacmach.New.pf_get_hyp id (Proofview.Goal.assume gl))
      (Proofview.Goal.env gl) (Proofview.Goal.sigma gl))
    convert_hyp

type change_arg = evar_map -> evar_map * constr

let check_types env sigma mayneedglobalcheck deep newc origc =
  let t1 = Retyping.get_type_of env sigma newc in
  if deep then begin
    let t2 = Retyping.get_type_of env sigma origc in
    let sigma, t2 = Evarsolve.refresh_universes ~onlyalg:true (Some false) env sigma t2 in
    if not (snd (infer_conv ~pb:Reduction.CUMUL env sigma t1 t2)) then
      if
        isSort (whd_betadeltaiota env sigma t1) &&
        isSort (whd_betadeltaiota env sigma t2)
      then
        mayneedglobalcheck := true
      else
        errorlabstrm "convert-check-hyp" (str "Types are incompatible.")
  end
  else
    if not (isSort (whd_betadeltaiota env sigma t1)) then
      errorlabstrm "convert-check-hyp" (str "Not a type.")

(* Now we introduce different instances of the previous tacticals *)
let change_and_check cv_pb mayneedglobalcheck deep t env sigma c =
  let sigma, t' = t sigma in
  check_types env sigma mayneedglobalcheck deep t' c;
  let sigma, b = infer_conv ~pb:cv_pb env sigma t' c in
  if not b then errorlabstrm "convert-check-hyp" (str "Not convertible.");
  sigma, t'

let change_and_check_subst cv_pb mayneedglobalcheck subst t env sigma c =
  let t' sigma =
    let sigma, t = t sigma in
      sigma, replace_vars (Id.Map.bindings subst) t 
  in change_and_check cv_pb mayneedglobalcheck true t' env sigma c

(* Use cumulativity only if changing the conclusion not a subterm *)
let change_on_subterm cv_pb deep t where env sigma c =
  let mayneedglobalcheck = ref false in
  let sigma,c = match where with
  | None -> change_and_check cv_pb mayneedglobalcheck deep t env sigma c
  | Some occl ->
      e_contextually false occl
        (fun subst ->
          change_and_check_subst Reduction.CONV mayneedglobalcheck subst t)
        env sigma c in
  if !mayneedglobalcheck then
    begin
      try ignore (Typing.type_of env sigma c)
      with e when catchable_exception e ->
        error "Replacement would lead to an ill-typed term."
    end;
  sigma,c

let change_in_concl occl t =
  e_change_in_concl ((change_on_subterm Reduction.CUMUL false t occl),DEFAULTcast)

let change_in_hyp occl t id  =
  e_change_in_hyp (fun x -> change_on_subterm Reduction.CONV x t occl) id

let change_option occl t = function
  | Some id -> change_in_hyp occl t id
  | None -> change_in_concl occl t

let change chg c cls gl =
  let cls = concrete_clause_of (fun () -> pf_ids_of_hyps gl) cls in
  Proofview.V82.of_tactic (Tacticals.New.tclMAP (function
    | OnHyp (id,occs,where) ->
       change_option (bind_change_occurrences occs chg) c (Some (id,where))
    | OnConcl occs ->
       change_option (bind_change_occurrences occs chg) c None)
    cls) gl

let change_concl t = 
  change_in_concl None (fun sigma -> sigma, t)

(* Pour usage interne (le niveau User est pris en compte par reduce) *)
let red_in_concl        = reduct_in_concl (red_product,REVERTcast)
let red_in_hyp          = reduct_in_hyp    red_product
let red_option          = reduct_option   (red_product,REVERTcast)
let hnf_in_concl        = reduct_in_concl (hnf_constr,REVERTcast)
let hnf_in_hyp          = reduct_in_hyp    hnf_constr
let hnf_option          = reduct_option   (hnf_constr,REVERTcast)
let simpl_in_concl      = reduct_in_concl (simpl,REVERTcast)
let simpl_in_hyp        = reduct_in_hyp    simpl
let simpl_option        = reduct_option   (simpl,REVERTcast)
let normalise_in_concl  = reduct_in_concl (compute,REVERTcast)
let normalise_in_hyp    = reduct_in_hyp    compute
let normalise_option    = reduct_option   (compute,REVERTcast)
let normalise_vm_in_concl = reduct_in_concl (Redexpr.cbv_vm,VMcast)
let unfold_in_concl loccname = reduct_in_concl (unfoldn loccname,REVERTcast)
let unfold_in_hyp   loccname = reduct_in_hyp   (unfoldn loccname)
let unfold_option   loccname = reduct_option (unfoldn loccname,DEFAULTcast)
let pattern_option l = e_reduct_option (pattern_occs l,DEFAULTcast)

(* The main reduction function *)

let reduction_clause redexp cl =
  let nbcl = List.length cl in
  List.map (function
    | OnHyp (id,occs,where) ->
	(Some (id,where), bind_red_expr_occurrences occs nbcl redexp)
    | OnConcl occs ->
	(None, bind_red_expr_occurrences occs nbcl redexp)) cl

let reduce redexp cl goal =
  let cl = concrete_clause_of (fun () -> pf_ids_of_hyps goal) cl in
  let redexps = reduction_clause redexp cl in
  let tac = tclMAP (fun (where,redexp) ->
    e_reduct_option ~check:true
      (Redexpr.reduction_of_red_expr (pf_env goal) redexp) where) redexps in
  match redexp with
  | Fold _ | Pattern _ -> with_check tac goal
  | _ -> tac goal

(* Unfolding occurrences of a constant *)

let unfold_constr = function
  | ConstRef sp -> unfold_in_concl [AllOccurrences,EvalConstRef sp]
  | VarRef id -> unfold_in_concl [AllOccurrences,EvalVarRef id]
  | _ -> errorlabstrm "unfold_constr" (str "Cannot unfold a non-constant.")

(*******************************************)
(*         Introduction tactics            *)
(*******************************************)

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

let build_intro_tac id dest tac = match dest with
  | MoveLast -> Tacticals.New.tclTHEN (introduction id) (tac id)
  | dest -> Tacticals.New.tclTHENLIST 
    [introduction id; 
     Proofview.V82.tactic (move_hyp id dest); tac id]
    
let rec intro_then_gen name_flag move_flag force_flag dep_flag tac =
  Proofview.Goal.enter begin fun gl ->
    let concl = Proofview.Goal.concl (Proofview.Goal.assume gl) in
    let concl = nf_evar (Proofview.Goal.sigma gl) concl in
    match kind_of_term concl with
    | Prod (name,t,u) when not dep_flag || (dependent (mkRel 1) u) ->
        let name = find_name false (name,None,t) name_flag gl in
	build_intro_tac name move_flag tac
    | LetIn (name,b,t,u) when not dep_flag || (dependent (mkRel 1) u) ->
        let name = find_name false (name,Some b,t) name_flag gl in
	build_intro_tac name move_flag tac
    | _ ->
	begin if not force_flag then Proofview.tclZERO (RefinerError IntroNeedsProduct)
            (* Note: red_in_concl includes betaiotazeta and this was like *)
            (* this since at least V6.3 (a pity *)
            (* that intro do betaiotazeta only when reduction is needed; and *)
            (* probably also a pity that intro does zeta *)
          else Proofview.tclUNIT ()
        end <*>
	  Proofview.tclORELSE
	  (Tacticals.New.tclTHEN (Proofview.V82.tactic hnf_in_concl)
	     (intro_then_gen name_flag move_flag false dep_flag tac))
          begin function (e, info) -> match e with
            | RefinerError IntroNeedsProduct ->
                Proofview.tclZERO 
		  (Errors.UserError("Intro",str "No product even after head-reduction."))
            | e -> Proofview.tclZERO ~info e
          end
  end

let intro_gen n m f d = intro_then_gen n m f d (fun _ -> Proofview.tclUNIT ())
let intro_mustbe_force id = intro_gen (NamingMustBe (dloc,id)) MoveLast true false
let intro_using id = intro_gen (NamingBasedOn (id,[])) MoveLast false false

let intro_then = intro_then_gen (NamingAvoid []) MoveLast false false
let intro = intro_gen (NamingAvoid []) MoveLast false false
let introf = intro_gen (NamingAvoid []) MoveLast true false
let intro_avoiding l = intro_gen (NamingAvoid l) MoveLast false false

let intro_then_force = intro_then_gen (NamingAvoid []) MoveLast true false

let intro_move_avoid idopt avoid hto = match idopt with
  | None -> intro_gen (NamingAvoid avoid) hto true false
  | Some id -> intro_gen (NamingMustBe (dloc,id)) hto true false

let intro_move idopt hto = intro_move_avoid idopt [] hto

(**** Multiple introduction tactics ****)

let rec intros_using = function
  | []     -> Proofview.tclUNIT()
  | str::l -> Tacticals.New.tclTHEN (intro_using str) (intros_using l)

let intros = Tacticals.New.tclREPEAT intro

let intro_forthcoming_then_gen name_flag move_flag dep_flag n bound tac =
  let rec aux n ids =
    (* Note: we always use the bound when there is one for "*" and "**" *)
    if (match bound with None -> true | Some (_,p) -> n < p) then
    Proofview.tclORELSE
      begin
      intro_then_gen name_flag move_flag false dep_flag
         (fun id -> aux (n+1) (id::ids))
      end
      begin function (e, info) -> match e with
      | RefinerError IntroNeedsProduct ->
          tac ids
      | e -> Proofview.tclZERO ~info e
      end
    else
      tac ids
  in
  aux n []

let get_next_hyp_position id gl =
  let rec get_next_hyp_position id = function
  | [] -> raise (RefinerError (NoSuchHyp id))
  | (hyp,_,_) :: right ->
    if Id.equal hyp id then
      match right with (id,_,_)::_ -> MoveBefore id | [] -> MoveLast
    else
      get_next_hyp_position id right
  in
  let hyps = Proofview.Goal.hyps (Proofview.Goal.assume gl) in
  get_next_hyp_position id hyps

let intro_replacing id =
  Proofview.Goal.enter begin fun gl ->
  let next_hyp = get_next_hyp_position id gl in
  Tacticals.New.tclTHENLIST [
    Proofview.V82.tactic (thin_for_replacing [id]);
    introduction id;
    Proofview.V82.tactic (move_hyp id next_hyp);
  ]
  end

(* We have e.g. [x, y, y', x', y'' |- forall y y' y'', G] and want to
   reintroduce y, y,' y''. Note that we have to clear y, y' and y''
   before introducing y because y' or y'' can e.g. depend on old y. *)

(* This version assumes that replacement is actually possible *)
(* (ids given in the introduction order) *)
(* We keep a sub-optimality in cleaing for compatibility with *)
(* the behavior of inversion *)
let intros_possibly_replacing ids =
  let suboptimal = true in
  Proofview.Goal.enter begin fun gl ->
    let posl = List.map (fun id -> (id, get_next_hyp_position id gl)) ids in
    Tacticals.New.tclTHEN
      (Tacticals.New.tclMAP (fun id -> 
	Tacticals.New.tclTRY (Proofview.V82.tactic (thin_for_replacing [id])))
	 (if suboptimal then ids else List.rev ids))
      (Tacticals.New.tclMAP (fun (id,pos) ->
        Tacticals.New.tclORELSE (intro_move (Some id) pos) (intro_using id))
         posl)
  end

(* This version assumes that replacement is actually possible *)
let intros_replacing ids =
  Proofview.Goal.enter begin fun gl ->
    let posl = List.map (fun id -> (id, get_next_hyp_position id gl)) ids in
    Tacticals.New.tclTHEN
      (Proofview.V82.tactic (thin_for_replacing ids))
      (Tacticals.New.tclMAP (fun (id,pos) -> intro_move (Some id) pos) posl)
  end

(* User-level introduction tactics *)

let pf_lookup_hypothesis_as_renamed env ccl = function
  | AnonHyp n -> Detyping.lookup_index_as_renamed env ccl n
  | NamedHyp id -> Detyping.lookup_name_as_displayed env ccl id

let pf_lookup_hypothesis_as_renamed_gen red h gl =
  let env = pf_env gl in
  let rec aux ccl =
    match pf_lookup_hypothesis_as_renamed env ccl h with
      | None when red ->
          aux
	    (snd ((fst (Redexpr.reduction_of_red_expr env (Red true)))
	       env (project gl) ccl))
      | x -> x
  in
  try aux (pf_concl gl)
  with Redelimination -> None

let is_quantified_hypothesis id g =
  match pf_lookup_hypothesis_as_renamed_gen false (NamedHyp id) g with
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

let intros_until_gen red h =
  Proofview.Goal.nf_enter begin fun gl ->
  let n = Tacmach.New.of_old (depth_of_quantified_hypothesis red h) gl in
  Tacticals.New.tclDO n (if red then introf else intro)
  end

let intros_until_id id = intros_until_gen false (NamedHyp id)
let intros_until_n_gen red n = intros_until_gen red (AnonHyp n)

let intros_until = intros_until_gen true
let intros_until_n = intros_until_n_gen true

let tclCHECKVAR id gl = ignore (pf_get_hyp gl id); tclIDTAC gl

let try_intros_until_id_check id =
  Tacticals.New.tclORELSE (intros_until_id id) (Proofview.V82.tactic (tclCHECKVAR id))

let try_intros_until tac = function
  | NamedHyp id -> Tacticals.New.tclTHEN (try_intros_until_id_check id) (tac id)
  | AnonHyp n -> Tacticals.New.tclTHEN (intros_until_n n) (Tacticals.New.onLastHypId tac)

let rec intros_move = function
  | [] -> Proofview.tclUNIT ()
  | (hyp,destopt) :: rest ->
      Tacticals.New.tclTHEN (intro_gen (NamingMustBe (dloc,hyp)) destopt false false)
	(intros_move rest)

(* Apply a tactic on a quantified hypothesis, an hypothesis in context
   or a term with bindings *)

let onOpenInductionArg env sigma tac = function
  | clear_flag,ElimOnConstr f ->
      let (sigma',cbl) = f env sigma in
      let pending = (sigma,sigma') in
      Tacticals.New.tclTHEN
        (Proofview.Unsafe.tclEVARS sigma')
        (tac clear_flag (pending,cbl))
  | clear_flag,ElimOnAnonHyp n ->
      Tacticals.New.tclTHEN
        (intros_until_n n)
        (Tacticals.New.onLastHyp
           (fun c ->
             Proofview.Goal.enter begin fun gl ->
             let sigma = Proofview.Goal.sigma gl in
             let pending = (sigma,sigma) in
             tac clear_flag (pending,(c,NoBindings))
             end))
  | clear_flag,ElimOnIdent (_,id) ->
      (* A quantified hypothesis *)
      Tacticals.New.tclTHEN
        (try_intros_until_id_check id)
        (Proofview.Goal.enter begin fun gl ->
         let sigma = Proofview.Goal.sigma gl in
         let pending = (sigma,sigma) in
         tac clear_flag (pending,(mkVar id,NoBindings))
        end)

let onInductionArg tac = function
  | clear_flag,ElimOnConstr cbl ->
      tac clear_flag cbl
  | clear_flag,ElimOnAnonHyp n ->
      Tacticals.New.tclTHEN
        (intros_until_n n)
        (Tacticals.New.onLastHyp (fun c -> tac clear_flag (c,NoBindings)))
  | clear_flag,ElimOnIdent (_,id) ->
      (* A quantified hypothesis *)
      Tacticals.New.tclTHEN
        (try_intros_until_id_check id)
        (tac clear_flag (mkVar id,NoBindings))

let map_induction_arg f = function
  | clear_flag,ElimOnConstr g -> clear_flag,ElimOnConstr (f g)
  | clear_flag,ElimOnAnonHyp n as x -> x
  | clear_flag,ElimOnIdent id as x -> x

(****************************************)
(* tactic "cut" (actually modus ponens) *)
(****************************************)

let cut c =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let concl = Tacmach.New.pf_nf_concl gl in
    let is_sort =
      try
        (** Backward compat: ensure that [c] is well-typed. *)
        let typ = Typing.type_of env sigma c in
        let typ = whd_betadeltaiota env sigma typ in
        match kind_of_term typ with
        | Sort _ -> true
        | _ -> false
      with e when Pretype_errors.precatchable_exception e -> false
    in
    if is_sort then
      let id = next_name_away_with_default "H" Anonymous (Tacmach.New.pf_ids_of_hyps gl) in
      (** Backward compat: normalize [c]. *)
      let c = local_strong whd_betaiota sigma c in
      Proofview.Refine.refine ~unsafe:true begin fun h ->
        let (h, f) = Evarutil.new_evar ~principal:true env h (mkArrow c (Vars.lift 1 concl)) in
        let (h, x) = Evarutil.new_evar env h c in
        let f = mkLambda (Name id, c, mkApp (Vars.lift 1 f, [|mkRel 1|])) in
        (h, mkApp (f, [|x|]))
      end
    else
      Tacticals.New.tclZEROMSG (str "Not a proposition or a type.")
  end

let error_uninstantiated_metas t clenv =
  let na = meta_name clenv.evd (List.hd (Metaset.elements (metavars_of t))) in
  let id = match na with Name id -> id | _ -> anomaly (Pp.str "unnamed dependent meta")
  in errorlabstrm "" (str "Cannot find an instance for " ++ pr_id id ++ str".")

let check_unresolved_evars_of_metas sigma clenv =
  (* This checks that Metas turned into Evars by *)
  (* Refiner.pose_all_metas_as_evars are resolved *)
  List.iter (fun (mv,b) -> match b with
  | Clval (_,(c,_),_) ->
    (match kind_of_term c.rebus with
    | Evar (evk,_) when Evd.is_undefined clenv.evd evk
                     && not (Evd.mem sigma evk) ->
      error_uninstantiated_metas (mkMeta mv) clenv
    | _ -> ())
  | _ -> ())
  (meta_list clenv.evd)

let do_replace id = function
  | NamingMustBe (_,id') when Option.equal Id.equal id (Some id') -> true
  | _ -> false

(* For a clenv expressing some lemma [C[?1:T1,...,?n:Tn] : P] and some
   goal [G], [clenv_refine_in] returns [n+1] subgoals, the [n] last
   ones (resp [n] first ones if [sidecond_first] is [true]) being the
   [Ti] and the first one (resp last one) being [G] whose hypothesis
   [id] is replaced by P using the proof given by [tac] *)

let clenv_refine_in ?(sidecond_first=false) with_evars ?(with_classes=true) 
    targetid id sigma0 clenv tac =
  let clenv = Clenvtac.clenv_pose_dependent_evars with_evars clenv in
  let clenv =
    if with_classes then
      { clenv with evd = Typeclasses.resolve_typeclasses 
	  ~fail:(not with_evars) clenv.env clenv.evd }
    else clenv
  in
  let new_hyp_typ = clenv_type clenv in
  if not with_evars then check_unresolved_evars_of_metas sigma0 clenv;
  if not with_evars && occur_meta new_hyp_typ then
    error_uninstantiated_metas new_hyp_typ clenv;
  let new_hyp_prf = clenv_value clenv in
  let exact_tac = Proofview.V82.tactic (refine_no_check new_hyp_prf) in
  let naming = NamingMustBe (dloc,targetid) in
  let with_clear = do_replace (Some id) naming in
  Tacticals.New.tclTHEN
    (Proofview.Unsafe.tclEVARS clenv.evd)
    (if sidecond_first then
       Tacticals.New.tclTHENFIRST
         (assert_before_then_gen with_clear naming new_hyp_typ tac) exact_tac
     else
       Tacticals.New.tclTHENLAST
         (assert_after_then_gen with_clear naming new_hyp_typ tac) exact_tac)

(********************************************)
(*       Elimination tactics                *)
(********************************************)

let last_arg c = match kind_of_term c with
  | App (f,cl) ->
      Array.last cl
  | _ -> anomaly (Pp.str "last_arg")

let nth_arg i c =
  if Int.equal i (-1) then last_arg c else
  match kind_of_term c with
  | App (f,cl) -> cl.(i)
  | _ -> anomaly (Pp.str "nth_arg")

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

let enforce_prop_bound_names rename tac =
  match rename with
  | Some (isrec,nn) when Namegen.use_h_based_elimination_names () ->
      (* Rename dependent arguments in Prop with name "H" *)
      (* so as to avoid having hypothesis such as "t:True", "n:~A" when calling *)
      (* elim or induction with schemes built by Indrec.build_induction_scheme *)
      let rec aux env sigma i t =
        if i = 0 then t else match kind_of_term t with
        | Prod (Name _ as na,t,t') ->
            let very_standard = true in
            let na =
              if Retyping.get_sort_family_of env sigma t = InProp then
                (* "very_standard" says that we should have "H" names only, but
                   this would break compatibility even more... *)
                let s = match Namegen.head_name t with
                  | Some id when not very_standard -> string_of_id id
                  | _ -> "" in
                Name (add_suffix Namegen.default_prop_ident s)
              else
                na in
            mkProd (na,t,aux (push_rel (na,None,t) env) sigma (i-1) t')
        | Prod (Anonymous,t,t') ->
            mkProd (Anonymous,t,aux (push_rel (Anonymous,None,t) env) sigma (i-1) t')
        | LetIn (na,c,t,t') ->
            mkLetIn (na,c,t,aux (push_rel (na,Some c,t) env) sigma (i-1) t')
        | _ -> print_int i; Pp.msg (print_constr t); assert false in
      let rename_branch i =
        Proofview.Goal.nf_enter begin fun gl ->
          let env = Proofview.Goal.env gl in
          let sigma = Proofview.Goal.sigma gl in
          let t = Proofview.Goal.concl gl in
          change_concl (aux env sigma i t)
        end in
      (if isrec then Tacticals.New.tclTHENFIRSTn else Tacticals.New.tclTHENLASTn)
        tac
        (Array.map rename_branch nn)
  | _ ->
      tac

let elimination_clause_scheme with_evars ?(with_classes=true) ?(flags=elim_flags ()) 
    rename i (elim, elimty, bindings) indclause =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let elimclause = make_clenv_binding env sigma (elim, elimty) bindings in
  let indmv =
    (match kind_of_term (nth_arg i elimclause.templval.rebus) with
       | Meta mv -> mv
       | _  -> errorlabstrm "elimination_clause"
             (str "The type of elimination clause is not well-formed."))
  in
  let elimclause' = clenv_fchain ~flags indmv elimclause indclause in
  enforce_prop_bound_names rename (Clenvtac.res_pf elimclause' ~with_evars ~with_classes ~flags)
  end

(*
 * Elimination tactic with bindings and using an arbitrary
 * elimination constant called elimc. This constant should end
 * with a clause (x:I)(P .. ), where P is a bound variable.
 * The term c is of type t, which is a product ending with a type
 * matching I, lbindc are the expected terms for c arguments
 *)

type eliminator = {
  elimindex : int option;  (* None = find it automatically *)
  elimrename : (bool * int array) option; (** None = don't rename Prop hyps with H-names *)
  elimbody : constr with_bindings
}

let general_elim_clause_gen elimtac indclause elim =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let (elimc,lbindelimc) = elim.elimbody in
  let elimt = Retyping.get_type_of env sigma elimc in
  let i =
    match elim.elimindex with None -> index_of_ind_arg elimt | Some i -> i in
  elimtac elim.elimrename i (elimc, elimt, lbindelimc) indclause
  end

let general_elim with_evars clear_flag (c, lbindc) elim =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let ct = Retyping.get_type_of env sigma c in
  let t = try snd (reduce_to_quantified_ind env sigma ct) with UserError _ -> ct in
  let elimtac = elimination_clause_scheme with_evars in
  let indclause  = make_clenv_binding env sigma (c, t) lbindc in
  Tacticals.New.tclTHEN
    (general_elim_clause_gen elimtac indclause elim)
    (apply_clear_request clear_flag (use_clear_hyp_by_default ()) c)
  end

(* Case analysis tactics *)

let general_case_analysis_in_context with_evars clear_flag (c,lbindc) =
  Proofview.Goal.nf_enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in
  let t = Retyping.get_type_of env sigma c in
  let (mind,_) = reduce_to_quantified_ind env sigma t in
  let sort = Tacticals.New.elimination_sort_of_goal gl in
  let sigma, elim =
    if occur_term c concl then
      build_case_analysis_scheme env sigma mind true sort
    else
      build_case_analysis_scheme_default env sigma mind sort in
  Tacticals.New.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
  (general_elim with_evars clear_flag (c,lbindc)
   {elimindex = None; elimbody = (elim,NoBindings);
    elimrename = Some (false, constructors_nrealdecls (fst mind))})
  end

let general_case_analysis with_evars clear_flag (c,lbindc as cx) =
  match kind_of_term c with
    | Var id when lbindc == NoBindings ->
	Tacticals.New.tclTHEN (try_intros_until_id_check id)
	  (general_case_analysis_in_context with_evars clear_flag cx)
    | _ ->
        general_case_analysis_in_context with_evars clear_flag cx

let simplest_case c = general_case_analysis false None (c,NoBindings)

(* Elimination tactic with bindings but using the default elimination
 * constant associated with the type. *)

exception IsNonrec

let is_nonrec mind = (Global.lookup_mind (fst mind)).mind_finite == Decl_kinds.BiFinite

let find_ind_eliminator ind s gl =
  let gr = lookup_eliminator ind s in
  let evd, c = Tacmach.New.pf_apply Evd.fresh_global gl gr in
    evd, c

let find_eliminator c gl =
  let ((ind,u),t) = Tacmach.New.pf_reduce_to_quantified_ind gl (Tacmach.New.pf_type_of gl c) in
  if is_nonrec ind then raise IsNonrec;
  let evd, c = find_ind_eliminator ind (Tacticals.New.elimination_sort_of_goal gl) gl in
    evd, {elimindex = None; elimbody = (c,NoBindings);
          elimrename = Some (true, constructors_nrealdecls ind)}

let default_elim with_evars clear_flag (c,_ as cx) =
  Proofview.tclORELSE
    (Proofview.Goal.enter begin fun gl ->
      let evd, elim = find_eliminator c gl in
	Tacticals.New.tclTHEN (Proofview.Unsafe.tclEVARS evd)
	  (general_elim with_evars clear_flag cx elim)
    end)
    begin function (e, info) -> match e with
      | IsNonrec ->
          (* For records, induction principles aren't there by default
             anymore.  Instead, we do a case analysis instead. *)
          general_case_analysis with_evars clear_flag cx
      | e -> Proofview.tclZERO ~info e
    end

let elim_in_context with_evars clear_flag c = function
  | Some elim ->
      general_elim with_evars clear_flag c
        {elimindex = Some (-1); elimbody = elim; elimrename = None}
  | None -> default_elim with_evars clear_flag c

let elim with_evars clear_flag (c,lbindc as cx) elim =
  match kind_of_term c with
    | Var id when lbindc == NoBindings ->
	Tacticals.New.tclTHEN (try_intros_until_id_check id)
	  (elim_in_context with_evars clear_flag cx elim)
    | _ ->
	elim_in_context with_evars clear_flag cx elim

(* The simplest elimination tactic, with no substitutions at all. *)

let simplest_elim c = default_elim false None (c,NoBindings)

(* Elimination in hypothesis *)
(* Typically, elimclause := (eq_ind ?x ?P ?H ?y ?Heq : ?P ?y)
              indclause : forall ..., hyps -> a=b    (to take place of ?Heq)
              id : phi(a)                            (to take place of ?H)
      and the result is to overwrite id with the proof of phi(b)

   but this generalizes to any elimination scheme with one constructor
   (e.g. it could replace id:A->B->C by id:C, knowing A/\B)
*)

let clenv_fchain_in id ?(flags=elim_flags ()) mv elimclause hypclause =
  try clenv_fchain ~flags mv elimclause hypclause
  with PretypeError (env,evd,NoOccurrenceFound (op,_)) ->
    (* Set the hypothesis name in the message *)
    raise (PretypeError (env,evd,NoOccurrenceFound (op,Some id)))

let elimination_in_clause_scheme with_evars ?(flags=elim_flags ()) 
    id rename i (elim, elimty, bindings) indclause =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let elimclause = make_clenv_binding env sigma (elim, elimty) bindings in
  let indmv = destMeta (nth_arg i elimclause.templval.rebus) in
  let hypmv =
    try match List.remove Int.equal indmv (clenv_independent elimclause) with
      | [a] -> a
      | _ -> failwith ""
    with Failure _ -> errorlabstrm "elimination_clause"
          (str "The type of elimination clause is not well-formed.") in
  let elimclause'  = clenv_fchain ~flags indmv elimclause indclause in
  let hyp = mkVar id in
  let hyp_typ = Retyping.get_type_of env sigma hyp in
  let hypclause = mk_clenv_from_env env sigma (Some 0) (hyp, hyp_typ) in
  let elimclause'' = clenv_fchain_in id ~flags hypmv elimclause' hypclause in
  let new_hyp_typ  = clenv_type elimclause'' in
  if Term.eq_constr hyp_typ new_hyp_typ then
    errorlabstrm "general_rewrite_in"
      (str "Nothing to rewrite in " ++ pr_id id ++ str".");
  clenv_refine_in with_evars id id sigma elimclause''
    (fun id -> Proofview.tclUNIT ())
  end

let general_elim_clause with_evars flags id c e =
  let elim = match id with
  | None -> elimination_clause_scheme with_evars ~with_classes:true ~flags
  | Some id -> elimination_in_clause_scheme with_evars ~flags id
  in
  general_elim_clause_gen elim c e

(* Apply a tactic below the products of the conclusion of a lemma *)

type conjunction_status =
  | DefinedRecord of constant option list
  | NotADefinedRecordUseScheme of constr

let make_projection env sigma params cstr sign elim i n c u =
  let elim = match elim with
  | NotADefinedRecordUseScheme elim ->
      (* bugs: goes from right to left when i increases! *)
      let (na,b,t) = List.nth cstr.cs_args i in
      let b = match b with None -> mkRel (i+1) | Some b -> b in
      let branch = it_mkLambda_or_LetIn b cstr.cs_args in
      if
	(* excludes dependent projection types *)
	noccur_between 1 (n-i-1) t
	(* to avoid surprising unifications, excludes flexible
	projection types or lambda which will be instantiated by Meta/Evar *)
	&& not (isEvar (fst (whd_betaiota_stack sigma t)))
	&& not (isRel t && destRel t > n-i)
      then
        let t = lift (i+1-n) t in
	let abselim = beta_applist (elim,params@[t;branch]) in
	let c = beta_applist (abselim, [mkApp (c, extended_rel_vect 0 sign)]) in
	  Some (it_mkLambda_or_LetIn c sign, it_mkProd_or_LetIn t sign)
      else
	None
  | DefinedRecord l ->
      (* goes from left to right when i increases! *)
      match List.nth l i with
      | Some proj ->
	  let args = extended_rel_vect 0 sign in
	  let proj =
	    if Environ.is_projection proj env then
	      mkProj (Projection.make proj false, mkApp (c, args))
	    else
	      mkApp (mkConstU (proj,u), Array.append (Array.of_list params)
		[|mkApp (c, args)|])
	  in
	  let app = it_mkLambda_or_LetIn proj sign in
	  let t = Retyping.get_type_of env sigma app in
	    Some (app, t)
      | None -> None
  in elim

let descend_in_conjunctions avoid tac exit c =
  Proofview.Goal.nf_enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  try
    let t = Retyping.get_type_of env sigma c in
    let ((ind,u),t) = reduce_to_quantified_ind env sigma t in
    let sign,ccl = decompose_prod_assum t in
    match match_with_tuple ccl with
    | Some (_,_,isrec) ->
	let n = (constructors_nrealargs ind).(0) in
	let sort = Tacticals.New.elimination_sort_of_goal gl in
	let IndType (indf,_) = find_rectype env sigma ccl in
	let (_,inst), params = dest_ind_family indf in
	let cstr = (get_constructors env indf).(0) in
	let elim =
	  try DefinedRecord (Recordops.lookup_projections ind)
	  with Not_found ->
	    let elim = build_case_analysis_scheme env sigma (ind,u) false sort in
	    NotADefinedRecordUseScheme (snd elim) in
	Tacticals.New.tclFIRST
	  (List.init n (fun i ->
            Proofview.Goal.enter begin fun gl ->
            let env = Proofview.Goal.env gl in
            let sigma = Proofview.Goal.sigma gl in
	    match make_projection env sigma params cstr sign elim i n c u with
	    | None -> Tacticals.New.tclFAIL 0 (mt())
	    | Some (p,pt) ->
	      Tacticals.New.tclTHENS
		(assert_before_gen false (NamingAvoid avoid) pt)
		[Proofview.V82.tactic (refine p);
		 (* Might be ill-typed due to forbidden elimination. *)
		 Tacticals.New.onLastHypId (tac (not isrec))]
           end))
    | None ->
	raise Exit
  with RefinerError _|UserError _|Exit -> exit ()
  end

(****************************************************)
(*            Resolution tactics                    *)
(****************************************************)

let solve_remaining_apply_goals =
  Proofview.Goal.nf_enter begin fun gl ->
  if !apply_solve_class_goals then
    try 
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let concl = Proofview.Goal.concl gl in
      if Typeclasses.is_class_type sigma concl then
        let evd', c' = Typeclasses.resolve_one_typeclass env sigma concl in
	Tacticals.New.tclTHEN
          (Proofview.Unsafe.tclEVARS evd')
          (Proofview.V82.tactic (refine_no_check c'))
	else Proofview.tclUNIT ()
    with Not_found -> Proofview.tclUNIT ()
  else Proofview.tclUNIT ()
  end
  
let general_apply with_delta with_destruct with_evars clear_flag (loc,(c,lbind)) =
  Proofview.Goal.nf_enter begin fun gl ->
  let concl = Proofview.Goal.concl gl in
  let flags =
    if with_delta then default_unify_flags () else default_no_delta_unify_flags () in
  (* The actual type of the theorem. It will be matched against the
  goal. If this fails, then the head constant will be unfolded step by
  step. *)
  let concl_nprod = nb_prod concl in
  let rec try_main_apply with_destruct c =
    Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in

    let thm_ty0 = nf_betaiota sigma (Retyping.get_type_of env sigma c) in
    let try_apply thm_ty nprod =
      try
        let n = nb_prod thm_ty - nprod in
        if n<0 then error "Applied theorem has not enough premisses.";
        let clause = make_clenv_binding_apply env sigma (Some n) (c,thm_ty) lbind in
        Clenvtac.res_pf clause ~with_evars ~flags
      with UserError _ as exn ->
        Proofview.tclZERO exn
    in
    Proofview.tclORELSE
      (try_apply thm_ty0 concl_nprod)
      (function (e, info) -> match e with
        | PretypeError _|RefinerError _|UserError _|Failure _ as exn0 ->
	let rec try_red_apply thm_ty =
          try 
            (* Try to head-reduce the conclusion of the theorem *)
            let red_thm = try_red_product env sigma thm_ty in
            Proofview.tclORELSE
              (try_apply red_thm concl_nprod)
              (function (e, info) -> match e with
              | PretypeError _|RefinerError _|UserError _|Failure _ ->
		try_red_apply red_thm
              | exn -> iraise (exn, info))
          with Redelimination ->
            (* Last chance: if the head is a variable, apply may try
	       second order unification *)
            let tac =
	      if with_destruct then
                descend_in_conjunctions []
                  (fun b id ->
                    Tacticals.New.tclTHEN
                      (try_main_apply b (mkVar id))
                      (Proofview.V82.tactic (thin [id])))
                  (fun _ ->
                    let info = Loc.add_loc info loc in
                    Proofview.tclZERO ~info exn0) c
	      else
                let info = Loc.add_loc info loc in
		Proofview.tclZERO ~info exn0 in
            if not (Int.equal concl_nprod 0) then
              try
                Proofview.tclORELSE
                  (try_apply thm_ty 0)
                  (function (e, info) -> match e with
                  | PretypeError _|RefinerError _|UserError _|Failure _->
                    tac
                  | exn -> iraise (exn, info))
              with UserError _ | Exit ->
                tac
            else
              tac
	in try_red_apply thm_ty0
      | exn -> iraise (exn, info))
    end
  in
    Tacticals.New.tclTHENLIST [
      try_main_apply with_destruct c;
      solve_remaining_apply_goals;
      apply_clear_request clear_flag (use_clear_hyp_by_default ()) c
    ]
  end

let rec apply_with_bindings_gen b e = function
  | [] -> Proofview.tclUNIT ()
  | [k,cb] -> general_apply b b e k cb
  | (k,cb)::cbl ->
      Tacticals.New.tclTHENLAST
        (general_apply b b e k cb)
        (apply_with_bindings_gen b e cbl)

let apply_with_delayed_bindings_gen b e l = 
  let one k (loc, f) =
    Proofview.Goal.enter begin fun gl ->
      let sigma = Proofview.Goal.sigma gl in
      let env = Proofview.Goal.env gl in
      let sigma, cb = f env sigma in
	Tacticals.New.tclWITHHOLES e
          (general_apply b b e k) sigma (loc,cb)
    end
  in
  let rec aux = function
    | [] -> Proofview.tclUNIT ()
    | [k,f] -> one k f
    | (k,f)::cbl ->
      Tacticals.New.tclTHENLAST
        (one k f) (aux cbl)
  in aux l

let apply_with_bindings cb = apply_with_bindings_gen false false [None,(dloc,cb)]

let eapply_with_bindings cb = apply_with_bindings_gen false true [None,(dloc,cb)]

let apply c = apply_with_bindings_gen false false [None,(dloc,(c,NoBindings))]

let eapply c = apply_with_bindings_gen false true [None,(dloc,(c,NoBindings))]

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
    with e when catchable_exception e ->
    try find (clenv_push_prod clause)
    with NotExtensibleClause -> failwith "Cannot apply"
  in find clause

let progress_with_clause flags innerclause clause =
  let ordered_metas = List.rev (clenv_independent clause) in
  if List.is_empty ordered_metas then error "Statement without assumptions.";
  let f mv =
    try Some (find_matching_clause (clenv_fchain mv ~flags clause) innerclause)
    with Failure _ -> None
  in
  try List.find_map f ordered_metas
  with Not_found -> error "Unable to unify."

let apply_in_once_main flags innerclause env sigma (d,lbind) =
  let thm = nf_betaiota sigma (Retyping.get_type_of env sigma d) in
  let rec aux clause =
    try progress_with_clause flags innerclause clause
    with e when Errors.noncritical e ->
    let e = Errors.push e in
    try aux (clenv_push_prod clause)
    with NotExtensibleClause -> iraise e
  in
  aux (make_clenv_binding env sigma (d,thm) lbind)

let apply_in_once sidecond_first with_delta with_destruct with_evars naming
    id (clear_flag,(loc,(d,lbind))) tac =
  Proofview.Goal.nf_enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let flags =
    if with_delta then default_unify_flags () else default_no_delta_unify_flags () in
  let t' = Tacmach.New.pf_get_hyp_typ id gl in
  let innerclause = mk_clenv_from_env env sigma (Some 0) (mkVar id,t') in
  let targetid = find_name true (Anonymous,None,t') naming gl in
  let rec aux idstoclear with_destruct c =
    Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    try
      let clause = apply_in_once_main flags innerclause env sigma (c,lbind) in
      clenv_refine_in ~sidecond_first with_evars targetid id sigma clause
        (fun id ->
          Tacticals.New.tclTHENLIST [
            apply_clear_request clear_flag false c;
            Proofview.V82.tactic (thin idstoclear);
            tac id
          ])
    with e when with_destruct && Errors.noncritical e ->
      let e = Errors.push e in
        (descend_in_conjunctions [targetid]
           (fun b id -> aux (id::idstoclear) b (mkVar id))
           (fun _ -> iraise e) c)
    end
  in
  aux [] with_destruct d
  end

let apply_in_delayed_once sidecond_first with_delta with_destruct with_evars naming
    id (clear_flag,(loc,f)) tac =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let sigma, c = f env sigma in
    Tacticals.New.tclWITHHOLES with_evars 
      (apply_in_once sidecond_first with_delta with_destruct with_evars
         naming id (clear_flag,(loc,c)))
      sigma tac
  end

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

let cut_and_apply c =
  Proofview.Goal.nf_enter begin fun gl ->
    match kind_of_term (Tacmach.New.pf_hnf_constr gl (Tacmach.New.pf_type_of gl c)) with
      | Prod (_,c1,c2) when not (dependent (mkRel 1) c2) ->
        let concl = Proofview.Goal.concl gl in
        let env = Tacmach.New.pf_env gl in
        Proofview.Refine.refine begin fun sigma ->
          let typ = mkProd (Anonymous, c2, concl) in
          let (sigma, f) = Evarutil.new_evar env sigma typ in
          let (sigma, x) = Evarutil.new_evar env sigma c1 in
          let ans = mkApp (f, [|mkApp (c, [|x|])|]) in
          (sigma, ans)
        end
      | _ -> error "lapply needs a non-dependent product."
  end

(********************************************************************)
(*               Exact tactics                                      *)
(********************************************************************)

(* let convert_leqkey = Profile.declare_profile "convert_leq";; *)
(* let convert_leq = Profile.profile3 convert_leqkey convert_leq *)

(* let refine_no_checkkey = Profile.declare_profile "refine_no_check";; *)
(* let refine_no_check = Profile.profile2 refine_no_checkkey refine_no_check *)

let new_exact_no_check c =
  Proofview.Refine.refine ~unsafe:true (fun h -> (h, c))

let exact_check c =
  Proofview.Goal.enter begin fun gl ->
  (** We do not need to normalize the goal because we just check convertibility *)
  let concl = Proofview.Goal.concl (Proofview.Goal.assume gl) in
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let sigma, ct = Typing.e_type_of env sigma c in
    Proofview.Unsafe.tclEVARS sigma <*>
      Tacticals.New.tclTHEN (convert_leq ct concl) (new_exact_no_check c)
  end

let exact_no_check = refine_no_check

let vm_cast_no_check c gl =
  let concl = pf_concl gl in
  refine_no_check (Term.mkCast(c,Term.VMcast,concl)) gl


let exact_proof c gl =
  let c,ctx = Constrintern.interp_casted_constr (pf_env gl) (project gl) c (pf_concl gl)
  in tclTHEN (tclEVARUNIVCONTEXT ctx) (refine_no_check c) gl

let assumption =
  let rec arec gl only_eq = function
  | [] ->
    if only_eq then
      let hyps = Proofview.Goal.hyps gl in
      arec gl false hyps
    else Tacticals.New.tclZEROMSG (str "No such assumption.")
  | (id, c, t)::rest ->
    let concl = Proofview.Goal.concl gl in
    let sigma = Proofview.Goal.sigma gl in
    let (sigma, is_same_type) =
      if only_eq then (sigma, Constr.equal t concl)
      else
        let env = Proofview.Goal.env gl in
        infer_conv env sigma t concl
    in
    if is_same_type then
      (Proofview.Unsafe.tclEVARS sigma) <*>
	Proofview.Refine.refine ~unsafe:true (fun h -> (h, mkVar id))
    else arec gl only_eq rest
  in
  let assumption_tac gl =
    let hyps = Proofview.Goal.hyps gl in
    arec gl true hyps
  in
  Proofview.Goal.nf_enter assumption_tac

(*****************************************************************)
(*          Modification of a local context                      *)
(*****************************************************************)

(* This tactic enables the user to remove hypotheses from the signature.
 * Some care is taken to prevent him from removing variables that are
 * subsequently used in other hypotheses or in the conclusion of the
 * goal. *)

let clear ids = (* avant seul dyn_clear n'echouait pas en [] *)
  if List.is_empty ids then tclIDTAC else thin ids

let on_the_bodies = function
| [] -> assert false
| [id] -> str " depends on the body of " ++ pr_id id
| l -> str " depends on the bodies of " ++ pr_sequence pr_id l

let check_is_type env ty msg =
  Proofview.tclEVARMAP >>= fun sigma ->
  let evdref = ref sigma in
  try
    let _ = Typing.sort_of env evdref ty in
    Proofview.Unsafe.tclEVARS !evdref
  with e when Errors.noncritical e ->
    msg e

let check_decl env (_, c, ty) msg =
  Proofview.tclEVARMAP >>= fun sigma ->
  let evdref = ref sigma in
  try
    let _ = Typing.sort_of env evdref ty in
    let _ = match c with
    | None -> ()
    | Some c -> Typing.check env evdref c ty
    in
    Proofview.Unsafe.tclEVARS !evdref
  with e when Errors.noncritical e ->
    msg e

let clear_body ids =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let concl = Proofview.Goal.concl (Proofview.Goal.assume gl) in
    let ctx = named_context env in
    let map (id, body, t as decl) = match body with
    | None ->
      let () = if List.mem_f Id.equal id ids then
        errorlabstrm "" (str "Hypothesis " ++ pr_id id ++ str " is not a local definition")
      in
      decl
    | Some _ ->
      if List.mem_f Id.equal id ids then (id, None, t) else decl
    in
    let ctx = List.map map ctx in
    let base_env = reset_context env in
    let env = push_named_context ctx base_env in
    let check_hyps =
      let check env (id, _, _ as decl) =
        let msg _ = Tacticals.New.tclZEROMSG
          (str "Hypothesis " ++ pr_id id ++ on_the_bodies ids)
        in
        check_decl env decl msg <*> Proofview.tclUNIT (push_named decl env)
      in
      let checks = Proofview.Monad.List.fold_left check base_env (List.rev ctx) in
      Proofview.tclIGNORE checks
    in
    let check_concl =
      let msg _ = Tacticals.New.tclZEROMSG
        (str "Conclusion" ++ on_the_bodies ids)
      in
      check_is_type env concl msg
    in
    check_hyps <*> check_concl <*>
    Proofview.Refine.refine ~unsafe:true begin fun sigma ->
      Evarutil.new_evar env sigma concl
    end
  end

let clear_wildcards ids =
  Proofview.V82.tactic (tclMAP (fun (loc,id) gl ->
    try with_check (Tacmach.thin_no_check [id]) gl
    with ClearDependencyError (id,err) ->
      (* Intercept standard [thin] error message *)
      Loc.raise loc
        (error_clear_dependency (pf_env gl) (project gl) (Id.of_string "_") err))
    ids)

(*   Takes a list of booleans, and introduces all the variables
 *  quantified in the goal which are associated with a value
 *  true  in the boolean list. *)

let rec intros_clearing = function
  | []          -> Proofview.tclUNIT ()
  | (false::tl) -> Tacticals.New.tclTHEN intro (intros_clearing tl)
  | (true::tl)  ->
      Tacticals.New.tclTHENLIST
        [ intro; Tacticals.New.onLastHypId (fun id -> Proofview.V82.tactic (clear [id])); intros_clearing tl]

(* Modifying/Adding an hypothesis  *)

let specialize (c,lbind) g =
  let tac, term =
    if lbind == NoBindings then
      let evd = Typeclasses.resolve_typeclasses (pf_env g) (project g) in
	tclEVARS evd, nf_evar evd c
    else
      let clause = pf_apply make_clenv_binding g (c,pf_type_of g c) lbind in
      let flags = { (default_unify_flags ()) with resolve_evars = true } in
      let clause = clenv_unify_meta_types ~flags clause in
      let (thd,tstack) = whd_nored_stack clause.evd (clenv_value clause) in
      let rec chk = function
      | [] -> []
      | t::l -> if occur_meta t then [] else t :: chk l
      in
      let tstack = chk tstack in
      let term = applist(thd,List.map (nf_evar clause.evd) tstack) in
      if occur_meta term then
	errorlabstrm "" (str "Cannot infer an instance for " ++
          pr_name (meta_name clause.evd (List.hd (collect_metas term))) ++
	  str ".");
       tclEVARS clause.evd, term
  in
  match kind_of_term (fst(decompose_app (snd(decompose_lam_assum c)))) with
       | Var id when Id.List.mem id (pf_ids_of_hyps g) ->
	   tclTHEN tac
	     (tclTHENFIRST
	       (fun g -> Proofview.V82.of_tactic (assert_before_replacing id (pf_type_of g term)) g)
	       (exact_no_check term)) g
       | _ -> tclTHEN tac
	   (tclTHENLAST
              (fun g -> Proofview.V82.of_tactic (cut (pf_type_of g term)) g)
              (exact_no_check term)) g

(* Keeping only a few hypotheses *)

let keep hyps =
  Proofview.Goal.nf_enter begin fun gl ->
  Proofview.tclENV >>= fun env ->
  let ccl = Proofview.Goal.concl gl in
  let cl,_ =
    fold_named_context_reverse (fun (clear,keep) (hyp,_,_ as decl) ->
      if Id.List.mem hyp hyps
        || List.exists (occur_var_in_decl env hyp) keep
	|| occur_var env hyp ccl
      then (clear,decl::keep)
      else (hyp::clear,keep))
      ~init:([],[]) (Proofview.Goal.env gl)
  in
  Proofview.V82.tactic (fun gl -> thin cl gl)
  end

(************************)
(* Introduction tactics *)
(************************)

let check_number_of_constructors expctdnumopt i nconstr =
  if Int.equal i 0 then error "The constructors are numbered starting from 1.";
  begin match expctdnumopt with
    | Some n when not (Int.equal n nconstr) ->
	error ("Not an inductive goal with "^
	       string_of_int n ^ String.plural n " constructor"^".")
    | _ -> ()
  end;
  if i > nconstr then error "Not enough constructors."

let constructor_tac with_evars expctdnumopt i lbind =
  Proofview.Goal.enter begin fun gl ->
    let cl = Tacmach.New.pf_nf_concl gl in
    let reduce_to_quantified_ind =
      Tacmach.New.pf_apply Tacred.reduce_to_quantified_ind gl
    in
    let (mind,redcl) = reduce_to_quantified_ind cl in
    let nconstr =
      Array.length (snd (Global.lookup_inductive (fst mind))).mind_consnames in
      check_number_of_constructors expctdnumopt i nconstr;

      let sigma, cons = Evd.fresh_constructor_instance
	(Proofview.Goal.env gl) (Proofview.Goal.sigma gl) (fst mind, i) in
      let cons = mkConstructU cons in
	
      let apply_tac = general_apply true false with_evars None (dloc,(cons,lbind)) in
	(Tacticals.New.tclTHENLIST
           [Proofview.Unsafe.tclEVARS sigma; 
	    convert_concl_no_check redcl DEFAULTcast;
	    intros; apply_tac])
  end

let one_constructor i lbind = constructor_tac false None i lbind

(* Try to apply the constructor of the inductive definition followed by
   a tactic t given as an argument.
   Should be generalize in Constructor (Fun c : I -> tactic)
 *)

let rec tclANY tac = function
| [] -> Tacticals.New.tclZEROMSG (str "No applicable tactic.")
| arg :: l ->
  Tacticals.New.tclORD (tac arg) (fun () -> tclANY tac l)

let any_constructor with_evars tacopt =
  let t = match tacopt with None -> Proofview.tclUNIT () | Some t -> t in
  let tac i = Tacticals.New.tclTHEN (constructor_tac with_evars None i NoBindings) t in
  Proofview.Goal.enter begin fun gl ->
    let cl = Tacmach.New.pf_nf_concl gl in
    let reduce_to_quantified_ind =
      Tacmach.New.pf_apply Tacred.reduce_to_quantified_ind gl
    in
    let mind = fst (reduce_to_quantified_ind cl) in
    let nconstr =
      Array.length (snd (Global.lookup_inductive (fst mind))).mind_consnames in
    if Int.equal nconstr 0 then error "The type has no constructors.";
    tclANY tac (List.interval 1 nconstr)
 end

let left_with_bindings  with_evars = constructor_tac with_evars (Some 2) 1
let right_with_bindings with_evars = constructor_tac with_evars (Some 2) 2
let split_with_bindings with_evars l =
  Tacticals.New.tclMAP (constructor_tac with_evars (Some 1) 1) l

let left           = left_with_bindings false
let simplest_left  = left NoBindings

let right          = right_with_bindings false
let simplest_right = right NoBindings

let split          = constructor_tac false (Some 1) 1
let simplest_split = split NoBindings

(*****************************)
(* Decomposing introductions *)
(*****************************)

(* Rewriting function for rewriting one hypothesis at the time *)
let (forward_general_rewrite_clause, general_rewrite_clause) = Hook.make ()

(* Rewriting function for substitution (x=t) everywhere at the same time *)
let (forward_subst_one, subst_one) = Hook.make ()

let error_unexpected_extra_pattern loc bound pat =
  let _,nb = Option.get bound in
  let s1,s2,s3 = match pat with
  | IntroNaming (IntroIdentifier _) ->
      "name", (String.plural nb " introduction pattern"), "no"
  | _ -> "introduction pattern", "", "none" in
  user_err_loc (loc,"",str "Unexpected " ++ str s1 ++ str " (" ++
    (if Int.equal nb 0 then (str s3 ++ str s2) else
      (str "at most " ++ int nb ++ str s2)) ++ spc () ++
       str (if Int.equal nb 1 then "was" else "were") ++
      strbrk " expected in the branch).")

let intro_decomp_eq_function = ref (fun _ -> failwith "Not implemented")

let declare_intro_decomp_eq f = intro_decomp_eq_function := f

let my_find_eq_data_decompose gl t =
  try find_eq_data_decompose gl t
  with e when is_anomaly e
    (* Hack in case equality is not yet defined... one day, maybe,
       known equalities will be dynamically registered *)
      -> raise Constr_matching.PatternMatchingFailure

let intro_decomp_eq loc l thin tac id =
  Proofview.Goal.nf_enter begin fun gl ->
  let c = mkVar id in
  let t = Tacmach.New.pf_type_of gl c in
  let _,t = Tacmach.New.pf_reduce_to_quantified_ind gl t in
  let eq,u,eq_args = my_find_eq_data_decompose gl t in
  !intro_decomp_eq_function
    (fun n -> tac ((dloc,id)::thin) (Some (true,n)) l)
    (eq,t,eq_args) (c, t)
  end

let intro_or_and_pattern loc bracketed ll thin tac id =
  Proofview.Goal.enter begin fun gl ->
  let c = mkVar id in
  let t = Tacmach.New.pf_type_of gl c in
  let ((ind,u),t) = Tacmach.New.pf_reduce_to_quantified_ind gl t in
  let nv = constructors_nrealargs ind in
  let ll = fix_empty_or_and_pattern (Array.length nv) ll in
  check_or_and_pattern_size loc ll (Array.length nv);
  Tacticals.New.tclTHENLASTn
    (Tacticals.New.tclTHEN (simplest_case c) (Proofview.V82.tactic (clear [id])))
    (Array.map2 (fun n l -> tac thin (Some (bracketed,n)) l)
       nv (Array.of_list ll))
  end

let rewrite_hyp assert_style l2r id =
  let rew_on l2r =
    Hook.get forward_general_rewrite_clause l2r false (mkVar id,NoBindings) in
  let subst_on l2r x rhs =
    Hook.get forward_subst_one true x (id,rhs,l2r) in
  let clear_var_and_eq c = tclTHEN (clear [id]) (clear [destVar c]) in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let type_of = Tacmach.New.pf_type_of gl in
    let whd_betadeltaiota = Tacmach.New.pf_apply whd_betadeltaiota gl in
    let t = whd_betadeltaiota (type_of (mkVar id)) in
    match match_with_equality_type t with
    | Some (hdcncl,[_;lhs;rhs]) ->
        if l2r && isVar lhs && not (occur_var env (destVar lhs) rhs) then
          subst_on l2r (destVar lhs) rhs
        else if not l2r && isVar rhs && not (occur_var env (destVar rhs) lhs) then
          subst_on l2r (destVar rhs) lhs
        else
          Tacticals.New.tclTHEN (rew_on l2r onConcl) (Proofview.V82.tactic (clear [id]))
    | Some (hdcncl,[c]) ->
        let l2r = not l2r in (* equality of the form eq_true *)
        if isVar c then
          Tacticals.New.tclTHEN (rew_on l2r allHypsAndConcl) 
	    (Proofview.V82.tactic (clear_var_and_eq c))
        else
          Tacticals.New.tclTHEN (rew_on l2r onConcl) (Proofview.V82.tactic (clear [id]))
    | _ ->
        Tacticals.New.tclTHEN (rew_on l2r onConcl) (Proofview.V82.tactic (clear [id]))
  end

let rec prepare_naming loc = function
  | IntroIdentifier id -> NamingMustBe (loc,id)
  | IntroAnonymous -> NamingAvoid []
  | IntroFresh id -> NamingBasedOn (id,[])

let rec explicit_intro_names = function
| (_, IntroForthcoming _) :: l -> explicit_intro_names l
| (_, IntroNaming (IntroIdentifier id)) :: l -> id :: explicit_intro_names l
| (_, IntroAction (IntroOrAndPattern ll)) :: l' ->
    List.flatten (List.map (fun l -> explicit_intro_names (l@l')) ll)
| (_, IntroAction (IntroInjection l)) :: l' ->
    explicit_intro_names (l@l')
| (_, IntroAction (IntroApplyOn (c,pat))) :: l' ->
    explicit_intro_names (pat::l')
| (_, (IntroNaming (IntroAnonymous | IntroFresh _)
     | IntroAction (IntroWildcard | IntroRewrite _))) :: l ->
     explicit_intro_names l
| [] -> []

let wild_id = Id.of_string "_tmp"

let rec list_mem_assoc_right id = function
  | [] -> false
  | (x,id')::l -> Id.equal id id' || list_mem_assoc_right id l

let check_thin_clash_then id thin avoid tac =
  if list_mem_assoc_right id thin then
    let newid = next_ident_away (add_suffix id "'") avoid in
    let thin =
      List.map (on_snd (fun id' -> if Id.equal id id' then newid else id')) thin in
    Tacticals.New.tclTHEN (rename_hyp [id,newid]) (tac thin)
  else
    tac thin

let make_tmp_naming avoid l = function
  (* In theory, we could use a tmp id like "wild_id" for all actions
     but we prefer to avoid it to avoid this kind of "ugly" names *)
  (* Alternatively, we could have called check_thin_clash_then on
     IntroAnonymous, but at the cost of a "renaming"; Note that in the
     case of IntroFresh, we should use check_thin_clash_then anyway to
     prevent the case of an IntroFresh precisely using the wild_id *)
  | IntroWildcard -> NamingBasedOn (wild_id,avoid@explicit_intro_names l)
  | _ -> NamingAvoid(avoid@explicit_intro_names l)

let fit_bound n = function
  | None -> true
  | Some (use_bound,n') -> not use_bound || n = n'

let exceed_bound n = function
  | None -> false
  | Some (use_bound,n') -> use_bound && n >= n'

  (* We delay thinning until the completion of the whole intros tactic
     to ensure that dependent hypotheses are cleared in the right
     dependency order (see bug #1000); we use fresh names, not used in
     the tactic, for the hyps to clear *)
let rec intro_patterns_core b avoid ids thin destopt bound n tac = function
  | [] when fit_bound n bound ->
      tac ids thin
  | [] ->
      (* Behave as IntroAnonymous *)
      intro_patterns_core b avoid ids thin destopt bound n tac
        [dloc,IntroNaming IntroAnonymous]
  | (loc,pat) :: l ->
  if exceed_bound n bound then error_unexpected_extra_pattern loc bound pat else
  match pat with
  | IntroForthcoming onlydeps ->
      intro_forthcoming_then_gen (NamingAvoid (avoid@explicit_intro_names l))
	  destopt onlydeps n bound
        (fun ids -> intro_patterns_core b avoid ids thin destopt bound
          (n+List.length ids) tac l)
  | IntroAction pat ->
      intro_then_gen (make_tmp_naming avoid l pat)
	MoveLast true false
        (intro_pattern_action loc (b || not (List.is_empty l)) false pat thin
          (fun thin bound' -> intro_patterns_core b avoid ids thin destopt bound' 0
            (fun ids thin ->
              intro_patterns_core b avoid ids thin destopt bound (n+1) tac l)))
  | IntroNaming pat ->
      intro_pattern_naming loc b avoid ids pat thin destopt bound n tac l

and intro_pattern_naming loc b avoid ids pat thin destopt bound n tac l =
  match pat with
  | IntroIdentifier id ->
      check_thin_clash_then id thin avoid (fun thin ->
        intro_then_gen (NamingMustBe (loc,id)) destopt true false
          (fun id -> intro_patterns_core b avoid (id::ids) thin destopt bound (n+1) tac l))
  | IntroAnonymous ->
      intro_then_gen (NamingAvoid (avoid@explicit_intro_names l))
	destopt true false
        (fun id -> intro_patterns_core b avoid (id::ids) thin destopt bound (n+1) tac l)
  | IntroFresh id ->
      (* todo: avoid thinned names to interfere with generation of fresh name *)
      intro_then_gen (NamingBasedOn (id, avoid@explicit_intro_names l))
	destopt true false
        (fun id -> intro_patterns_core b avoid (id::ids) thin destopt bound (n+1) tac l)

and intro_pattern_action loc b style pat thin tac id = match pat with
  | IntroWildcard ->
      tac ((loc,id)::thin) None []
  | IntroOrAndPattern ll ->
      intro_or_and_pattern loc b ll thin tac id
  | IntroInjection l' ->
      intro_decomp_eq loc l' thin tac id
  | IntroRewrite l2r ->
      Tacticals.New.tclTHENLAST
        (* Skip the side conditions of the rewriting step *)
	(rewrite_hyp style l2r id)
        (tac thin None [])
  | IntroApplyOn (f,(loc,pat)) ->
      let naming,tac_ipat = prepare_intros_loc loc (IntroIdentifier id) pat in
      Proofview.Goal.enter begin fun gl ->
        let sigma = Proofview.Goal.sigma gl in
        let env = Proofview.Goal.env gl in
        let sigma,c = f env sigma in
        Proofview.Unsafe.tclEVARS sigma <*>
          (Tacticals.New.tclTHENFIRST
             (* Skip the side conditions of the apply *)
             (apply_in_once false true true true naming id
                (None,(sigma,(c,NoBindings))) tac_ipat))
	  (tac thin None [])
      end

and prepare_intros_loc loc dft = function
  | IntroNaming ipat ->
      prepare_naming loc ipat,
      (fun _ -> Proofview.tclUNIT ())
  | IntroAction ipat ->
      prepare_naming loc dft,
      (let tac thin bound =
        intro_patterns_core true [] [] thin MoveLast bound 0
          (fun _ l -> clear_wildcards l) in
      fun id -> intro_pattern_action loc true true ipat [] tac id)
  | IntroForthcoming _ -> user_err_loc
      (loc,"",str "Introduction pattern for one hypothesis expected.")

let intro_patterns_bound_to n destopt =
  intro_patterns_core true [] [] [] destopt
    (Some (true,n)) 0 (fun _ -> clear_wildcards)

(* The following boolean governs what "intros []" do on examples such
   as "forall x:nat*nat, x=x"; if true, it behaves as "intros [? ?]";
   if false, it behaves as "intro H; case H; clear H" for fresh H.
   Kept as false for compatibility.
 *)
let bracketing_last_or_and_intro_pattern = false 

let intro_patterns_to destopt =
  intro_patterns_core bracketing_last_or_and_intro_pattern
    [] [] [] destopt None 0 (fun _ l -> clear_wildcards l)

let intro_pattern_to destopt pat =
  intro_patterns_to destopt [dloc,pat]

let intro_patterns = intro_patterns_to MoveLast

(* Implements "intros" *)
let intros_patterns = function
  | [] -> intros
  | l -> intro_patterns_to MoveLast l

(**************************)
(*   Forward reasoning    *)
(**************************)

let prepare_intros dft = function
  | None -> prepare_naming dloc dft, (fun _id -> Proofview.tclUNIT ())
  | Some (loc,ipat) -> prepare_intros_loc loc dft ipat

let ipat_of_name = function
  | Anonymous -> None
  | Name id -> Some (dloc, IntroNaming (IntroIdentifier id))

 let head_ident c =
   let c = fst (decompose_app ((strip_lam_assum c))) in
   if isVar c then Some (destVar c) else None

let assert_as first ipat c =
  let naming,tac = prepare_intros IntroAnonymous ipat in
  let repl = do_replace (head_ident c) naming in
  if first then assert_before_then_gen repl naming c tac
  else assert_after_then_gen repl naming c tac

(* apply in as *)

let general_apply_in sidecond_first with_delta with_destruct with_evars
    with_clear id lemmas ipat =
  let tac (naming,lemma) tac id =
    apply_in_delayed_once sidecond_first with_delta with_destruct with_evars
      naming id lemma tac in
  let naming,ipat_tac = prepare_intros (IntroIdentifier id) ipat in
  let lemmas_target, last_lemma_target =
    let last,first = List.sep_last lemmas in
    List.map (fun lem -> (NamingMustBe (dloc,id),lem)) first, (naming,last)
  in
  (* We chain apply_in_once, ending with an intro pattern *)
  List.fold_right tac lemmas_target (tac last_lemma_target ipat_tac) id

(*
  if sidecond_first then
    (* Skip the side conditions of the applied lemma *)
    Tacticals.New.tclTHENLAST (tclMAPLAST tac lemmas_target) (ipat_tac id)
  else
    Tacticals.New.tclTHENFIRST (tclMAPFIRST tac lemmas_target) (ipat_tac id)
*)

let apply_in simple with_evars clear_flag id lemmas ipat =
  let lemmas = List.map (fun (k,(loc,l)) -> k, (loc, fun _ sigma -> sigma, l)) lemmas in
  general_apply_in false simple simple with_evars clear_flag id lemmas ipat

let apply_delayed_in simple with_evars clear_flag id lemmas ipat =
  general_apply_in false simple simple with_evars clear_flag id lemmas ipat

(*****************************)
(* Tactics abstracting terms *)
(*****************************)

(* Implementation without generalisation: abbrev will be lost in hyps in *)
(* in the extracted proof *)

let tactic_infer_flags with_evar = {
  Pretyping.use_typeclasses = true;
  Pretyping.use_unif_heuristics = true;
  Pretyping.use_hook = Some solve_by_implicit_tactic;
  Pretyping.fail_evar = not with_evar;
  Pretyping.expand_evars = true }

let decode_hyp = function
  | None -> MoveLast
  | Some id -> MoveAfter id

(* [letin_tac b (... abstract over c ...) gl] transforms
   [...x1:T1(c),...,x2:T2(c),... |- G(c)] into
   [...x:T;Heqx:(x=c);x1:T1(x),...,x2:T2(x),... |- G(x)] if [b] is false or
   [...x:=c:T;x1:T1(x),...,x2:T2(x),... |- G(x)] if [b] is true
*)

let letin_tac_gen with_eq (id,depdecls,lastlhyp,ccl,c) ty =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let t = match ty with Some t -> t | _ -> typ_of env sigma c in
    let eq_tac gl = match with_eq with
      | Some (lr,(loc,ido)) ->
          let heq = match ido with
            | IntroAnonymous -> new_fresh_id [id] (add_prefix "Heq" id) gl
            | IntroFresh heq_base -> new_fresh_id [id] heq_base gl
            | IntroIdentifier id -> id in
          let eqdata = build_coq_eq_data () in
          let args = if lr then [t;mkVar id;c] else [t;c;mkVar id]in
          let sigma, eq = Evd.fresh_global env sigma eqdata.eq in
          let sigma, refl = Evd.fresh_global env sigma eqdata.refl in
          let eq = applist (eq,args) in
          let refl = applist (refl, [t;mkVar id]) in
	  let term = mkNamedLetIn id c t (mkLetIn (Name heq, refl, eq, ccl)) in
	  let sigma, _ = Typing.e_type_of env sigma term in
            sigma, term,
            Tacticals.New.tclTHEN
	      (intro_gen (NamingMustBe (loc,heq)) (decode_hyp lastlhyp) true false)
	      (clear_body [heq;id])
      | None ->
	  (sigma, mkNamedLetIn id c t ccl, Proofview.tclUNIT ()) in
    let (sigma,newcl,eq_tac) = eq_tac gl in
    Tacticals.New.tclTHENLIST
      [ Proofview.Unsafe.tclEVARS sigma;
	convert_concl_no_check newcl DEFAULTcast;
        intro_gen (NamingMustBe (dloc,id)) (decode_hyp lastlhyp) true false;
        Tacticals.New.tclMAP convert_hyp_no_check depdecls;
        eq_tac ]
  end

let insert_before decls lasthyp env =
  match lasthyp with
  | None -> push_named_context decls env
  | Some id ->
  Environ.fold_named_context
    (fun _ (id',_,_ as d) env ->
      let env = if Id.equal id id' then push_named_context decls env else env in
      push_named d env)
    ~init:(reset_context env) env

(* unsafe *)

let mkletin_goal env sigma store with_eq dep (id,lastlhyp,ccl,c) ty =
  let body = if dep then Some c else None in
  let t = match ty with Some t -> t | _ -> typ_of env sigma c in
  match with_eq with
  | Some (lr,(loc,ido)) ->
      let heq = match ido with
      | IntroAnonymous -> fresh_id_in_env [id] (add_prefix "Heq" id) env
      | IntroFresh heq_base -> fresh_id_in_env [id] heq_base env
      | IntroIdentifier id -> id in
      let eqdata = build_coq_eq_data () in
      let args = if lr then [t;mkVar id;c] else [t;c;mkVar id]in
      let sigma, eq = Evd.fresh_global env sigma eqdata.eq in
      let sigma, refl = Evd.fresh_global env sigma eqdata.refl in
      let eq = applist (eq,args) in
      let refl = applist (refl, [t;mkVar id]) in
      let newenv = insert_before [heq,None,eq;id,body,t] lastlhyp env in
      let (sigma,x) = new_evar newenv sigma ~principal:true ~store ccl in
      (sigma,mkNamedLetIn id c t (mkNamedLetIn heq refl eq x))
  | None ->
      let newenv = insert_before [id,body,t] lastlhyp env in
      let (sigma,x) = new_evar newenv sigma ~principal:true ~store ccl in
      (sigma,mkNamedLetIn id c t x)

let letin_tac with_eq id c ty occs =
  Proofview.Goal.nf_enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let ccl = Proofview.Goal.concl gl in
    let abs = AbstractExact (id,c,ty,occs,true) in
    let (id,_,depdecls,lastlhyp,ccl,_) = make_abstraction env sigma ccl abs in
    (* We keep the original term to match *)
    letin_tac_gen with_eq (id,depdecls,lastlhyp,ccl,c) ty
  end

let letin_pat_tac with_eq id c occs =
  Proofview.Goal.nf_enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let ccl = Proofview.Goal.concl gl in
    let check t = true in
    let abs = AbstractPattern (false,check,id,c,occs,false) in
    let (id,_,depdecls,lastlhyp,ccl,res) = make_abstraction env sigma ccl abs in
    let sigma,c = match res with
    | None -> finish_evar_resolution ~flags:(tactic_infer_flags false) env sigma c
    | Some (sigma,c) -> (sigma,c) in
    Tacticals.New.tclTHEN
      (Proofview.Unsafe.tclEVARS sigma)
      (letin_tac_gen with_eq (id,depdecls,lastlhyp,ccl,c) None)
  end

(* Tactics "pose proof" (usetac=None) and "assert"/"enough" (otherwise) *)
let forward b usetac ipat c =
  match usetac with
  | None ->
      Proofview.Goal.enter begin fun gl ->
      let t = Tacmach.New.pf_type_of gl  c in
      Tacticals.New.tclTHENFIRST (assert_as true ipat t)
	(Proofview.V82.tactic (exact_no_check c))
      end
  | Some tac ->
      if b then
        Tacticals.New.tclTHENFIRST (assert_as b ipat c) tac
      else
        Tacticals.New.tclTHENS3PARTS
          (assert_as b ipat c) [||] tac [|Tacticals.New.tclIDTAC|]

let pose_proof na c = forward true None (ipat_of_name na) c
let assert_by na t tac = forward true (Some tac) (ipat_of_name na) t
let enough_by na t tac = forward false (Some tac) (ipat_of_name na) t

(***************************)
(*  Generalization tactics *)
(***************************)

(* Given a type [T] convertible to [forall x1..xn:A1..An(x1..xn-1), G(x1..xn)]
   and [a1..an:A1..An(a1..an-1)] such that the goal is [G(a1..an)],
   this generalizes [hyps |- goal] into [hyps |- T] *)

let apply_type hdcty argl gl =
  refine (applist (mkCast (Evarutil.mk_new_meta(),DEFAULTcast, hdcty),argl)) gl

(* Given a context [hyps] with domain [x1..xn], possibly with let-ins,
   and well-typed in the current goal, [bring_hyps hyps] generalizes
   [ctxt |- G(x1..xn] into [ctxt |- forall hyps, G(x1..xn)] *)

let bring_hyps hyps =
  if List.is_empty hyps then Tacticals.New.tclIDTAC
  else
    Proofview.Goal.enter begin fun gl ->
      let env = Proofview.Goal.env gl in
      let concl = Tacmach.New.pf_nf_concl gl in
      let newcl = List.fold_right mkNamedProd_or_LetIn hyps concl in
      let args = Array.of_list (instance_from_named_context hyps) in
      Proofview.Refine.refine begin fun sigma ->
        let (sigma, ev) = Evarutil.new_evar env sigma newcl in
        (sigma, (mkApp (ev, args)))
      end
    end

let revert hyps = 
  Proofview.Goal.enter begin fun gl ->
    let gl = Proofview.Goal.assume gl in
    let ctx = List.map (fun id -> Tacmach.New.pf_get_hyp id gl) hyps in
      (bring_hyps ctx) <*> (Proofview.V82.tactic (clear hyps))
  end

(* Compute a name for a generalization *)

let generalized_name c t ids cl = function
  | Name id as na ->
      if Id.List.mem id ids then
	errorlabstrm "" (pr_id id ++ str " is already used.");
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

(* Abstract over [c] in [forall x1:A1(c)..xi:Ai(c).T(c)] producing
   [forall x, x1:A1(x1), .., xi:Ai(x). T(x)] with all [c] abtracted in [Ai]
   but only those at [occs] in [T] *)

let generalize_goal_gen env ids i ((occs,c,b),na) t (cl,evd) =
  let decls,cl = decompose_prod_n_assum i cl in
  let dummy_prod = it_mkProd_or_LetIn mkProp decls in
  let newdecls,_ = decompose_prod_n_assum i (subst_term_gen eq_constr_nounivs c dummy_prod) in
  let cl',evd' = subst_closed_term_occ env evd (AtOccs occs) c (it_mkProd_or_LetIn cl newdecls) in
  let na = generalized_name c t ids cl' na in
    mkProd_or_LetIn (na,b,t) cl', evd'

let generalize_goal gl i ((occs,c,b),na as o) cl =
  let t = pf_type_of gl c in
  let env = pf_env gl in
    generalize_goal_gen env (pf_ids_of_hyps gl) i o t cl

let generalize_dep ?(with_let=false) c gl =
  let env = pf_env gl in
  let sign = pf_hyps gl in
  let init_ids = ids_of_named_context (Global.named_context()) in
  let seek d toquant =
    if List.exists (fun (id,_,_) -> occur_var_in_decl env id d) toquant
      || dependent_in_decl c d then
      d::toquant
    else
      toquant in
  let to_quantify = Context.fold_named_context seek sign ~init:[] in
  let to_quantify_rev = List.rev to_quantify in
  let qhyps = List.map (fun (id,_,_) -> id) to_quantify_rev in
  let tothin = List.filter (fun id -> not (Id.List.mem id init_ids)) qhyps in
  let tothin' =
    match kind_of_term c with
      | Var id when mem_named_context id sign && not (Id.List.mem id init_ids)
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
  let cl'',evd = generalize_goal gl 0 ((AllOccurrences,c,body),Anonymous)
    (cl',project gl) in
  let args = instance_from_named_context to_quantify_rev in
  tclTHENLIST
    [tclEVARS evd;
     apply_type cl'' (if Option.is_empty body then c::args else args);
     thin (List.rev tothin')]
    gl

(**  *)
let generalize_gen_let lconstr gl =
  let newcl, evd =
    List.fold_right_i (generalize_goal gl) 0 lconstr
      (pf_concl gl,project gl)
  in
  tclTHEN (tclEVARS evd)
    (apply_type newcl (List.map_filter (fun ((_,c,b),_) ->
      if Option.is_empty b then Some c else None) lconstr)) gl

let new_generalize_gen_let lconstr =
  Proofview.Goal.enter begin fun gl ->
    let gl = Proofview.Goal.assume gl in
    let concl = Proofview.Goal.concl gl in
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let ids = Tacmach.New.pf_ids_of_hyps gl in
    let (newcl, sigma), args =
      List.fold_right_i 
	(fun i ((_,c,b),_ as o) (cl, args) ->
	  let t = Tacmach.New.pf_type_of gl c in
	  let args = if Option.is_empty b then c :: args else args in
	    generalize_goal_gen env ids i o t cl, args)
	0 lconstr ((concl, sigma), [])
    in
      Proofview.Unsafe.tclEVARS sigma <*>
	Proofview.Refine.refine begin fun sigma ->
          let (sigma, ev) = Evarutil.new_evar env sigma newcl in
            (sigma, (applist (ev, args)))
	end
  end

let generalize_gen lconstr =
  generalize_gen_let (List.map (fun ((occs,c),na) ->
    (occs,c,None),na) lconstr)

let new_generalize_gen lconstr =
  new_generalize_gen_let (List.map (fun ((occs,c),na) ->
    (occs,c,None),na) lconstr)
    
let generalize l =
  generalize_gen_let (List.map (fun c -> ((AllOccurrences,c,None),Anonymous)) l)

let new_generalize l =
  new_generalize_gen_let (List.map (fun c -> ((AllOccurrences,c,None),Anonymous)) l)

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

(*****************************)
(* Ad hoc unfold             *)
(*****************************)

(* The two following functions should already exist, but found nowhere *)
(* Unfolds x by its definition everywhere *)
let unfold_body x gl =
  let hyps = pf_hyps gl in
  let xval =
    match Context.lookup_named x hyps with
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

(* Either unfold and clear if defined or simply clear if not a definition *)
let expand_hyp id = tclTHEN (tclTRY (unfold_body id)) (clear [id])

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

  Strategy: (cf in [induction_with_atomization_of_ind_arg])
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
  if not (List.is_empty names) && Flags.is_verbose () then
    msg_warning
      (str"Unused introduction " ++ str (String.plural (List.length names) "pattern")
       ++ str": " ++ prlist_with_sep spc 
	 (Miscprint.pr_intro_pattern 
	    (fun c -> Printer.pr_constr (snd (c (Global.env()) Evd.empty)))) names)

let intropattern_of_name gl avoid = function
  | Anonymous -> IntroNaming IntroAnonymous
  | Name id -> IntroNaming (IntroIdentifier (new_fresh_id avoid id gl))

let rec consume_pattern avoid na isdep gl = function
  | [] -> ((dloc, intropattern_of_name gl avoid na), [])
  | (loc,IntroForthcoming true)::names when not isdep ->
      consume_pattern avoid na isdep gl names
  | (loc,IntroForthcoming _)::names as fullpat ->
      let avoid = avoid@explicit_intro_names names in
      ((loc,intropattern_of_name gl avoid na), fullpat)
  | (loc,IntroNaming IntroAnonymous)::names ->
      let avoid = avoid@explicit_intro_names names in
      ((loc,intropattern_of_name gl avoid na), names)
  | (loc,IntroNaming (IntroFresh id'))::names ->
      let avoid = avoid@explicit_intro_names names in
      ((loc,IntroNaming (IntroIdentifier (new_fresh_id avoid id' gl))), names)
  | pat::names -> (pat,names)

let re_intro_dependent_hypotheses (lstatus,rstatus) (_,tophyp) =
  let tophyp = match tophyp with None -> MoveLast | Some hyp -> MoveAfter hyp in
  let newlstatus = (* if some IH has taken place at the top of hyps *)
    List.map (function (hyp,MoveLast) -> (hyp,tophyp) | x -> x) lstatus
  in
  Tacticals.New.tclTHEN
    (intros_move rstatus)
    (intros_move newlstatus)

let dest_intro_patterns avoid thin dest pat tac =
  intro_patterns_core true avoid [] thin dest None 0 tac pat

let safe_dest_intro_patterns avoid thin dest pat tac =
  Proofview.tclORELSE
    (dest_intro_patterns avoid thin dest pat tac)
    begin function (e, info) -> match e with
      | UserError ("move_hyp",_) ->
       (* May happen e.g. with "destruct x using s" with an hypothesis
          which is morally an induction hypothesis to be "MoveLast" if
          known as such but which is considered instead as a subterm of
          a constructor to be move at the place of x. *)
          dest_intro_patterns avoid thin MoveLast pat tac
      | e -> Proofview.tclZERO ~info e
    end

type elim_arg_kind = RecArg | IndArg | OtherArg

type recarg_position =
  | AfterFixedPosition of Id.t option (* None = top of context *)

let update_dest (recargdests,tophyp as dests) = function
  | [] -> dests
  | hyp::_ ->
      (match recargdests with
        | AfterFixedPosition None -> AfterFixedPosition (Some hyp)
        | x -> x),
       (match tophyp with None -> Some hyp | x -> x)

let get_recarg_dest (recargdests,tophyp) =
  match recargdests with
  | AfterFixedPosition None -> MoveLast
  | AfterFixedPosition (Some id) -> MoveAfter id

(* Current policy re-introduces recursive arguments of destructed
   variable at the place of the original variable while induction
   hypothesese are introduced at the top of the context. Since in the
   general case of an inductive scheme, the induction hypotheses can
   arrive just after the recursive arguments (e.g. as in "forall
   t1:tree, P t1 -> forall t2:tree, P t2 -> P (node t1 t2)", we need
   to update the position for t2 after "P t1" is introduced if ever t2
   had to be introduced at the top of the context).
*)

let induct_discharge dests avoid' tac (avoid,ra) names =
  let avoid = avoid @ avoid' in
  let rec peel_tac ra dests names thin =
    match ra with
    | (RecArg,deprec,recvarname) ::
        (IndArg,depind,hyprecname) :: ra' ->
        Proofview.Goal.enter begin fun gl ->
        let (recpat,names) = match names with
          | [loc,IntroNaming (IntroIdentifier id) as pat] ->
              let id' = next_ident_away (add_prefix "IH" id) avoid in
	      (pat, [dloc, IntroNaming (IntroIdentifier id')])
          | _ -> consume_pattern avoid (Name recvarname) deprec gl names in
        let dest = get_recarg_dest dests in
        dest_intro_patterns avoid thin dest [recpat] (fun ids thin ->
        Proofview.Goal.enter begin fun gl ->
          let (hyprec,names) =
            consume_pattern avoid (Name hyprecname) depind gl names
          in
	  dest_intro_patterns avoid thin MoveLast [hyprec] (fun ids' thin ->
	    peel_tac ra' (update_dest dests ids') names thin)
        end)
        end
    | (IndArg,dep,hyprecname) :: ra' ->
        Proofview.Goal.enter begin fun gl ->
	(* Rem: does not happen in Coq schemes, only in user-defined schemes *)
        let pat,names =
          consume_pattern avoid (Name hyprecname) dep gl names in
	dest_intro_patterns avoid thin MoveLast [pat] (fun ids thin ->
        peel_tac ra' (update_dest dests ids) names thin)
        end
    | (RecArg,dep,recvarname) :: ra' ->
        Proofview.Goal.enter begin fun gl ->
        let (pat,names) =
          consume_pattern avoid (Name recvarname) dep gl names in
        let dest = get_recarg_dest dests in
	dest_intro_patterns avoid thin dest [pat] (fun ids thin ->
        peel_tac ra' dests names thin)
        end
    | (OtherArg,dep,_) :: ra' ->
        Proofview.Goal.enter begin fun gl ->
        let (pat,names) = consume_pattern avoid Anonymous dep gl names in
        let dest = get_recarg_dest dests in
	safe_dest_intro_patterns avoid thin dest [pat] (fun ids thin ->
        peel_tac ra' dests names thin)
        end
    | [] ->
        check_unused_names names;
        Tacticals.New.tclTHEN (clear_wildcards thin) (tac dests)
  in
  peel_tac ra dests names []

(* - le recalcul de indtyp à chaque itération de atomize_one est pour ne pas
     s'embêter à regarder si un letin_tac ne fait pas des
     substitutions aussi sur l'argument voisin *)

(* Marche pas... faut prendre en compte l'occurrence précise... *)

let atomize_param_of_ind_then (indref,nparams,_) hyp0 tac =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let tmptyp0 = Tacmach.New.pf_get_hyp_typ hyp0 (Proofview.Goal.assume gl) in
  let reduce_to_quantified_ref = Tacmach.New.pf_apply reduce_to_quantified_ref gl in
  let typ0 = reduce_to_quantified_ref indref tmptyp0 in
  let prods, indtyp = decompose_prod typ0 in
  let hd,argl = decompose_app indtyp in
  let params = List.firstn nparams argl in
  (* le gl est important pour ne pas préévaluer *)
  let rec atomize_one i args avoid =
    if Int.equal i nparams then
      let t = applist (hd, params@args) in
      Tacticals.New.tclTHEN
        (change_in_hyp None (fun sigma -> sigma, t) (hyp0,InHypTypeOnly))
        (tac avoid)
    else
      let c = List.nth argl (i-1) in
      match kind_of_term c with
	| Var id when not (List.exists (occur_var env id) args) &&
                      not (List.exists (occur_var env id) params) ->
            (* Based on the knowledge given by the user, all
               constraints on the variable are generalizable in the
               current environment so that it is clearable after destruction *)
	    atomize_one (i-1) (c::args) (id::avoid)
	| _ ->
            if List.exists (dependent c) params ||
               List.exists (dependent c) args
            then
              (* This is a case where the argument is constrained in a
                 way which would require some kind of inversion; we
                 follow the (old) discipline of not generalizing over
                 this term, since we don't try to invert the
                 constraint anyway. *)
	      atomize_one (i-1) (c::args) avoid
            else
            (* We reason blindly on the term and do as if it were
               generalizable, ignoring the constraints coming from
               its structure *)
            let id = match kind_of_term c with
            | Var id -> id
            | _ ->
            let type_of = Tacmach.New.pf_type_of gl in
            id_of_name_using_hdchar (Global.env()) (type_of c) Anonymous in
            let x = fresh_id_in_env avoid id env in
	    Tacticals.New.tclTHEN
	      (letin_tac None (Name x) c None allHypsAndConcl)
	      (atomize_one (i-1) (mkVar x::args) (x::avoid))
  in
  atomize_one (List.length argl) [] []
  end

let find_atomic_param_of_ind nparams indtyp =
  let argl = snd (decompose_app indtyp) in
  let params,args = List.chop nparams argl in
  let test c = isVar c && not (List.exists (dependent c) params) in
  List.map destVar (List.filter test args)

(* [cook_sign] builds the lists [beforetoclear] (preceding the
   ind. var.) and [aftertoclear] (coming after the ind. var.)  of hyps
   that must be erased, the lists of hyps to be generalize [decldeps] on the
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

   Other solutions are welcome

   PC 9 fev 06: Adapted to accept multi argument principle with no
   main arg hyp. hyp0 is now optional, meaning that it is possible
   that there is no main induction hypotheses. In this case, we
   consider the last "parameter" (in [indvars]) as the limit between
   "left" and "right", BUT it must be included in indhyps.

   Other solutions are still welcome

*)

exception Shunt of Id.t move_location

let cook_sign hyp0_opt inhyps indvars env =
  (* First phase from L to R: get [indhyps], [decldep] and [statuslist]
     for the hypotheses before (= more ancient than) hyp0 (see above) *)
  let toclear = ref [] in
  let avoid = ref [] in
  let decldeps = ref [] in
  let ldeps = ref [] in
  let rstatus = ref [] in
  let lstatus = ref [] in
  let before = ref true in
  let maindep = ref false in
  let seek_deps env (hyp,_,_ as decl) rhyp =
    if (match hyp0_opt with Some hyp0 -> Id.equal hyp hyp0 | _ -> false)
    then begin
      before:=false;
      (* Note that if there was no main induction hypotheses, then hyp
         is one of indvars too *)
      toclear := hyp::!toclear;
      MoveFirst (* fake value *)
    end else if Id.List.mem hyp indvars then begin
      (* The variables in indvars are such that they don't occur any
         more after generalization, so declare them to clear. *)
      toclear := hyp::!toclear;
      rhyp
    end else
      let dephyp0 = List.is_empty inhyps && 
	(Option.cata (fun id -> occur_var_in_decl env id decl) false hyp0_opt)
      in
      let depother = List.is_empty inhyps &&
	(List.exists (fun id -> occur_var_in_decl env id decl) indvars ||
         List.exists (fun (id,_,_) -> occur_var_in_decl env id decl) !decldeps)
      in
      if not (List.is_empty inhyps) && Id.List.mem hyp inhyps
         || dephyp0 || depother
      then begin
	decldeps := decl::!decldeps;
	avoid := hyp::!avoid;
        maindep := dephyp0 || !maindep;
	if !before then begin
          toclear := hyp::!toclear;
	  rstatus := (hyp,rhyp)::!rstatus
        end
	else begin
	  toclear := hyp::!toclear;
	  ldeps := hyp::!ldeps (* status computed in 2nd phase *)
        end;
	MoveBefore hyp end
      else
	MoveBefore hyp
  in
  let _ = fold_named_context seek_deps env ~init:MoveFirst in
  (* 2nd phase from R to L: get left hyp of [hyp0] and [lhyps] *)
  let compute_lstatus lhyp (hyp,_,_) =
    if (match hyp0_opt with Some hyp0 -> Id.equal hyp hyp0 | _ -> false) then
      raise (Shunt lhyp);
    if Id.List.mem hyp !ldeps then begin
      lstatus := (hyp,lhyp)::!lstatus;
      lhyp
    end else
      if Id.List.mem hyp !toclear then lhyp else MoveAfter hyp
  in
  try
    let _ =
      fold_named_context_reverse compute_lstatus ~init:MoveLast env in
    raise (Shunt MoveLast) (* ?? FIXME *)
  with Shunt lhyp0 ->
    let lhyp0 = match lhyp0 with
      | MoveLast -> None
      | MoveAfter hyp -> Some hyp
      | _ -> assert false in
    let statuslists = (!lstatus,List.rev !rstatus) in
    let recargdests = AfterFixedPosition (if Option.is_empty hyp0_opt then None else lhyp0) in
    (statuslists, (recargdests,None), !toclear, !decldeps, !avoid, !maindep)

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
  if Int.equal n 0 || Int.equal n 1 then id
  else
    (* This extends the name to accept new digits if it already ends with *)
    (* digits *)
    Id.of_string (atompart_of_id (make_ident (Id.to_string id) (Some 0)))

(* Builds two different names from an optional inductive type and a
   number, also deals with a list of names to avoid. If the inductive
   type is None, then hyprecname is IHi where i is a number. *)
let make_up_names n ind_opt cname =
  let is_hyp = String.equal (atompart_of_id cname) "H" in
  let base = Id.to_string (make_base n cname) in
  let ind_prefix = "IH" in
  let base_ind =
    if is_hyp then
      match ind_opt with
	| None -> Id.of_string ind_prefix
	| Some ind_id -> add_prefix ind_prefix (Nametab.basename_of_global ind_id)
    else add_prefix ind_prefix cname in
  let hyprecname = make_base n base_ind in
  let avoid =
    if Int.equal n 1 (* Only one recursive argument *) || Int.equal n 0 then []
    else
      (* Forbid to use cname, cname0, hyprecname and hyprecname0 *)
      (* in order to get names such as f1, f2, ... *)
      let avoid =
        (make_ident (Id.to_string hyprecname) None) ::
        (make_ident (Id.to_string hyprecname) (Some 0)) :: [] in
      if not (String.equal (atompart_of_id cname) "H") then
        (make_ident base (Some 0)) :: (make_ident base None) :: avoid
      else avoid in
  Id.of_string base, hyprecname, avoid

let error_ind_scheme s =
  let s = if not (String.is_empty s) then s^" " else s in
  error ("Cannot recognize "^s^"an induction scheme.")

let glob = Universes.constr_of_global

let coq_eq = lazy (glob (Coqlib.build_coq_eq ()))
let coq_eq_refl = lazy (glob (Coqlib.build_coq_eq_refl ()))

let coq_heq = lazy (Coqlib.coq_constant "mkHEq" ["Logic";"JMeq"] "JMeq")
let coq_heq_refl = lazy (Coqlib.coq_constant "mkHEq" ["Logic";"JMeq"] "JMeq_refl")


let mkEq t x y =
  mkApp (Lazy.force coq_eq, [| t; x; y |])

let mkRefl t x =
  mkApp (Lazy.force coq_eq_refl, [| t; x |])

let mkHEq t x u y =
  mkApp (Lazy.force coq_heq,
	[| t; x; u; y |])

let mkHRefl t x =
  mkApp (Lazy.force coq_heq_refl,
	[| t; x |])

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
    | Var id -> Id.Set.add id vars
    | App (f, args) ->
	(match kind_of_term f with
	| Construct ((ind,_),_)
	| Ind (ind,_) ->
            let (mib,mip) = Global.lookup_inductive ind in
	      Array.fold_left_from
		(if all then 0 else mib.Declarations.mind_nparams)
		aux vars args
	| _ -> fold_constr aux vars c)
    | _ -> fold_constr aux vars c
  in aux vars c

let decompose_indapp f args =
  match kind_of_term f with
  | Construct ((ind,_),_)
  | Ind (ind,_) ->
      let (mib,mip) = Global.lookup_inductive ind in
      let first = mib.Declarations.mind_nparams_rec in
      let pars, args = Array.chop first args in
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
  if Id.Set.is_empty hyps then []
  else
    let (_,lh) =
      Context.fold_named_context_reverse
        (fun (hs,hl) (x,_,_ as d) ->
	  if Id.Set.mem x nogen then (hs,hl)
	  else if Id.Set.mem x hs then (hs,x::hl)
	  else
	    let xvars = global_vars_set_of_decl env d in
	      if not (Id.Set.is_empty (Id.Set.diff xvars hs)) then
		(Id.Set.add x hs, x :: hl)
	      else (hs, hl))
        ~init:(hyps,[])
        sign
    in lh

exception Seen

let linear vars args =
  let seen = ref vars in
    try
      Array.iter (fun i ->
	let rels = ids_of_constr ~all:true Id.Set.empty i in
	let seen' =
	  Id.Set.fold (fun id acc ->
	    if Id.Set.mem id acc then raise Seen
	    else Id.Set.add id acc)
	    rels !seen
	in seen := seen')
	args;
      true
    with Seen -> false

let is_defined_variable env id = match lookup_named id env with
| (_, None, _) -> false
| (_, Some _, _) -> true

let abstract_args gl generalize_vars dep id defined f args =
  let sigma = project gl in
  let env = pf_env gl in
  let concl = pf_concl gl in
  let dep = dep || dependent (mkVar id) concl in
  let avoid = ref [] in
  let get_id name =
    let id = fresh_id !avoid (match name with Name n -> n | Anonymous -> Id.of_string "gen_x") gl in
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
    let ty = (* refresh_universes_strict *) ty in
    let lenctx = List.length ctx in
    let liftargty = lift lenctx argty in
    let leq = constr_cmp Reduction.CUMUL liftargty ty in
      match kind_of_term arg with
      | Var id when not (is_defined_variable env id) && leq && not (Id.Set.mem id nongenvars) ->
      	  (subst1 arg arity, ctx, ctxenv, mkApp (c, [|arg|]), args, eqs, refls,
      	  Id.Set.add id nongenvars, Id.Set.remove id vars, env)
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
	    nongenvars, Id.Set.union argvars vars, env)
  in
  let f', args' = decompose_indapp f args in
  let dogen, f', args' =
    let parvars = ids_of_constr ~all:true Id.Set.empty f' in
      if not (linear parvars args') then true, f, args
      else
	match Array.findi (fun i x -> not (isVar x) || is_defined_variable env (destVar x)) args' with
	| None -> false, f', args'
	| Some nonvar ->
	    let before, after = Array.chop nonvar args' in
	      true, mkApp (f', before), after
  in
    if dogen then
      let arity, ctx, ctxenv, c', args, eqs, refls, nogen, vars, env =
	Array.fold_left aux (pf_type_of gl f',[],env,f',[],[],[],Id.Set.empty,Id.Set.empty,env) args'
      in
      let args, refls = List.rev args, List.rev refls in
      let vars =
	if generalize_vars then
	  let nogen = Id.Set.add id nogen in
	    hyps_of_vars (pf_env gl) (pf_hyps gl) nogen vars
	else []
      in
      let body, c' = if defined then Some c', typ_of ctxenv Evd.empty c' else None, c' in
	Some (make_abstract_generalize gl id concl dep ctx body c' eqs args refls,
	     dep, succ (List.length ctx), vars)
    else None

let abstract_generalize ?(generalize_vars=true) ?(force_dep=false) id =
  Proofview.Goal.nf_enter begin fun gl ->
  Coqlib.check_required_library Coqlib.jmeq_module_name;
  let (f, args, def, id, oldid) =
    let oldid = Tacmach.New.pf_get_new_id id gl in
    let (_, b, t) = Tacmach.New.pf_get_hyp id gl in
      match b with
      | None -> let f, args = decompose_app t in
	        (f, args, false, id, oldid)
      | Some t ->
	  let f, args = decompose_app t in
	  (f, args, true, id, oldid)
  in
  if List.is_empty args then Proofview.tclUNIT ()
  else
    let args = Array.of_list args in
    let newc = Tacmach.New.of_old (fun gl -> abstract_args gl generalize_vars force_dep id def f args) gl in
      match newc with
      | None -> Proofview.tclUNIT ()
      | Some (newc, dep, n, vars) ->
	  let tac =
	    if dep then
	      Tacticals.New.tclTHENLIST [Proofview.V82.tactic (refine newc); rename_hyp [(id, oldid)]; Tacticals.New.tclDO n intro;
			   Proofview.V82.tactic (generalize_dep ~with_let:true (mkVar oldid))]
	    else
	      Tacticals.New.tclTHENLIST [Proofview.V82.tactic (refine newc); Proofview.V82.tactic (clear [id]); Tacticals.New.tclDO n intro]
	  in
	    if List.is_empty vars then tac
	    else Tacticals.New.tclTHEN tac
              (Tacticals.New.tclFIRST
                [revert vars ;
		 Proofview.V82.tactic (fun gl -> tclMAP (fun id ->
				     tclTRY (generalize_dep ~with_let:true (mkVar id))) vars gl)])
  end

let rec compare_upto_variables x y =
  if (isVar x || isRel x) && (isVar y || isRel y) then true
  else compare_constr compare_upto_variables x y

let specialize_eqs id gl =
  let env = pf_env gl in
  let ty = pf_get_hyp_typ gl id in
  let evars = ref (project gl) in
  let unif env evars c1 c2 =
    compare_upto_variables c1 c2 && Evarconv.e_conv env evars c1 c2
  in
  let rec aux in_eqs ctx acc ty =
    match kind_of_term ty with
    | Prod (na, t, b) ->
	(match kind_of_term t with
	| App (eq, [| eqty; x; y |]) when Term.eq_constr (Lazy.force coq_eq) eq ->
	    let c = if noccur_between 1 (List.length ctx) x then y else x in
	    let pt = mkApp (Lazy.force coq_eq, [| eqty; c; c |]) in
	    let p = mkApp (Lazy.force coq_eq_refl, [| eqty; c |]) in
	      if unif (push_rel_context ctx env) evars pt t then
		aux true ctx (mkApp (acc, [| p |])) (subst1 p b)
	      else acc, in_eqs, ctx, ty
	| App (heq, [| eqty; x; eqty'; y |]) when Term.eq_constr heq (Lazy.force coq_heq) ->
	    let eqt, c = if noccur_between 1 (List.length ctx) x then eqty', y else eqty, x in
	    let pt = mkApp (Lazy.force coq_heq, [| eqt; c; eqt; c |]) in
	    let p = mkApp (Lazy.force coq_heq_refl, [| eqt; c |]) in
	      if unif (push_rel_context ctx env) evars pt t then
		aux true ctx (mkApp (acc, [| p |])) (subst1 p b)
	      else acc, in_eqs, ctx, ty
	| _ ->
	    if in_eqs then acc, in_eqs, ctx, ty
	    else
	      let e = e_new_evar (push_rel_context ctx env) evars t in
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
	(exact_no_check ((* refresh_universes_strict *) acc')) gl
    else tclFAIL 0 (str "Nothing to do in hypothesis " ++ pr_id id) gl


let specialize_eqs id gl =
  if
    (try ignore(clear [id] gl); false
     with e when Errors.noncritical e -> true)
  then
    tclFAIL 0 (str "Specialization not allowed on dependent hypotheses") gl
  else specialize_eqs id gl

let occur_rel n c =
  let res = not (noccurn n c) in
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
  match acc2 with
  | [] ->
    let hyps,ccl = decompose_prod_assum elimt in
    let hd_ccl_pred,_ = decompose_app ccl in
    begin match kind_of_term hd_ccl_pred with
      | Rel i  -> let acc3,acc1 = List.chop (i-1) hyps in acc1 , [] , acc3 , ccl
      | _ -> error_ind_scheme ""
    end
  | _ -> acc1, acc2 , acc3, ccl


let exchange_hd_app subst_hd t =
  let hd,args= decompose_app t in mkApp (subst_hd,Array.of_list args)

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

  let ccl = exchange_hd_app (mkVar (Id.of_string "__QI_DUMMY__")) conclusion in
  let concl_with_args = it_mkProd_or_LetIn ccl args_indargs in
  let nparams = Int.Set.cardinal (free_rels concl_with_args) in
  let preds,params = List.chop (List.length params_preds - nparams) params_preds in

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
    if Int.equal !res.nargs 0 then raise Exit;
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
	      Int.equal (List.length hi_args) (List.length params + !res.nargs -1) in
	    (* FIXME: Ces deux tests ne sont pas suffisants. *)
	    if not (hi_is_ind && hi_args_enough) then raise Exit (* No indarg *)
	    else (* Last arg is the indarg *)
	      res := {!res with
		indarg = Some (List.hd !res.args);
		indarg_in_concl = occur_rel 1 ccl;
		args = List.tl !res.args; nargs = !res.nargs - 1;
	      };
	    raise Exit);
    raise Exit(* exit anyway *)
  with Exit -> (* Ending by computing indref: *)
    match !res.indarg with
      | None -> !res (* No indref *)
      | Some ( _,Some _,_) -> error_ind_scheme ""
      | Some ( _,None,ind) ->
	  let indhd,indargs = decompose_app ind in
	  try {!res with indref = Some (global_of_constr indhd) }
	  with e when Errors.noncritical e ->
            error "Cannot find the inductive type of the inductive scheme."

let compute_scheme_signature scheme names_info ind_type_guess =
  let f,l = decompose_app scheme.concl in
  (* Vérifier que les arguments de Qi sont bien les xi. *)
  let cond, check_concl =
    match scheme.indarg with
      | Some (_,Some _,_) ->
	  error "Strange letin, cannot recognize an induction scheme."
      | None -> (* Non standard scheme *)
	  let cond hd = Term.eq_constr hd ind_type_guess && not scheme.farg_in_concl
	  in (cond, fun _ _ -> ())
      | Some ( _,None,ind) -> (* Standard scheme from an inductive type *)
	  let indhd,indargs = decompose_app ind in
	  let cond hd = Term.eq_constr hd indhd in
	  let check_concl is_pred p =
	    (* Check again conclusion *)
	    let ccl_arg_ok = is_pred (p + scheme.nargs + 1) f == IndArg in
	    let ind_is_ok =
	      List.equal Term.eq_constr
		(List.lastn scheme.nargs indargs)
		(extended_rel_list 0 scheme.args) in
	    if not (ccl_arg_ok && ind_is_ok) then
	      error_ind_scheme "the conclusion of"
	  in (cond, check_concl)
  in
  let is_pred n c =
    let hd = fst (decompose_app c) in
    match kind_of_term hd with
      | Rel q when n < q && q <= n+scheme.npredicates -> IndArg
      | _ when cond hd -> RecArg
      | _ -> OtherArg
  in
  let rec check_branch p c =
    match kind_of_term c with
      | Prod (_,t,c) ->
	(is_pred p t, dependent (mkRel 1) c) :: check_branch (p+1) c
      | LetIn (_,_,_,c) ->
	(OtherArg, dependent (mkRel 1) c) :: check_branch (p+1) c
      | _ when is_pred p c == IndArg -> []
      | _ -> raise Exit
  in
  let rec find_branches p lbrch =
    match lbrch with
      | (_,None,t)::brs ->
	(try
	   let lchck_brch = check_branch p t in
	   let n = List.fold_left
	     (fun n (b,_) -> if b == RecArg then n+1 else n) 0 lchck_brch in
	   let recvarname, hyprecname, avoid =
	     make_up_names n scheme.indref names_info in
	   let namesign =
	     List.map (fun (b,dep) ->
	       (b, dep, if b == IndArg then hyprecname else recvarname))
	       lchck_brch in
	   (avoid,namesign) :: find_branches (p+1) brs
	 with Exit-> error_ind_scheme "the branches of")
      | (_,Some _,_)::_ -> error_ind_scheme "the branches of"
      | [] -> check_concl is_pred p; []
  in
  Array.of_list (find_branches 0 (List.rev scheme.branches))

(* Check that the elimination scheme has a form similar to the
   elimination schemes built by Coq. Schemes may have the standard
   form computed from an inductive type OR (feb. 2006) a non standard
   form. That is: with no main induction argument and with an optional
   extra final argument of the form (f x y ...) in the conclusion. In
   the non standard case, naming of generated hypos is slightly
   different. *)
let compute_elim_signature (evd,(elimc,elimt),ind_type_guess) names_info =
  let scheme = compute_elim_sig ~elimc:elimc elimt in
    evd, (compute_scheme_signature scheme names_info ind_type_guess, scheme)

let guess_elim isrec dep s hyp0 gl =
  let tmptyp0 =	Tacmach.New.pf_get_hyp_typ hyp0 gl in
  let mind,_ = Tacmach.New.pf_reduce_to_quantified_ind gl tmptyp0 in
  let evd, elimc =
    if isrec && not (is_nonrec (fst mind)) then find_ind_eliminator (fst mind) s gl
    else
      if use_dependent_propositions_elimination () && dep
      then
	Tacmach.New.pf_apply build_case_analysis_scheme gl mind true s
      else
	Tacmach.New.pf_apply build_case_analysis_scheme_default gl mind s in
  let elimt = Tacmach.New.pf_type_of gl elimc in
    evd, ((elimc, NoBindings), elimt), mkIndU mind

let given_elim hyp0 (elimc,lbind as e) gl =
  let tmptyp0 = Tacmach.New.pf_get_hyp_typ hyp0 gl in
  let ind_type_guess,_ = decompose_app ((strip_prod tmptyp0)) in
  Proofview.Goal.sigma gl, (e, Tacmach.New.pf_type_of gl elimc), ind_type_guess

type scheme_signature =
    (Id.t list * (elim_arg_kind * bool * Id.t) list) array

type eliminator_source =
  | ElimUsing of (eliminator * types) * scheme_signature
  | ElimOver of bool * Id.t

let find_induction_type isrec elim hyp0 gl =
  let scheme,elim =
    match elim with
    | None ->
       let sort = Tacticals.New.elimination_sort_of_goal gl in
       let _, (elimc,elimt),_ = 
	 guess_elim isrec (* dummy: *) true sort hyp0 gl in
	let scheme = compute_elim_sig ~elimc elimt in
	(* We drop the scheme waiting to know if it is dependent *)
	scheme, ElimOver (isrec,hyp0)
    | Some e ->
	let evd, (elimc,elimt),ind_guess = given_elim hyp0 e gl in
	let scheme = compute_elim_sig ~elimc elimt in
	if Option.is_empty scheme.indarg then error "Cannot find induction type";
	let indsign = compute_scheme_signature scheme hyp0 ind_guess in
	let elim = ({elimindex = Some(-1); elimbody = elimc; elimrename = None},elimt) in
	scheme, ElimUsing (elim,indsign) in
  (Option.get scheme.indref,scheme.nparams, elim)

let get_elim_signature elim hyp0 gl =
  compute_elim_signature (given_elim hyp0 elim gl) hyp0

let is_functional_induction elimc gl =
  let scheme = compute_elim_sig ~elimc (Tacmach.New.pf_type_of gl (fst elimc)) in
  (* The test is not safe: with non-functional induction on non-standard
     induction scheme, this may fail *)
  Option.is_empty scheme.indarg

(* Wait the last moment to guess the eliminator so as to know if we
   need a dependent one or not *)

let get_eliminator elim dep s gl = match elim with
  | ElimUsing (elim,indsign) ->
      Proofview.Goal.sigma gl, (* bugged, should be computed *) true, elim, indsign
  | ElimOver (isrec,id) ->
      let evd, (elimc,elimt),_ as elims = guess_elim isrec dep s id gl in
      let _, (l, s) = compute_elim_signature elims id in
      let branchlengthes = List.map (fun (_,b,c) -> assert (b=None); pi1 (decompose_prod_letin c)) (List.rev s.branches) in
      evd, isrec, ({elimindex = None; elimbody = elimc; elimrename = Some (isrec,Array.of_list branchlengthes)}, elimt), l

(* Instantiate all meta variables of elimclause using lid, some elts
   of lid are parameters (first ones), the other are
   arguments. Returns the clause obtained.  *)
let recolle_clenv i params args elimclause gl =
  let _,arr = destApp elimclause.templval.rebus in
  let lindmv =
    Array.map
      (fun x ->
	match kind_of_term x with
	  | Meta mv -> mv
	  | _  -> errorlabstrm "elimination_clause"
              (str "The type of the elimination clause is not well-formed."))
      arr in
  let k = match i with -1 -> Array.length lindmv - List.length args | _ -> i in
  (* parameters correspond to first elts of lid. *)
  let clauses_params =
    List.map_i (fun i id -> mkVar id , pf_get_hyp_typ gl id , lindmv.(i))
      0 params in
  let clauses_args =
    List.map_i (fun i id -> mkVar id , pf_get_hyp_typ gl id , lindmv.(k+i))
      0 args in
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
let induction_tac with_evars params indvars elim gl =
  let ({elimindex=i;elimbody=(elimc,lbindelimc);elimrename=rename},elimt) = elim in
  let i = match i with None -> index_of_ind_arg elimt | Some i -> i in
  (* elimclause contains this: (elimc ?i ?j ?k...?l) *)
  let elimc = mkCast (elimc, DEFAULTcast, elimt) in
  let elimclause =
    pf_apply make_clenv_binding gl (elimc,elimt) lbindelimc in
  (* elimclause' is built from elimclause by instanciating all args and params. *)
  let elimclause' = recolle_clenv i params indvars elimclause gl in
  (* one last resolution (useless?) *)
  let resolved = clenv_unique_resolver ~flags:(elim_flags ()) elimclause' gl in
  Proofview.V82.of_tactic (enforce_prop_bound_names rename (Clenvtac.clenv_refine with_evars resolved)) gl

(* Apply induction "in place" taking into account dependent
   hypotheses from the context, replacing the main hypothesis on which
   induction applies with the induction hypotheses *)

let apply_induction_in_context hyp0 inhyps elim indvars names induct_tac =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let concl = Tacmach.New.pf_nf_concl gl in
    let statuslists,lhyp0,toclear,deps,avoid,dep = cook_sign hyp0 inhyps indvars env in
    let dep = dep || Option.cata (fun id -> occur_var env id concl) false hyp0 in
    let tmpcl = it_mkNamedProd_or_LetIn concl deps in
    let s = Retyping.get_sort_family_of env sigma tmpcl in
    let deps_cstr =
      List.fold_left
        (fun a (id,b,_) -> if Option.is_empty b then (mkVar id)::a else a) [] deps in
    let (sigma, isrec, elim, indsign) = get_eliminator elim dep s (Proofview.Goal.assume gl) in
    let names = compute_induction_names (Array.length indsign) names in
    (if isrec then Tacticals.New.tclTHENFIRSTn else Tacticals.New.tclTHENLASTn)
      (Tacticals.New.tclTHENLIST [
        Proofview.Unsafe.tclEVARS sigma;
        (* Generalize dependent hyps (but not args) *)
        if deps = [] then Proofview.tclUNIT () else Proofview.V82.tactic (apply_type tmpcl deps_cstr);
        (* side-conditions in elim (resp case) schemes come last (resp first) *)
        induct_tac elim;
        Proofview.V82.tactic (tclMAP expand_hyp toclear)
      ])
      (Array.map2
         (induct_discharge lhyp0 avoid (re_intro_dependent_hypotheses statuslists))
         indsign names)
  end

let induction_with_atomization_of_ind_arg isrec with_evars elim names hyp0 inhyps =
  Proofview.Goal.enter begin fun gl ->
  let elim_info = find_induction_type isrec elim hyp0 (Proofview.Goal.assume gl) in
  atomize_param_of_ind_then elim_info hyp0 (fun indvars ->
    apply_induction_in_context (Some hyp0) inhyps (pi3 elim_info) indvars names
      (fun elim -> Proofview.V82.tactic (induction_tac with_evars [] [hyp0] elim)))
  end

let msg_not_right_number_induction_arguments scheme =
  str"Not the right number of induction arguments (expected " ++
  pr_enum (fun x -> x) [
    if scheme.farg_in_concl then str "the function name" else mt();
    if scheme.nparams != 0 then int scheme.nparams ++ str (String.plural scheme.nparams " parameter") else mt ();
    if scheme.nargs != 0 then int scheme.nargs ++ str (String.plural scheme.nargs " argument") else mt ()] ++ str ")."

(* Induction on a list of induction arguments. Analyze the elim
   scheme (which is mandatory for multiple ind args), check that all
   parameters and arguments are given (mandatory too).
   Main differences with induction_from_context is that there is no
   main induction argument. On the other hand, all args and params
   must be given, so we help a bit the unifier by making the "pattern"
   by hand before calling induction_tac *)
let induction_without_atomization isrec with_evars elim names lid =
  Proofview.Goal.nf_enter begin fun gl ->
  let sigma, (indsign,scheme) = get_elim_signature elim (List.hd lid) gl in
  let nargs_indarg_farg =
    scheme.nargs + (if scheme.farg_in_concl then 1 else 0) in
  if not (Int.equal (List.length lid) (scheme.nparams + nargs_indarg_farg))
  then
    Tacticals.New.tclZEROMSG (msg_not_right_number_induction_arguments scheme)
  else
  let indvars,lid_params = List.chop nargs_indarg_farg lid in
  (* terms to patternify we must patternify indarg or farg if present in concl *)
  let realindvars = List.rev (if scheme.farg_in_concl then List.tl indvars else indvars) in
  let lidcstr = List.map mkVar (List.rev indvars) in
  let params = List.rev lid_params in
  let indvars =
    (* Temporary hack for compatibility, while waiting for better
       analysis of the form of induction schemes: a scheme like
       gt_wf_rec was taken as a functional scheme with no parameters,
       but by chance, because of the addition of at least hyp0 for
       cook_sign, it behaved as if there was a real induction arg. *)
    if indvars = [] then [List.hd lid_params] else indvars in
  let induct_tac elim = Proofview.V82.tactic (tclTHENLIST [
    (* pattern to make the predicate appear. *)
    reduce (Pattern (List.map inj_with_occurrences lidcstr)) onConcl;
    (* Induction by "refine (indscheme ?i ?j ?k...)" + resolution of all
       possible holes using arguments given by the user (but the
       functional one). *)
    (* FIXME: Tester ca avec un principe dependant et non-dependant *)
    induction_tac with_evars params realindvars elim
  ]) in
  let elim = ElimUsing (({elimindex = Some (-1); elimbody = Option.get scheme.elimc; elimrename = None}, scheme.elimt), indsign) in
  apply_induction_in_context None [] elim indvars names induct_tac
  end

(* assume that no occurrences are selected *)
let clear_unselected_context id inhyps cls gl =
  if occur_var (pf_env gl) id (pf_concl gl) &&
    cls.concl_occs == NoOccurrences
  then errorlabstrm ""
    (str "Conclusion must be mentioned: it depends on " ++ pr_id id
     ++ str ".");
  match cls.onhyps with
  | Some hyps ->
      let to_erase (id',_,_ as d) =
	if Id.List.mem id' inhyps then (* if selected, do not erase *) None
	else
	  (* erase if not selected and dependent on id or selected hyps *)
	  let test id = occur_var_in_decl (pf_env gl) id d in
	  if List.exists test (id::inhyps) then Some id' else None in
      let ids = List.map_filter to_erase (pf_hyps gl) in
      thin ids gl
  | None -> tclIDTAC gl

let use_bindings env sigma elim (c,lbind) typ =
  let typ =
    if elim == None then
      (* w/o an scheme, the term has to be applied at least until
         obtaining an inductive type (even though the arity might be
         known only by pattern-matching, as in the case of a term of
         the form "nat_rect ?A ?o ?s n", with ?A to be inferred by
         matching. *)
      let sign,t = splay_prod env sigma typ in it_mkProd t sign
    else
      (* Otherwise, we exclude the case of an induction argument in an
         explicitly functional type. Henceforth, we can complete the
         pattern until it has as type an atomic type (even though this
         atomic type can hide a functional type, for which the "using"
         clause has a scheme). *)
      typ in
  let rec find_clause typ =
    try
      let indclause = make_clenv_binding env sigma (c,typ) lbind in
      (* We lose the possibility of coercions in with-bindings *)
      pose_all_metas_as_evars env indclause.evd (clenv_value indclause)
    with e when catchable_exception e ->
    try find_clause (try_red_product env sigma typ)
    with Redelimination -> raise e in
  find_clause typ

let check_expected_type env sigma (elimc,bl) elimt =
  (* Compute the expected template type of the term in case a using
     clause is given *)
  let sign,_ = splay_prod env sigma elimt in
  let n = List.length sign in
  if n == 0 then error "Scheme cannot be applied.";
  let sigma,cl = make_evar_clause env sigma ~len:(n - 1) elimt in
  let sigma = solve_evar_clause env sigma true cl bl in
  let (_,u,_) = destProd cl.cl_concl in
  fun t -> Evarconv.e_cumul env (ref sigma) t u

let check_enough_applied env sigma elim =
  (* A heuristic to decide whether the induction arg is enough applied *)
  match elim with
  | None ->
      (* No eliminator given *)
      fun u ->
      let t,_ = decompose_app (whd_betadeltaiota env sigma u) in isInd t
  | Some elimc ->
      let elimt = typ_of env sigma (fst elimc) in
      let scheme = compute_elim_sig ~elimc elimt in
      match scheme.indref with
      | None ->
         (* in the absence of information, do not assume it may be
            partially applied *)
          fun _ -> true
      | Some _ ->
          (* Last argument is supposed to be the induction argument *)
          check_expected_type env sigma elimc elimt

let pose_induction_arg_then isrec with_evars (is_arg_pure_hyp,from_prefix) elim
     id ((pending,(c0,lbind)),(eqname,names)) t0 inhyps cls tac =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let ccl = Proofview.Goal.raw_concl gl in
  let store = Proofview.Goal.extra gl in
  let check = check_enough_applied env sigma elim in
  let (sigma',c) = use_bindings env sigma elim (c0,lbind) t0 in
  let abs = AbstractPattern (from_prefix,check,Name id,(pending,c),cls,false) in
  let (id,sign,_,lastlhyp,ccl,res) = make_abstraction env sigma' ccl abs in
  match res with
  | None ->
      (* pattern not found *)
      let with_eq = Option.map (fun eq -> (false,eq)) eqname in
      (* we restart using bindings after having tried type-class
         resolution etc. on the term given by the user *)
      let flags = tactic_infer_flags (with_evars && (* do not give a success semantics to edestruct on an open term yet *) false) in
      let (sigma,c0) = finish_evar_resolution ~flags env sigma (pending,c0) in
      (if isrec then
          (* Historically, induction has side conditions last *)
          Tacticals.New.tclTHENFIRST
       else
          (* and destruct has side conditions first *)
          Tacticals.New.tclTHENLAST)
      (Tacticals.New.tclTHENLIST [
        Proofview.Unsafe.tclEVARS sigma;
        Proofview.Refine.refine ~unsafe:true (fun sigma ->
          let (sigma,c) = use_bindings env sigma elim (c0,lbind) t0 in
          let t = Retyping.get_type_of env sigma c in
          mkletin_goal env sigma store with_eq false (id,lastlhyp,ccl,c) (Some t));
        Proofview.(if with_evars then shelve_unifiable else guard_no_unifiable);
        if is_arg_pure_hyp
        then Tacticals.New.tclTRY (Proofview.V82.tactic (thin [destVar c0]))
        else Proofview.tclUNIT ();
        if isrec then Proofview.cycle (-1) else Proofview.tclUNIT ()
      ])
      tac

  | Some (sigma',c) ->
      (* pattern found *)
      let with_eq = Option.map (fun eq -> (false,eq)) eqname in
      (* TODO: if ind has predicate parameters, use JMeq instead of eq *)
      let env = reset_with_named_context sign env in
      Tacticals.New.tclTHENLIST [
        Proofview.Unsafe.tclEVARS sigma';
        Proofview.Refine.refine ~unsafe:true (fun sigma ->
          mkletin_goal env sigma store with_eq true (id,lastlhyp,ccl,c) None);
        tac
      ]
  end

let has_generic_occurrences_but_goal cls id env ccl =
  clause_with_generic_context_selection cls &&
  (* TODO: whd_evar of goal *)
  (cls.concl_occs != NoOccurrences || not (occur_var env id ccl))

let induction_gen clear_flag isrec with_evars elim
    ((_pending,(c,lbind)),(eqname,names) as arg) cls =
  let inhyps = match cls with
  | Some {onhyps=Some hyps} -> List.map (fun ((_,id),_) -> id) hyps
  | _ -> [] in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let ccl = Proofview.Goal.raw_concl gl in
  let cls = Option.default allHypsAndConcl cls in
  let t = typ_of env sigma c in
  let is_arg_pure_hyp =
    isVar c && not (mem_named_context (destVar c) (Global.named_context()))
    && lbind == NoBindings && not with_evars && Option.is_empty eqname
    && clear_flag == None
    && has_generic_occurrences_but_goal cls (destVar c) env ccl in
  let enough_applied = check_enough_applied env sigma elim t in
  if is_arg_pure_hyp && enough_applied then
    (* First case: induction on a variable already in an inductive type and
       with maximal abstraction over the variable.
       This is a situation where the induction argument is a
       clearable variable of the goal w/o occurrence selection
       and w/o equality kept: no need to generalize *)
    let id = destVar c in
    Tacticals.New.tclTHEN
      (Proofview.V82.tactic (clear_unselected_context id inhyps cls))
      (induction_with_atomization_of_ind_arg
         isrec with_evars elim names id inhyps)
  else
  (* Otherwise, we look for the pattern, possibly adding missing arguments and
     declaring the induction argument as a new local variable *)
    let id =
    (* Type not the right one if partially applied but anyway for internal use*)
      let x = id_of_name_using_hdchar (Global.env()) t Anonymous in
      new_fresh_id [] x gl in
    let info_arg = (is_arg_pure_hyp, not enough_applied) in
    pose_induction_arg_then
      isrec with_evars info_arg elim id arg t inhyps cls
    (induction_with_atomization_of_ind_arg
       isrec with_evars elim names id inhyps)
  end

(* Induction on a list of arguments. First make induction arguments
   atomic (using letins), then do induction. The specificity here is
   that all arguments and parameters of the scheme are given
   (mandatory for the moment), so we don't need to deal with
    parameters of the inductive type as in induction_gen. *)
let induction_gen_l isrec with_evars elim names lc =
  let newlc = ref [] in
  let lc = List.map (function
    | (c,None) -> c
    | (c,Some(loc,eqname)) ->
      user_err_loc (loc,"",str "Do not know what to do with " ++
                         Miscprint.pr_intro_pattern_naming eqname)) lc in
  let rec atomize_list l =
    match l with
      | [] -> Proofview.tclUNIT ()
      | c::l' ->
	  match kind_of_term c with
	    | Var id when not (mem_named_context id (Global.named_context()))
		&& not with_evars ->
		let _ = newlc:= id::!newlc in
		atomize_list l'

	    | _ ->
                Proofview.Goal.enter begin fun gl ->
                let type_of = Tacmach.New.pf_type_of gl in
                let x =
		  id_of_name_using_hdchar (Global.env()) (type_of c) Anonymous in

                let id = new_fresh_id [] x gl in
		let newl' = List.map (replace_term c (mkVar id)) l' in
		let _ = newlc:=id::!newlc in
		Tacticals.New.tclTHEN
		  (letin_tac None (Name id) c None allHypsAndConcl)
		  (atomize_list newl')
                end in
  Tacticals.New.tclTHENLIST
    [
      (atomize_list lc);
      (Proofview.tclUNIT () >>= fun () -> (* ensure newlc has been computed *)
	induction_without_atomization isrec with_evars elim names !newlc)
    ]

(* Induction either over a term, over a quantified premisse, or over
   several quantified premisses (like with functional induction
   principles).
   TODO: really unify induction with one and induction with several
   args *)
let induction_destruct isrec with_evars (lc,elim) =
  match lc with
  | [] -> assert false (* ensured by syntax, but if called inside caml? *)
  | [c,(eqname,names as allnames),cls] ->
    Proofview.Goal.nf_enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    match elim with
    | Some elim when is_functional_induction elim gl ->
      (* Standard induction on non-standard induction schemes *)
      (* will be removable when is_functional_induction will be more clever *)
      if not (Option.is_empty cls) then error "'in' clause not supported here.";
      let finish_evar_resolution f =
        let (sigma',(c,lbind)) = f env sigma in
        let pending = (sigma,sigma') in
        snd (finish_evar_resolution env sigma' (pending,c)),lbind in
      let c = map_induction_arg finish_evar_resolution c in
      onInductionArg
	(fun _clear_flag (c,lbind) ->
	  if lbind != NoBindings then
	    error "'with' clause not supported here.";
	  induction_gen_l isrec with_evars elim names [c,eqname]) c
    | _ ->
      (* standard induction *)
      onOpenInductionArg env sigma
      (fun clear_flag c -> induction_gen clear_flag isrec with_evars elim (c,allnames) cls) c
    end
  | _ ->
    Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    match elim with
    | None ->
      (* Several arguments, without "using" clause *)
      (* TODO: Do as if the arguments after the first one were called with *)
      (* "destruct", but selecting occurrences on the initial copy of *)
      (* the goal *)
      let (a,b,cl) = List.hd lc in
      let l = List.tl lc in
      (* TODO *)
      Tacticals.New.tclTHEN
        (onOpenInductionArg env sigma (fun clear_flag a ->
          induction_gen clear_flag isrec with_evars None (a,b) cl) a)
        (Tacticals.New.tclMAP (fun (a,b,cl) ->
          Proofview.Goal.enter begin fun gl ->
          let env = Proofview.Goal.env gl in
          let sigma = Proofview.Goal.sigma gl in      
          onOpenInductionArg env sigma (fun clear_flag a ->
            induction_gen clear_flag false with_evars None (a,b) cl) a
          end) l)
    | Some elim ->
      (* Several induction hyps with induction scheme *)
      let finish_evar_resolution f =
        let (sigma',(c,lbind)) = f env sigma in
        let pending = (sigma,sigma') in
	if lbind != NoBindings then
	  error "'with' clause not supported here.";
        snd (finish_evar_resolution env sigma' (pending,c)) in
      let lc = List.map (on_pi1 (map_induction_arg finish_evar_resolution)) lc in
      let newlc =
        List.map (fun (x,(eqn,names),cls) ->
          if cls != None then error "'in' clause not yet supported here.";
	  match x with (* FIXME: should we deal with ElimOnIdent? *)
          | _clear_flag,ElimOnConstr x ->
              if eqn <> None then error "'eqn' clause not supported here.";
              (x,names)
	  | _ -> error "Don't know where to find some argument.")
	  lc in
      (* Check that "as", if any, is given only on the last argument *)
      let names,rest = List.sep_last (List.map snd newlc) in
      if List.exists (fun n -> not (Option.is_empty n)) rest then
        error "'as' clause with multiple arguments and 'using' clause can only occur last.";
      let newlc = List.map (fun (x,_) -> (x,None)) newlc in
      induction_gen_l isrec with_evars elim names newlc
    end

let induction ev clr c l e =
  induction_gen clr true ev e 
    (((Evd.empty,Evd.empty),(c,NoBindings)),(None,l)) None

let destruct ev clr c l e =
  induction_gen clr false ev e
    (((Evd.empty,Evd.empty),(c,NoBindings)),(None,l)) None

(* The registered tactic, which calls the default elimination
 * if no elimination constant is provided. *)

(* Induction tactics *)

(* This was Induction before 6.3 (induction only in quantified premisses) *)
let simple_induct_id s = Tacticals.New.tclTHEN (intros_until_id s) (Tacticals.New.onLastHyp simplest_elim)
let simple_induct_nodep n = Tacticals.New.tclTHEN (intros_until_n n) (Tacticals.New.onLastHyp simplest_elim)

let simple_induct = function
  | NamedHyp id -> simple_induct_id id
  | AnonHyp n -> simple_induct_nodep n

(* Destruction tactics *)

let simple_destruct_id s    =
  (Tacticals.New.tclTHEN (intros_until_id s) (Tacticals.New.onLastHyp simplest_case))
let simple_destruct_nodep n =
  (Tacticals.New.tclTHEN (intros_until_n n)    (Tacticals.New.onLastHyp simplest_case))

let simple_destruct = function
  | NamedHyp id -> simple_destruct_id id
  | AnonHyp n -> simple_destruct_nodep n

(*
 *  Eliminations giving the type instead of the proof.
 * These tactics use the default elimination constant and
 * no substitutions at all.
 * May be they should be integrated into Elim ...
 *)

let elim_scheme_type elim t =
  Proofview.Goal.nf_enter begin fun gl ->
  let clause = Tacmach.New.of_old (fun gl -> mk_clenv_type_of gl elim) gl in
  match kind_of_term (last_arg clause.templval.rebus) with
    | Meta mv ->
        let clause' =
	  (* t is inductive, then CUMUL or CONV is irrelevant *)
	  clenv_unify ~flags:(elim_flags ()) Reduction.CUMUL t
            (clenv_meta_type clause mv) clause in
	Clenvtac.res_pf clause' ~flags:(elim_flags ()) ~with_evars:false
    | _ -> anomaly (Pp.str "elim_scheme_type")
  end

let elim_type t =
  Proofview.Goal.enter begin fun gl ->
  let (ind,t) = Tacmach.New.pf_apply reduce_to_atomic_ind gl t in
  let evd, elimc = find_ind_eliminator (fst ind) (Tacticals.New.elimination_sort_of_goal gl) gl in
  Tacticals.New.tclTHEN (Proofview.Unsafe.tclEVARS evd) (elim_scheme_type elimc t)
  end

let case_type t =
  Proofview.Goal.enter begin fun gl ->
  let (ind,t) = Tacmach.New.pf_apply reduce_to_atomic_ind gl t in
  let evd, elimc =
    Tacmach.New.pf_apply build_case_analysis_scheme_default gl ind (Tacticals.New.elimination_sort_of_goal gl)
  in
  Tacticals.New.tclTHEN (Proofview.Unsafe.tclEVARS evd) (elim_scheme_type elimc t)
  end


(************************************************)
(*  Tactics related with logic connectives      *)
(************************************************)

(* Reflexivity tactics *)

let (forward_setoid_reflexivity, setoid_reflexivity) = Hook.make ()

let maybe_betadeltaiota_concl allowred gl =
  let concl = Tacmach.New.pf_nf_concl gl in
  let sigma = Proofview.Goal.sigma gl in
  if not allowred then concl
  else
    let env = Proofview.Goal.env gl in
    whd_betadeltaiota env sigma concl

let reflexivity_red allowred =
  Proofview.Goal.enter begin fun gl ->
  (* PL: usual reflexivity don't perform any reduction when searching
     for an equality, but we may need to do some when called back from
     inside setoid_reflexivity (see Optimize cases in setoid_replace.ml). *)
    let concl = maybe_betadeltaiota_concl allowred gl in
    match match_with_equality_type concl with
    | None -> Proofview.tclZERO NoEquationFound
    | Some _ -> one_constructor 1 NoBindings
  end

let reflexivity =
  Proofview.tclORELSE
    (reflexivity_red false)
    begin function (e, info) -> match e with
      | NoEquationFound -> Hook.get forward_setoid_reflexivity
      | e -> Proofview.tclZERO ~info e
    end

let intros_reflexivity  = (Tacticals.New.tclTHEN intros reflexivity)

(* Symmetry tactics *)

(* This tactic first tries to apply a constant named sym_eq, where eq
   is the name of the equality predicate. If this constant is not
   defined and the conclusion is a=b, it solves the goal doing (Cut
   b=a;Intro H;Case H;Constructor 1) *)

let (forward_setoid_symmetry, setoid_symmetry) = Hook.make ()

(* This is probably not very useful any longer *)
let prove_symmetry hdcncl eq_kind =
  let symc =
    match eq_kind with
    | MonomorphicLeibnizEq (c1,c2) -> mkApp(hdcncl,[|c2;c1|])
    | PolymorphicLeibnizEq (typ,c1,c2) -> mkApp(hdcncl,[|typ;c2;c1|])
    | HeterogenousEq (t1,c1,t2,c2) -> mkApp(hdcncl,[|t2;c2;t1;c1|]) in
  Tacticals.New.tclTHENFIRST (cut symc)
    (Tacticals.New.tclTHENLIST
      [ intro;
        Tacticals.New.onLastHyp simplest_case;
	one_constructor 1 NoBindings ])

let match_with_equation c =
  try
    let res = match_with_equation c in
    Proofview.tclUNIT res
  with NoEquationFound ->
    Proofview.tclZERO NoEquationFound

let symmetry_red allowred =
  Proofview.Goal.enter begin fun gl ->
  (* PL: usual symmetry don't perform any reduction when searching
     for an equality, but we may need to do some when called back from
     inside setoid_reflexivity (see Optimize cases in setoid_replace.ml). *)
  let concl = maybe_betadeltaiota_concl allowred gl in
  match_with_equation concl >>= fun with_eqn ->
  match with_eqn with
  | Some eq_data,_,_ ->
      Tacticals.New.tclTHEN
        (convert_concl_no_check concl DEFAULTcast)
        (Tacticals.New.pf_constr_of_global eq_data.sym apply)
  | None,eq,eq_kind -> prove_symmetry eq eq_kind
  end

let symmetry =
  Proofview.tclORELSE
    (symmetry_red false)
    begin function (e, info) -> match e with
      | NoEquationFound -> Hook.get forward_setoid_symmetry
      | e -> Proofview.tclZERO ~info e
    end

let (forward_setoid_symmetry_in, setoid_symmetry_in) = Hook.make ()


let symmetry_in id =
  Proofview.Goal.enter begin fun gl ->
  let ctype = Tacmach.New.pf_type_of gl (mkVar id) in
  let sign,t = decompose_prod_assum ctype in
  Proofview.tclORELSE
    begin
      match_with_equation t >>= fun (_,hdcncl,eq) ->
        let symccl = match eq with
          | MonomorphicLeibnizEq (c1,c2) -> mkApp (hdcncl, [| c2; c1 |])
          | PolymorphicLeibnizEq (typ,c1,c2) -> mkApp (hdcncl, [| typ; c2; c1 |])
          | HeterogenousEq (t1,c1,t2,c2) -> mkApp (hdcncl, [| t2; c2; t1; c1 |]) in
        Tacticals.New.tclTHENS (cut (it_mkProd_or_LetIn symccl sign))
          [ intro_replacing id;
            Tacticals.New.tclTHENLIST [ intros; symmetry; apply (mkVar id); assumption ] ]
    end
    begin function (e, info) -> match e with
      | NoEquationFound -> Hook.get forward_setoid_symmetry_in id
      | e -> Proofview.tclZERO ~info e
    end
  end

let intros_symmetry =
  Tacticals.New.onClause
    (function
      | None -> Tacticals.New.tclTHEN intros symmetry
      | Some id -> symmetry_in id)

(* Transitivity tactics *)

(* This tactic first tries to apply a constant named eq_trans, where eq
   is the name of the equality predicate. If this constant is not
   defined and the conclusion is a=b, it solves the goal doing
   Cut x1=x2;
       [Cut x2=x3; [Intros e1 e2; Case e2;Assumption
                    | Idtac]
       | Idtac]
   --Eduardo (19/8/97)
*)

let (forward_setoid_transitivity, setoid_transitivity) = Hook.make ()


(* This is probably not very useful any longer *)
let prove_transitivity hdcncl eq_kind t =
  Proofview.Goal.enter begin fun gl ->
  let (eq1,eq2) = match eq_kind with
  | MonomorphicLeibnizEq (c1,c2) ->
      mkApp (hdcncl, [| c1; t|]), mkApp (hdcncl, [| t; c2 |])
  | PolymorphicLeibnizEq (typ,c1,c2) ->
      mkApp (hdcncl, [| typ; c1; t |]), mkApp (hdcncl, [| typ; t; c2 |])
  | HeterogenousEq (typ1,c1,typ2,c2) ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let type_of = Typing.type_of env sigma in
      let typt = type_of t in
        (mkApp(hdcncl, [| typ1; c1; typt ;t |]),
         mkApp(hdcncl, [| typt; t; typ2; c2 |]))
  in
  Tacticals.New.tclTHENFIRST (cut eq2)
    (Tacticals.New.tclTHENFIRST (cut eq1)
       (Tacticals.New.tclTHENLIST
	  [ Tacticals.New.tclDO 2 intro;
	    Tacticals.New.onLastHyp simplest_case;
	    assumption ]))
  end

let transitivity_red allowred t =
  Proofview.Goal.enter begin fun gl ->
  (* PL: usual transitivity don't perform any reduction when searching
     for an equality, but we may need to do some when called back from
     inside setoid_reflexivity (see Optimize cases in setoid_replace.ml). *)
  let concl = maybe_betadeltaiota_concl allowred gl in
  match_with_equation concl >>= fun with_eqn ->
  match with_eqn with
  | Some eq_data,_,_ ->
      Tacticals.New.tclTHEN
        (convert_concl_no_check concl DEFAULTcast)
        (match t with
	  | None -> Tacticals.New.pf_constr_of_global eq_data.trans eapply
	  | Some t -> Tacticals.New.pf_constr_of_global eq_data.trans (fun trans -> apply_list [trans;t]))
   | None,eq,eq_kind ->
      match t with
      | None -> Tacticals.New.tclZEROMSG (str"etransitivity not supported for this relation.")
      | Some t -> prove_transitivity eq eq_kind t
  end

let transitivity_gen t =
  Proofview.tclORELSE
    (transitivity_red false t)
    begin function (e, info) -> match e with
      | NoEquationFound -> Hook.get forward_setoid_transitivity t
      | e -> Proofview.tclZERO ~info e
    end

let etransitivity = transitivity_gen None
let transitivity t = transitivity_gen (Some t)

let intros_transitivity  n  = Tacticals.New.tclTHEN intros (transitivity_gen n)

(* tactical to save as name a subproof such that the generalisation of
   the current goal, abstracted with respect to the local signature,
   is solved by tac *)

(** d1 is the section variable in the global context, d2 in the goal context *)
let interpretable_as_section_decl evd d1 d2 = match d2,d1 with
  | (_,Some _,_), (_,None,_) -> false
  | (_,Some b1,t1), (_,Some b2,t2) -> 
    e_eq_constr_univs evd b1 b2 && e_eq_constr_univs evd t1 t2
  | (_,None,t1), (_,_,t2) -> e_eq_constr_univs evd t1 t2

let abstract_subproof id gk tac =
  let open Tacticals.New in
  let open Tacmach.New in
  let open Proofview.Notations in
  Proofview.Goal.nf_enter begin fun gl ->
  let current_sign = Global.named_context()
  and global_sign = Proofview.Goal.hyps gl in
  let evdref = ref (Proofview.Goal.sigma gl) in
  let sign,secsign =
    List.fold_right
      (fun (id,_,_ as d) (s1,s2) ->
	if mem_named_context id current_sign &&
          interpretable_as_section_decl evdref (Context.lookup_named id current_sign) d
        then (s1,push_named_context_val d s2)
	else (add_named_decl d s1,s2))
      global_sign (empty_named_context,empty_named_context_val) in
  let id = next_global_ident_away id (pf_ids_of_hyps gl) in
  let concl = it_mkNamedProd_or_LetIn (Proofview.Goal.concl gl) sign in
  let concl =
    try flush_and_check_evars !evdref concl
    with Uninstantiated_evar _ ->
      error "\"abstract\" cannot handle existentials." in

  let evd, ctx, concl =
    (* FIXME: should be done only if the tactic succeeds *)
    let evd, nf = nf_evars_and_universes !evdref in
    let ctx = Evd.universe_context_set evd in
      evd, ctx, nf concl
  in
  let solve_tac = tclCOMPLETE (tclTHEN (tclDO (List.length sign) intro) tac) in
  let ectx = Evd.evar_universe_context evd in
  let (const, safe, ectx) =
    try Pfedit.build_constant_by_tactic ~goal_kind:gk id ectx secsign concl solve_tac
    with Logic_monad.TacticFailure e as src ->
    (* if the tactic [tac] fails, it reports a [TacticFailure e],
       which is an error irrelevant to the proof system (in fact it
       means that [e] comes from [tac] failing to yield enough
       success). Hence it reraises [e]. *)
    let (_, info) = Errors.push src in
    iraise (e, info)
  in
  let cd = Entries.DefinitionEntry const in
  let decl = (cd, IsProof Lemma) in
  (** ppedrot: seems legit to have abstracted subproofs as local*)
  let cst = Declare.declare_constant ~internal:Declare.KernelSilent ~local:true id decl in
  (* let evd, lem = Evd.fresh_global (Global.env ()) evd (ConstRef cst) in *)
  let lem, ctx = Universes.unsafe_constr_of_global (ConstRef cst) in
  let evd = Evd.set_universe_context evd ectx in
  let open Declareops in
  let eff = Safe_typing.sideff_of_con (Global.safe_env ()) cst in
  let effs = cons_side_effects eff
    Entries.(snd (Future.force const.const_entry_body)) in
  let args = List.rev (instance_from_named_context sign) in
  let solve =
    Proofview.Unsafe.tclEVARS evd <*>
    Proofview.tclEFFECTS effs <*>
    new_exact_no_check (applist (lem, args))
  in
  if not safe then Proofview.mark_as_unsafe <*> solve else solve
  end

let anon_id = Id.of_string "anonymous"

let tclABSTRACT name_op tac =
  let open Proof_global in
  let default_gk = (Global, false, Proof Theorem) in
  let s, gk = match name_op with
    | Some s ->
      (try let _, gk, _ = current_proof_statement () in s, gk
       with NoCurrentProof -> s, default_gk)
    | None   ->
      let name, gk =
	try let name, gk, _ = current_proof_statement () in name, gk
	with NoCurrentProof -> anon_id, default_gk in
      add_suffix name "_subproof", gk
  in
  abstract_subproof s gk tac

let admit_as_an_axiom =
  Proofview.tclUNIT () >>= fun () -> (* delay for Coqlib.build_coq_proof_admitted *)
  simplest_case (Coqlib.build_coq_proof_admitted ()) <*>
  Proofview.mark_as_unsafe

let unify ?(state=full_transparent_state) x y =
  Proofview.Goal.nf_enter begin fun gl ->
  try
    let core_flags =
      { (default_unify_flags ()).core_unify_flags with
	modulo_delta = state;
	modulo_conv_on_closed_terms = Some state} in
    (* What to do on merge and subterm flags?? *)
    let flags = { (default_unify_flags ()) with
      core_unify_flags = core_flags;
      merge_unify_flags = core_flags;
      subterm_unify_flags = { core_flags with modulo_delta = empty_transparent_state } }
    in
    let evd = w_unify (Tacmach.New.pf_env gl) (Proofview.Goal.sigma gl) Reduction.CONV ~flags x y
    in Proofview.Unsafe.tclEVARS evd
  with e when Errors.noncritical e -> Tacticals.New.tclFAIL 0 (str"Not unifiable")
  end

module Simple = struct
  (** Simplified version of some of the above tactics *)

  let intro x = intro_move (Some x) MoveLast

  let generalize_gen cl =
    generalize_gen (List.map (on_fst Redexpr.out_with_occurrences) cl)
  let generalize cl =
    generalize_gen (List.map (fun c -> ((AllOccurrences,c),Names.Anonymous))
                        cl)

  let apply c =
    apply_with_bindings_gen false false [None,(Loc.ghost,(c,NoBindings))]
  let eapply c =
    apply_with_bindings_gen false true [None,(Loc.ghost,(c,NoBindings))]
  let elim c   = elim false None (c,NoBindings) None
  let case   c = general_case_analysis false None (c,NoBindings)

  let apply_in id c =
    apply_in false false None id [None,(Loc.ghost, (c, NoBindings))] None

end


(** Tacticals defined directly in term of Proofview *)
module New = struct
  open Proofview.Notations

  let exact_proof c = Proofview.V82.tactic (exact_proof c)

  open Genredexpr
  open Locus

  let reduce_after_refine =
    Proofview.V82.tactic (reduce
      (Lazy {rBeta=true;rIota=true;rZeta=false;rDelta=false;rConst=[]})
      {onhyps=None; concl_occs=AllOccurrences })

  let refine ?unsafe c =
    Proofview.Refine.refine ?unsafe c <*>
    reduce_after_refine
end
