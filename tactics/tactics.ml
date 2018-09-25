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
open Constr
open Termops
open Environ
open EConstr
open Vars
open Find_subterm
open Namegen
open Declarations
open Inductiveops
open Reductionops
open Globnames
open Evd
open Tacred
open Genredexpr
open Tacmach.New
open Logic
open Clenv
open Refiner
open Tacticals
open Hipattern
open Coqlib
open Decl_kinds
open Evarutil
open Indrec
open Pretype_errors
open Unification
open Locus
open Locusops
open Tactypes
open Proofview.Notations
open Context.Named.Declaration

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

let inj_with_occurrences e = (AllOccurrences,e)

let typ_of env sigma c =
  let open Retyping in
  try get_type_of ~lax:true env sigma c
  with RetypeError e ->
    user_err (print_retype_error e)

open Goptions

let clear_hyp_by_default = ref false

let use_clear_hyp_by_default () = !clear_hyp_by_default

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "default clearing of hypotheses after use";
      optkey   = ["Default";"Clearing";"Used";"Hypotheses"];
      optread  = (fun () -> !clear_hyp_by_default) ;
      optwrite = (fun b -> clear_hyp_by_default := b) }

(* Compatibility option useful in developments using apply intensively
   in ltac code *)

let universal_lemma_under_conjunctions = ref false

let accept_universal_lemma_under_conjunctions () =
  !universal_lemma_under_conjunctions

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "trivial unification in tactics applying under conjunctions";
      optkey   = ["Universal";"Lemma";"Under";"Conjunction"];
      optread  = (fun () -> !universal_lemma_under_conjunctions) ;
      optwrite = (fun b -> universal_lemma_under_conjunctions := b) }

(* The following boolean governs what "intros []" do on examples such
   as "forall x:nat*nat, x=x"; if true, it behaves as "intros [? ?]";
   if false, it behaves as "intro H; case H; clear H" for fresh H.
   Kept as false for compatibility.
 *)

let bracketing_last_or_and_intro_pattern = ref true

let use_bracketing_last_or_and_intro_pattern () =
  !bracketing_last_or_and_intro_pattern

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "bracketing last or-and introduction pattern";
      optkey   = ["Bracketing";"Last";"Introduction";"Pattern"];
      optread  = (fun () -> !bracketing_last_or_and_intro_pattern);
      optwrite = (fun b -> bracketing_last_or_and_intro_pattern := b) }

(*********************************************)
(*                 Tactics                   *)
(*********************************************)

(******************************************)
(*           Primitive tactics            *)
(******************************************)

(** This tactic creates a partial proof realizing the introduction rule, but
    does not check anything. *)
let unsafe_intro env store decl b =
  Refine.refine ~typecheck:false begin fun sigma ->
    let ctx = named_context_val env in
    let nctx = push_named_context_val decl ctx in
    let inst = List.map (NamedDecl.get_id %> mkVar) (named_context env) in
    let ninst = mkRel 1 :: inst in
    let nb = subst1 (mkVar (NamedDecl.get_id decl)) b in
    let (sigma, ev) = new_evar_instance nctx sigma nb ~principal:true ~store ninst in
    (sigma, mkNamedLambda_or_LetIn decl ev)
  end

let introduction id =
  Proofview.Goal.enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let sigma = Tacmach.New.project gl in
    let hyps = named_context_val (Proofview.Goal.env gl) in
    let store = Proofview.Goal.extra gl in
    let env = Proofview.Goal.env gl in
    let () = if mem_named_context_val id hyps then
      user_err ~hdr:"Tactics.introduction"
        (str "Variable " ++ Id.print id ++ str " is already declared.")
    in
    let open Context.Named.Declaration in
    match EConstr.kind sigma concl with
    | Prod (_, t, b) -> unsafe_intro env store (LocalAssum (id, t)) b
    | LetIn (_, c, t, b) -> unsafe_intro env store (LocalDef (id, c, t)) b
    | _ -> raise (RefinerError (env, sigma, IntroNeedsProduct))
  end

let refine          = Tacmach.refine
let error msg = CErrors.user_err Pp.(str msg)

let convert_concl ?(check=true) ty k =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let store = Proofview.Goal.extra gl in
    let conclty = Proofview.Goal.concl gl in
    Refine.refine ~typecheck:false begin fun sigma ->
      let sigma =
        if check then begin
          ignore (Typing.unsafe_type_of env sigma ty);
          match Reductionops.infer_conv env sigma ty conclty with
          | None -> error "Not convertible."
          | Some sigma -> sigma
        end else sigma in
      let (sigma, x) = Evarutil.new_evar env sigma ~principal:true ~store ty in
      let ans = if k == DEFAULTcast then x else mkCast(x,k,conclty) in
      (sigma, ans)
    end
  end

let convert_hyp ?(check=true) d =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let ty = Proofview.Goal.concl gl in
    let store = Proofview.Goal.extra gl in
    let sign = convert_hyp check (named_context_val env) sigma d in
    let env = reset_with_named_context sign env in
    Refine.refine ~typecheck:false begin fun sigma ->
      Evarutil.new_evar env sigma ~principal:true ~store ty
    end
  end

let convert_concl_no_check = convert_concl ~check:false
let convert_hyp_no_check = convert_hyp ~check:false

let convert_gen pb x y =
  Proofview.Goal.enter begin fun gl ->
    match Tacmach.New.pf_apply (Reductionops.infer_conv ~pb) gl x y with
    | Some sigma -> Proofview.Unsafe.tclEVARS sigma
    | None -> Tacticals.New.tclFAIL 0 (str "Not convertible")
    | exception _ ->
      (** FIXME: Sometimes an anomaly is raised from conversion *)
      Tacticals.New.tclFAIL 0 (str "Not convertible")
end

let convert x y = convert_gen Reduction.CONV x y
let convert_leq x y = convert_gen Reduction.CUMUL x y

let clear_in_global_msg = function
  | None -> mt ()
  | Some ref -> str " implicitly in " ++ Printer.pr_global ref

let clear_dependency_msg env sigma id err inglobal =
  let pp = clear_in_global_msg inglobal in
  match err with
  | Evarutil.OccurHypInSimpleClause None ->
      Id.print id ++ str " is used" ++ pp ++ str " in conclusion."
  | Evarutil.OccurHypInSimpleClause (Some id') ->
      Id.print id ++ strbrk " is used" ++ pp ++ str " in hypothesis " ++ Id.print id' ++ str"."
  | Evarutil.EvarTypingBreak ev ->
      str "Cannot remove " ++ Id.print id ++
      strbrk " without breaking the typing of " ++
      Printer.pr_existential env sigma ev ++ str"."
  | Evarutil.NoCandidatesLeft ev ->
      str "Cannot remove " ++ Id.print id ++ str " as it would leave the existential " ++
      Printer.pr_existential_key sigma ev ++ str" without candidates."

let error_clear_dependency env sigma id err inglobal =
  user_err (clear_dependency_msg env sigma id err inglobal)

let replacing_dependency_msg env sigma id err inglobal =
  let pp = clear_in_global_msg inglobal in
  match err with
  | Evarutil.OccurHypInSimpleClause None ->
      str "Cannot change " ++ Id.print id ++ str ", it is used" ++ pp ++ str " in conclusion."
  | Evarutil.OccurHypInSimpleClause (Some id') ->
      str "Cannot change " ++ Id.print id ++
      strbrk ", it is used" ++ pp ++ str " in hypothesis " ++ Id.print id' ++ str"."
  | Evarutil.EvarTypingBreak ev ->
      str "Cannot change " ++ Id.print id ++
      strbrk " without breaking the typing of " ++
      Printer.pr_existential env sigma ev ++ str"."
  | Evarutil.NoCandidatesLeft ev ->
      str "Cannot change " ++ Id.print id ++ str " as it would leave the existential " ++
      Printer.pr_existential_key sigma ev ++ str" without candidates."

let error_replacing_dependency env sigma id err inglobal =
  user_err (replacing_dependency_msg env sigma id err inglobal)

(* This tactic enables the user to remove hypotheses from the signature.
 * Some care is taken to prevent him from removing variables that are
 * subsequently used in other hypotheses or in the conclusion of the
 * goal. *)

let clear_gen fail = function
| [] -> Proofview.tclUNIT ()
| ids ->
  Proofview.Goal.enter begin fun gl ->
    let ids = List.fold_right Id.Set.add ids Id.Set.empty in
    (** clear_hyps_in_evi does not require nf terms *)
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let concl = Proofview.Goal.concl gl in
    let (sigma, hyps, concl) =
      try clear_hyps_in_evi env sigma (named_context_val env) concl ids
      with Evarutil.ClearDependencyError (id,err,inglobal) -> fail env sigma id err inglobal
    in
    let env = reset_with_named_context hyps env in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (Refine.refine ~typecheck:false begin fun sigma ->
      Evarutil.new_evar env sigma ~principal:true concl
    end)
  end

let clear ids = clear_gen error_clear_dependency ids
let clear_for_replacing ids = clear_gen error_replacing_dependency ids

let apply_clear_request clear_flag dft c =
  Proofview.tclEVARMAP >>= fun sigma ->
  let check_isvar c =
    if not (isVar sigma c) then
      error "keep/clear modifiers apply only to hypothesis names." in
  let doclear = match clear_flag with
    | None -> dft && isVar sigma c
    | Some true -> check_isvar c; true
    | Some false -> false in
  if doclear then clear [destVar sigma c]
  else Tacticals.New.tclIDTAC

(* Moving hypotheses *)
let move_hyp id dest =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let ty = Proofview.Goal.concl gl in
    let store = Proofview.Goal.extra gl in
    let sign = named_context_val env in
    let sign' = move_hyp_in_named_context env sigma id dest sign in
    let env = reset_with_named_context sign' env in
    Refine.refine ~typecheck:false begin fun sigma ->
      Evarutil.new_evar env sigma ~principal:true ~store ty
    end
  end

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
      let hyps = Proofview.Goal.hyps gl in
      let concl = Proofview.Goal.concl gl in
      let store = Proofview.Goal.extra gl in
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      (** Check that we do not mess variables *)
      let fold accu decl = Id.Set.add (NamedDecl.get_id decl) accu in
      let vars = List.fold_left fold Id.Set.empty hyps in
      let () =
        if not (Id.Set.subset src vars) then
          let hyp = Id.Set.choose (Id.Set.diff src vars) in
          raise (RefinerError (env, sigma, NoSuchHyp hyp))
      in
      let mods = Id.Set.diff vars src in
      let () =
        try
          let elt = Id.Set.choose (Id.Set.inter dst mods) in
          CErrors.user_err  (Id.print elt ++ str " is already used")
        with Not_found -> ()
      in
      (** All is well *)
      let make_subst (src, dst) = (src, mkVar dst) in
      let subst = List.map make_subst repl in
      let subst c = Vars.replace_vars subst c in
      let map decl =
        decl |> NamedDecl.map_id (fun id -> try List.assoc_f Id.equal id repl with Not_found -> id)
             |> NamedDecl.map_constr subst
      in
      let nhyps = List.map map hyps in
      let nconcl = subst concl in
      let nctx = val_of_named_context nhyps in
      let instance = List.map (NamedDecl.get_id %> mkVar) hyps in
      Refine.refine ~typecheck:false begin fun sigma ->
        Evarutil.new_evar_instance nctx sigma nconcl ~principal:true ~store instance
      end
    end

(**************************************************************)
(*          Fresh names                                       *)
(**************************************************************)

let fresh_id_in_env avoid id env =
  let avoid' = ids_of_named_context_val (named_context_val env) in
  let avoid = if Id.Set.is_empty avoid then avoid' else Id.Set.union avoid' avoid in
  next_ident_away_in_goal id avoid

let fresh_id avoid id gl =
  fresh_id_in_env avoid id (pf_env gl)

let new_fresh_id avoid id gl =
  fresh_id_in_env avoid id (Proofview.Goal.env gl)

let id_of_name_with_default id = function
  | Anonymous -> id
  | Name id   -> id

let default_id_of_sort s =
  if Sorts.is_small s then default_small_ident else default_type_ident

let default_id env sigma decl =
  let open Context.Rel.Declaration in
  match decl with
  | LocalAssum (name,t) ->
      let dft = default_id_of_sort (Retyping.get_sort_of env sigma t) in
      id_of_name_with_default dft name
  | LocalDef (name,b,_) -> id_of_name_using_hdchar env sigma b name

(* Non primitive introduction tactics are treated by intro_then_gen
   There is possibly renaming, with possibly names to avoid and
   possibly a move to do after the introduction *)

type name_flag =
  | NamingAvoid of Id.Set.t
  | NamingBasedOn of Id.t * Id.Set.t
  | NamingMustBe of lident

let naming_of_name = function
  | Anonymous -> NamingAvoid Id.Set.empty
  | Name id -> NamingMustBe (CAst.make id)

let find_name mayrepl decl naming gl = match naming with
  | NamingAvoid idl ->
      (* this case must be compatible with [find_intro_names] below. *)
      let env = Proofview.Goal.env gl in
      let sigma = Tacmach.New.project gl in
      new_fresh_id idl (default_id env sigma decl) gl
  | NamingBasedOn (id,idl) ->  new_fresh_id idl id gl
  | NamingMustBe {CAst.loc;v=id} ->
     (* When name is given, we allow to hide a global name *)
     let ids_of_hyps = Tacmach.New.pf_ids_set_of_hyps gl in
     if not mayrepl && Id.Set.mem id ids_of_hyps then
       user_err ?loc  (Id.print id ++ str" is already used.");
     id

(**************************************************************)
(*   Computing position of hypotheses for replacing           *)
(**************************************************************)

let get_next_hyp_position env sigma id =
  let rec aux = function
  | [] -> error_no_such_hypothesis env sigma id
  | decl :: right ->
    if Id.equal (NamedDecl.get_id decl) id then
      match right with decl::_ -> MoveBefore (NamedDecl.get_id decl) | [] -> MoveFirst
    else
      aux right
  in
  aux

let get_previous_hyp_position env sigma id =
  let rec aux dest = function
  | [] -> error_no_such_hypothesis env sigma id
  | decl :: right ->
      let hyp = NamedDecl.get_id decl in
      if Id.equal hyp id then dest else aux (MoveAfter hyp) right
  in
  aux MoveLast

(**************************************************************)
(*            Cut rule                                        *)
(**************************************************************)

let clear_hyps2 env sigma ids sign t cl =
  try
    let sigma = Evd.clear_metas sigma in
    Evarutil.clear_hyps2_in_evi env sigma sign t cl ids
  with Evarutil.ClearDependencyError (id,err,inglobal) ->
    error_replacing_dependency env sigma id err inglobal

let internal_cut_gen ?(check=true) dir replace id t =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let concl = Proofview.Goal.concl gl in
    let store = Proofview.Goal.extra gl in
    let sign = named_context_val env in
    let sign',t,concl,sigma =
      if replace then
        let nexthyp = get_next_hyp_position env sigma id (named_context_of_val sign) in
        let sigma,sign',t,concl = clear_hyps2 env sigma (Id.Set.singleton id) sign t concl in
        let sign' = insert_decl_in_named_context sigma (LocalAssum (id,t)) nexthyp sign' in
        sign',t,concl,sigma
      else
        (if check && mem_named_context_val id sign then
	   user_err (str "Variable " ++ Id.print id ++ str " is already declared.");
         push_named_context_val (LocalAssum (id,t)) sign,t,concl,sigma) in
    let nf_t = nf_betaiota env sigma t in
    Proofview.tclTHEN
      (Proofview.Unsafe.tclEVARS sigma)
      (Refine.refine ~typecheck:false begin fun sigma ->
        let (sigma,ev,ev') =
          if dir then
            let (sigma, ev) = Evarutil.new_evar_from_context sign sigma nf_t in
            let (sigma, ev') = Evarutil.new_evar_from_context sign' sigma ~principal:true ~store concl in
            (sigma,ev,ev')
          else
            let (sigma, ev') = Evarutil.new_evar_from_context sign' sigma ~principal:true ~store concl in
            let (sigma, ev) = Evarutil.new_evar_from_context sign sigma nf_t in
            (sigma,ev,ev') in
        let term = mkLetIn (Name id, ev, t, EConstr.Vars.subst_var id ev') in
        (sigma, term)
      end)
  end

let internal_cut ?(check=true) = internal_cut_gen ~check true
let internal_cut_rev ?(check=true) = internal_cut_gen ~check false

let assert_before_then_gen b naming t tac =
  let open Context.Rel.Declaration in
  Proofview.Goal.enter begin fun gl ->
    let id = find_name b (LocalAssum (Anonymous,t)) naming gl in
    Tacticals.New.tclTHENLAST
      (internal_cut b id t)
      (tac id)
  end

let assert_before_gen b naming t =
  assert_before_then_gen b naming t (fun _ -> Proofview.tclUNIT ())

let assert_before na = assert_before_gen false (naming_of_name na)
let assert_before_replacing id = assert_before_gen true (NamingMustBe (CAst.make id))

let assert_after_then_gen b naming t tac =
  let open Context.Rel.Declaration in
  Proofview.Goal.enter begin fun gl ->
    let id = find_name b (LocalAssum (Anonymous,t)) naming gl in
    Tacticals.New.tclTHENFIRST
      (internal_cut_rev b id t)
      (tac id)
  end

let assert_after_gen b naming t =
  assert_after_then_gen b naming t (fun _ -> (Proofview.tclUNIT ()))

let assert_after na = assert_after_gen false (naming_of_name na)
let assert_after_replacing id = assert_after_gen true (NamingMustBe (CAst.make id))

(**************************************************************)
(*          Fixpoints and CoFixpoints                         *)
(**************************************************************)

let rec mk_holes env sigma = function
| [] -> (sigma, [])
| arg :: rem ->
  let (sigma, arg) = Evarutil.new_evar env sigma arg in
  let (sigma, rem) = mk_holes env sigma rem in
  (sigma, arg :: rem)

let rec check_mutind env sigma k cl = match EConstr.kind sigma (strip_outer_cast sigma cl) with
| Prod (na, c1, b) ->
  if Int.equal k 1 then
    try
      let ((sp, _), u), _ = find_inductive env sigma c1 in
      (sp, u)
    with Not_found -> error "Cannot do a fixpoint on a non inductive type."
  else
    let open Context.Rel.Declaration in
    check_mutind (push_rel (LocalAssum (na, c1)) env) sigma (pred k) b
| LetIn (na, c1, t, b) ->
    let open Context.Rel.Declaration in
    check_mutind (push_rel (LocalDef (na, c1, t)) env) sigma k b
| _ -> error "Not enough products."

(* Refine as a fixpoint *)
let mutual_fix f n rest j = Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.New.project gl in
  let concl = Proofview.Goal.concl gl in
  let (sp, u) = check_mutind env sigma n concl in
  let firsts, lasts = List.chop j rest in
  let all = firsts @ (f, n, concl) :: lasts in
  let rec mk_sign sign = function
  | [] -> sign
  | (f, n, ar) :: oth ->
    let open Context.Named.Declaration in
    let (sp', u')  = check_mutind env sigma n ar in
    if not (MutInd.equal sp sp') then
      error "Fixpoints should be on the same mutual inductive declaration.";
    if mem_named_context_val f sign then
      user_err ~hdr:"Logic.prim_refiner"
        (str "Name " ++ Id.print f ++ str " already used in the environment");
    mk_sign (push_named_context_val (LocalAssum (f, ar)) sign) oth
  in
  let nenv = reset_with_named_context (mk_sign (named_context_val env) all) env in
  Refine.refine ~typecheck:false begin fun sigma ->
    let (sigma, evs) = mk_holes nenv sigma (List.map pi3 all) in
    let ids = List.map pi1 all in
    let evs = List.map (Vars.subst_vars (List.rev ids)) evs in
    let indxs = Array.of_list (List.map (fun n -> n-1) (List.map pi2 all)) in
    let funnames = Array.of_list (List.map (fun i -> Name i) ids) in
    let typarray = Array.of_list (List.map pi3 all) in
    let bodies = Array.of_list evs in
    let oterm = mkFix ((indxs,0),(funnames,typarray,bodies)) in
    (sigma, oterm)
  end
end

let fix id n = mutual_fix id n [] 0

let rec check_is_mutcoind env sigma cl =
  let b = whd_all env sigma cl in
  match EConstr.kind sigma b with
  | Prod (na, c1, b) ->
    let open Context.Rel.Declaration in
    check_is_mutcoind (push_rel (LocalAssum (na,c1)) env) sigma b
  | _ ->
    try
      let _ = find_coinductive env sigma b in ()
    with Not_found ->
      error "All methods must construct elements in coinductive types."

(* Refine as a cofixpoint *)
let mutual_cofix f others j = Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.New.project gl in
  let concl = Proofview.Goal.concl gl in
  let firsts,lasts = List.chop j others in
  let all = firsts @ (f, concl) :: lasts in
  List.iter (fun (_, c) -> check_is_mutcoind env sigma c) all;
  let rec mk_sign sign = function
  | [] -> sign
  | (f, ar) :: oth ->
    let open Context.Named.Declaration in
    if mem_named_context_val f sign then
      error "Name already used in the environment.";
    mk_sign (push_named_context_val (LocalAssum (f, ar)) sign) oth
  in
  let nenv = reset_with_named_context (mk_sign (named_context_val env) all) env in
  Refine.refine ~typecheck:false begin fun sigma ->
    let (ids, types) = List.split all in
    let (sigma, evs) = mk_holes nenv sigma types in
    let evs = List.map (Vars.subst_vars (List.rev ids)) evs in
    let funnames = Array.of_list (List.map (fun i -> Name i) ids) in
    let typarray = Array.of_list types in
    let bodies = Array.of_list evs in
    let oterm = mkCoFix (0, (funnames, typarray, bodies)) in
    (sigma, oterm)
  end
end

let cofix id = mutual_cofix id [] 0

(**************************************************************)
(*          Reduction and conversion tactics                  *)
(**************************************************************)

type tactic_reduction = Reductionops.reduction_function
type e_tactic_reduction = Reductionops.e_reduction_function

let pf_reduce_decl redfun where decl gl =
  let open Context.Named.Declaration in
  let redfun' c = Tacmach.New.pf_apply redfun gl c in
  match decl with
  | LocalAssum (id,ty) ->
      if where == InHypValueOnly then
	user_err  (Id.print id ++ str " has no value.");
      LocalAssum (id,redfun' ty)
  | LocalDef (id,b,ty) ->
      let b' = if where != InHypTypeOnly then redfun' b else b in
      let ty' =	if where != InHypValueOnly then redfun' ty else ty in
      LocalDef (id,b',ty')

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

let reduct_in_concl (redfun,sty) =
  Proofview.Goal.enter begin fun gl ->
    convert_concl_no_check (Tacmach.New.pf_apply redfun gl (Tacmach.New.pf_concl gl)) sty
  end

let reduct_in_hyp ?(check=false) redfun (id,where) =
  Proofview.Goal.enter begin fun gl ->
  convert_hyp ~check (pf_reduce_decl redfun where (Tacmach.New.pf_get_hyp id gl) gl)
  end

let revert_cast (redfun,kind as r) =
  if kind == DEFAULTcast then (redfun,REVERTcast) else r

let reduct_option ?(check=false) redfun = function
  | Some id -> reduct_in_hyp ~check (fst redfun) id
  | None    -> reduct_in_concl (revert_cast redfun)

(** Tactic reduction modulo evars (for universes essentially) *)

let pf_e_reduce_decl redfun where decl gl =
  let open Context.Named.Declaration in
  let sigma = Proofview.Goal.sigma gl in
  let redfun sigma c = redfun (Tacmach.New.pf_env gl) sigma c in
  match decl with
  | LocalAssum (id,ty) ->
      if where == InHypValueOnly then
	user_err  (Id.print id ++ str " has no value.");
    let (sigma, ty') = redfun sigma ty in
    (sigma, LocalAssum (id, ty'))
  | LocalDef (id,b,ty) ->
      let (sigma, b') = if where != InHypTypeOnly then redfun sigma b else (sigma, b) in
      let (sigma, ty') = if where != InHypValueOnly then redfun sigma ty else (sigma, ty) in
      (sigma, LocalDef (id, b', ty'))

let e_reduct_in_concl ~check (redfun, sty) =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let (sigma, c') = redfun (Tacmach.New.pf_env gl) sigma (Tacmach.New.pf_concl gl) in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (convert_concl ~check c' sty)
  end

let e_reduct_in_hyp ?(check=false) redfun (id, where) =
  Proofview.Goal.enter begin fun gl ->
    let (sigma, decl') = pf_e_reduce_decl redfun where (Tacmach.New.pf_get_hyp id gl) gl in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (convert_hyp ~check decl')
  end

let e_reduct_option ?(check=false) redfun = function
  | Some id -> e_reduct_in_hyp ~check (fst redfun) id
  | None    -> e_reduct_in_concl ~check (revert_cast redfun)

(** Versions with evars to maintain the unification of universes resulting
    from conversions. *)

let e_change_in_concl (redfun,sty) =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let (sigma, c) = redfun (Proofview.Goal.env gl) sigma (Proofview.Goal.concl gl) in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (convert_concl_no_check c sty)
  end

let e_pf_change_decl (redfun : bool -> e_reduction_function) where decl env sigma =
  let open Context.Named.Declaration in
  match decl with
  | LocalAssum (id,ty) ->
      if where == InHypValueOnly then
	user_err  (Id.print id ++ str " has no value.");
    let (sigma, ty') = redfun false env sigma ty in
    (sigma, LocalAssum (id, ty'))
  | LocalDef (id,b,ty) ->
      let (sigma, b') =
	if where != InHypTypeOnly then redfun true env sigma b else (sigma, b)
      in
      let (sigma, ty') =
	if where != InHypValueOnly then redfun false env sigma ty else (sigma, ty)
      in
      (sigma, LocalDef (id,b',ty'))

let e_change_in_hyp redfun (id,where) =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let hyp = Tacmach.New.pf_get_hyp id gl in
    let (sigma, c) = e_pf_change_decl redfun where hyp (Proofview.Goal.env gl) sigma in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (convert_hyp c)
  end

type change_arg = Ltac_pretype.patvar_map -> env -> evar_map -> evar_map * EConstr.constr

let make_change_arg c pats env sigma = (sigma, replace_vars (Id.Map.bindings pats) c)

let check_types env sigma mayneedglobalcheck deep newc origc =
  let t1 = Retyping.get_type_of env sigma newc in
  if deep then begin
    let t2 = Retyping.get_type_of env sigma origc in
    let sigma, t2 = Evarsolve.refresh_universes
		      ~onlyalg:true (Some false) env sigma t2 in
    match infer_conv ~pb:Reduction.CUMUL env sigma t1 t2 with
    | None ->
      if
        isSort sigma (whd_all env sigma t1) &&
        isSort sigma (whd_all env sigma t2)
      then (mayneedglobalcheck := true; sigma)
      else
        user_err ~hdr:"convert-check-hyp" (str "Types are incompatible.")
    | Some sigma -> sigma
  end
  else
    if not (isSort sigma (whd_all env sigma t1)) then
      user_err ~hdr:"convert-check-hyp" (str "Not a type.")
    else sigma

(* Now we introduce different instances of the previous tacticals *)
let change_and_check cv_pb mayneedglobalcheck deep t env sigma c =
  let (sigma, t') = t env sigma in
  let sigma = check_types env sigma mayneedglobalcheck deep t' c in
  match infer_conv ~pb:cv_pb env sigma t' c with
  | None -> user_err ~hdr:"convert-check-hyp" (str "Not convertible.");
  | Some sigma -> (sigma, t')

(* Use cumulativity only if changing the conclusion not a subterm *)
let change_on_subterm cv_pb deep t where env sigma c =
  let mayneedglobalcheck = ref false in
  let (sigma, c) = match where with
  | None -> change_and_check cv_pb mayneedglobalcheck deep (t Id.Map.empty) env sigma c
  | Some occl ->
      e_contextually false occl
        (fun subst ->
          change_and_check Reduction.CONV mayneedglobalcheck true (t subst))
        env sigma c in
  if !mayneedglobalcheck then
    begin
      try ignore (Typing.unsafe_type_of env sigma c)
      with e when catchable_exception e ->
        error "Replacement would lead to an ill-typed term."
    end;
  (sigma, c)

let change_in_concl occl t =
  e_change_in_concl ((change_on_subterm Reduction.CUMUL false t occl),DEFAULTcast)

let change_in_hyp occl t id  =
  e_change_in_hyp (fun x -> change_on_subterm Reduction.CONV x t occl) id

let change_option occl t = function
  | Some id -> change_in_hyp occl t id
  | None -> change_in_concl occl t

let change chg c cls =
  Proofview.Goal.enter begin fun gl ->
    let cls = concrete_clause_of (fun () -> Tacmach.New.pf_ids_of_hyps gl) cls in
    Tacticals.New.tclMAP (function
    | OnHyp (id,occs,where) ->
       change_option (bind_change_occurrences occs chg) c (Some (id,where))
    | OnConcl occs ->
       change_option (bind_change_occurrences occs chg) c None)
    cls
  end

let change_concl t = 
  change_in_concl None (make_change_arg t)

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

let reduce redexp cl =
  let trace env sigma =
    let open Printer in
    let pr = (pr_econstr_env, pr_leconstr_env, pr_evaluable_reference, pr_constr_pattern_env) in
    Pp.(hov 2 (Pputils.pr_red_expr_env env sigma pr str redexp))
  in
  let trace () =
    let sigma, env = Pfedit.get_current_context () in
    trace env sigma
  in
  Proofview.Trace.name_tactic trace begin
  Proofview.Goal.enter begin fun gl ->
  let cl' = concrete_clause_of (fun () -> Tacmach.New.pf_ids_of_hyps gl) cl in
  let redexps = reduction_clause redexp cl' in
  let check = match redexp with Fold _ | Pattern _ -> true | _ -> false in
  Tacticals.New.tclMAP (fun (where,redexp) ->
    e_reduct_option ~check
      (Redexpr.reduction_of_red_expr (Tacmach.New.pf_env gl) redexp) where) redexps
  end
  end

(* Unfolding occurrences of a constant *)

let unfold_constr = function
  | ConstRef sp -> unfold_in_concl [AllOccurrences,EvalConstRef sp]
  | VarRef id -> unfold_in_concl [AllOccurrences,EvalVarRef id]
  | _ -> user_err ~hdr:"unfold_constr" (str "Cannot unfold a non-constant.")

(*******************************************)
(*         Introduction tactics            *)
(*******************************************)

(* Returns the names that would be created by intros, without doing
   intros.  This function is supposed to be compatible with an
   iteration of [find_name] above. As [default_id] checks the sort of
   the type to build hyp names, we maintain an environment to be able
   to type dependent hyps. *)
let find_intro_names ctxt gl =
  let _, res, _ = List.fold_right
    (fun decl acc ->
      let env,idl,avoid = acc in
      let name = fresh_id avoid (default_id env gl.sigma decl) gl in
      let newenv = push_rel decl env in
      (newenv, name :: idl, Id.Set.add name avoid))
    ctxt (pf_env gl, [], Id.Set.empty) in
  List.rev res

let build_intro_tac id dest tac = match dest with
  | MoveLast -> Tacticals.New.tclTHEN (introduction id) (tac id)
  | dest -> Tacticals.New.tclTHENLIST 
    [introduction id; move_hyp id dest; tac id]

let rec intro_then_gen name_flag move_flag force_flag dep_flag tac =
  let open Context.Rel.Declaration in
  Proofview.Goal.enter begin fun gl ->
    let sigma = Tacmach.New.project gl in
    let env = Tacmach.New.pf_env gl in
    let concl = Proofview.Goal.concl gl in
    match EConstr.kind sigma concl with
    | Prod (name,t,u) when not dep_flag || not (noccurn sigma 1 u) ->
        let name = find_name false (LocalAssum (name,t)) name_flag gl in
	build_intro_tac name move_flag tac
    | LetIn (name,b,t,u) when not dep_flag || not (noccurn sigma 1 u) ->
        let name = find_name false (LocalDef (name,b,t)) name_flag gl in
	build_intro_tac name move_flag tac
    | Evar ev when force_flag ->
        let sigma, t = Evardefine.define_evar_as_product sigma ev in
        Tacticals.New.tclTHEN
          (Proofview.Unsafe.tclEVARS sigma)
          (intro_then_gen name_flag move_flag force_flag dep_flag tac)
    | _ ->
        begin if not force_flag then Proofview.tclZERO (RefinerError (env, sigma, IntroNeedsProduct))
            (* Note: red_in_concl includes betaiotazeta and this was like *)
            (* this since at least V6.3 (a pity *)
            (* that intro do betaiotazeta only when reduction is needed; and *)
            (* probably also a pity that intro does zeta *)
          else Proofview.tclUNIT ()
        end <*>
	  Proofview.tclORELSE
	  (Tacticals.New.tclTHEN hnf_in_concl
	     (intro_then_gen name_flag move_flag false dep_flag tac))
          begin function (e, info) -> match e with
            | RefinerError (env, sigma, IntroNeedsProduct) ->
                Tacticals.New.tclZEROMSG (str "No product even after head-reduction.")
            | e -> Proofview.tclZERO ~info e
          end
  end

let intro_gen n m f d = intro_then_gen n m f d (fun _ -> Proofview.tclUNIT ())
let intro_mustbe_force id = intro_gen (NamingMustBe (CAst.make id)) MoveLast true false
let intro_using id = intro_gen (NamingBasedOn (id, Id.Set.empty)) MoveLast false false

let intro_then = intro_then_gen (NamingAvoid Id.Set.empty) MoveLast false false
let intro = intro_gen (NamingAvoid Id.Set.empty) MoveLast false false
let introf = intro_gen (NamingAvoid Id.Set.empty) MoveLast true false
let intro_avoiding l = intro_gen (NamingAvoid l) MoveLast false false

let intro_move_avoid idopt avoid hto = match idopt with
  | None -> intro_gen (NamingAvoid avoid) hto true false
  | Some id -> intro_gen (NamingMustBe (CAst.make id)) hto true false

let intro_move idopt hto = intro_move_avoid idopt Id.Set.empty hto

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
      | RefinerError (env, sigma, IntroNeedsProduct) ->
          tac ids
      | e -> Proofview.tclZERO ~info e
      end
    else
      tac ids
  in
  aux n []

let intro_replacing id =
  Proofview.Goal.enter begin fun gl ->
  let env, sigma = Proofview.Goal.(env gl, sigma gl) in
  let hyps = Proofview.Goal.hyps gl in
  let next_hyp = get_next_hyp_position env sigma id hyps in
  Tacticals.New.tclTHENLIST [
    clear_for_replacing [id];
    introduction id;
    move_hyp id next_hyp;
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
    let env, sigma = Proofview.Goal.(env gl, sigma gl) in
    let hyps = Proofview.Goal.hyps gl in
    let posl = List.map (fun id -> (id, get_next_hyp_position env sigma id hyps)) ids in
    Tacticals.New.tclTHEN
      (Tacticals.New.tclMAP (fun id -> 
	Tacticals.New.tclTRY (clear_for_replacing [id]))
	 (if suboptimal then ids else List.rev ids))
      (Tacticals.New.tclMAP (fun (id,pos) ->
        Tacticals.New.tclORELSE (intro_move (Some id) pos) (intro_using id))
         posl)
  end

(* This version assumes that replacement is actually possible *)
let intros_replacing ids =
  Proofview.Goal.enter begin fun gl ->
    let hyps = Proofview.Goal.hyps gl in
    let env, sigma = Proofview.Goal.(env gl, sigma gl) in
    let posl = List.map (fun id -> (id, get_next_hyp_position env sigma id hyps)) ids in
    Tacticals.New.tclTHEN
      (clear_for_replacing ids)
      (Tacticals.New.tclMAP (fun (id,pos) -> intro_move (Some id) pos) posl)
  end

(* User-level introduction tactics *)

let lookup_hypothesis_as_renamed env sigma ccl = function
  | AnonHyp n -> Detyping.lookup_index_as_renamed env sigma ccl n
  | NamedHyp id -> Detyping.lookup_name_as_displayed env sigma ccl id

let lookup_hypothesis_as_renamed_gen red h gl =
  let env = Proofview.Goal.env gl in
  let rec aux ccl =
    match lookup_hypothesis_as_renamed env (Tacmach.New.project gl) ccl h with
      | None when red ->
        let (redfun, _) = Redexpr.reduction_of_red_expr env (Red true) in
        let (_, c) = redfun env (Proofview.Goal.sigma gl) ccl in
        aux c
      | x -> x
  in
  try aux (Proofview.Goal.concl gl)
  with Redelimination -> None

let is_quantified_hypothesis id gl =
  match lookup_hypothesis_as_renamed_gen false (NamedHyp id) gl with
    | Some _ -> true
    | None -> false

let msg_quantified_hypothesis = function
  | NamedHyp id ->
      str "quantified hypothesis named " ++ Id.print id
  | AnonHyp n ->
      pr_nth n ++
      str " non dependent hypothesis"

let warn_deprecated_intros_until_0 =
  CWarnings.create ~name:"deprecated-intros-until-0" ~category:"tactics"
    (fun () ->
       strbrk"\"intros until 0\" is deprecated, use \"intros *\"; instead of \"induction 0\" and \"destruct 0\" use explicitly a name.\"")

let depth_of_quantified_hypothesis red h gl =
  if h = AnonHyp 0 then warn_deprecated_intros_until_0 ();
  match lookup_hypothesis_as_renamed_gen red h gl with
    | Some depth -> depth
    | None ->
        user_err ~hdr:"lookup_quantified_hypothesis"
          (str "No " ++ msg_quantified_hypothesis h ++
	  strbrk " in current goal" ++
	  (if red then strbrk " even after head-reduction" else mt ()) ++
	  str".")

let intros_until_gen red h =
  Proofview.Goal.enter begin fun gl ->
  let n = depth_of_quantified_hypothesis red h gl in
  Tacticals.New.tclDO n (if red then introf else intro)
  end

let intros_until_id id = intros_until_gen false (NamedHyp id)
let intros_until_n_gen red n = intros_until_gen red (AnonHyp n)

let intros_until = intros_until_gen true
let intros_until_n = intros_until_n_gen true

let tclCHECKVAR id =
  Proofview.Goal.enter begin fun gl ->
    let _ = Tacmach.New.pf_get_hyp id gl in
    Proofview.tclUNIT ()
  end

let try_intros_until_id_check id =
  Tacticals.New.tclORELSE (intros_until_id id) (tclCHECKVAR id)

let try_intros_until tac = function
  | NamedHyp id -> Tacticals.New.tclTHEN (try_intros_until_id_check id) (tac id)
  | AnonHyp n -> Tacticals.New.tclTHEN (intros_until_n n) (Tacticals.New.onLastHypId tac)

let rec intros_move = function
  | [] -> Proofview.tclUNIT ()
  | (hyp,destopt) :: rest ->
      Tacticals.New.tclTHEN (intro_gen (NamingMustBe (CAst.make hyp)) destopt false false)
	(intros_move rest)

(* Apply a tactic on a quantified hypothesis, an hypothesis in context
   or a term with bindings *)

let tactic_infer_flags with_evar = {
  Pretyping.use_typeclasses = true;
  Pretyping.solve_unification_constraints = true;
  Pretyping.use_hook = Pfedit.solve_by_implicit_tactic ();
  Pretyping.fail_evar = not with_evar;
  Pretyping.expand_evars = true }

type evars_flag = bool     (* true = pose evars       false = fail on evars *)
type rec_flag = bool       (* true = recursive        false = not recursive *)
type advanced_flag = bool  (* true = advanced         false = basic *)
type clear_flag = bool option (* true = clear hyp, false = keep hyp, None = use default *)

type 'a core_destruction_arg =
  | ElimOnConstr of 'a
  | ElimOnIdent of lident
  | ElimOnAnonHyp of int

type 'a destruction_arg =
  clear_flag * 'a core_destruction_arg

let onOpenInductionArg env sigma tac = function
  | clear_flag,ElimOnConstr f ->
      let (sigma', cbl) = f env sigma in
      Tacticals.New.tclTHEN
        (Proofview.Unsafe.tclEVARS sigma')
        (tac clear_flag (sigma,cbl))
  | clear_flag,ElimOnAnonHyp n ->
      Tacticals.New.tclTHEN
        (intros_until_n n)
        (Tacticals.New.onLastHyp
           (fun c ->
             Proofview.Goal.enter begin fun gl ->
             let sigma = Tacmach.New.project gl in
             tac clear_flag (sigma,(c,NoBindings))
             end))
  | clear_flag,ElimOnIdent {CAst.v=id} ->
      (* A quantified hypothesis *)
      Tacticals.New.tclTHEN
        (try_intros_until_id_check id)
        (Proofview.Goal.enter begin fun gl ->
         let sigma = Tacmach.New.project gl in
         tac clear_flag (sigma,(mkVar id,NoBindings))
        end)

let onInductionArg tac = function
  | clear_flag,ElimOnConstr cbl ->
      tac clear_flag cbl
  | clear_flag,ElimOnAnonHyp n ->
      Tacticals.New.tclTHEN
        (intros_until_n n)
        (Tacticals.New.onLastHyp (fun c -> tac clear_flag (c,NoBindings)))
  | clear_flag,ElimOnIdent {CAst.v=id} ->
      (* A quantified hypothesis *)
      Tacticals.New.tclTHEN
        (try_intros_until_id_check id)
        (tac clear_flag (mkVar id,NoBindings))

let map_destruction_arg f sigma = function
  | clear_flag,ElimOnConstr g -> let sigma,x = f sigma g in (sigma, (clear_flag,ElimOnConstr x))
  | clear_flag,ElimOnAnonHyp n as x -> (sigma,x)
  | clear_flag,ElimOnIdent id as x -> (sigma,x)

let finish_delayed_evar_resolution with_evars env sigma f =
  let (sigma', (c, lbind)) = f env sigma in
  let flags = tactic_infer_flags with_evars in
  let (sigma', c) = finish_evar_resolution ~flags env sigma' (sigma,c) in
  (sigma', (c, lbind))

let with_no_bindings (c, lbind) =
  if lbind != NoBindings then error "'with' clause not supported here.";
  c

let force_destruction_arg with_evars env sigma c =
  map_destruction_arg (finish_delayed_evar_resolution with_evars env) sigma c

(****************************************)
(* tactic "cut" (actually modus ponens) *)
(****************************************)

let normalize_cut = false

let cut c =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let concl = Proofview.Goal.concl gl in
    let is_sort =
      try
        (** Backward compat: ensure that [c] is well-typed. *)
        let typ = Typing.unsafe_type_of env sigma c in
        let typ = whd_all env sigma typ in
        match EConstr.kind sigma typ with
        | Sort _ -> true
        | _ -> false
      with e when Pretype_errors.precatchable_exception e -> false
    in
    if is_sort then
      let id = next_name_away_with_default "H" Anonymous (Tacmach.New.pf_ids_set_of_hyps gl) in
      (** Backward compat: normalize [c]. *)
      let c = if normalize_cut then local_strong whd_betaiota sigma c else c in
      Refine.refine ~typecheck:false begin fun h ->
        let (h, f) = Evarutil.new_evar ~principal:true env h (mkArrow c (Vars.lift 1 concl)) in
        let (h, x) = Evarutil.new_evar env h c in
        let f = mkLetIn (Name id, x, c, mkApp (Vars.lift 1 f, [|mkRel 1|])) in
        (h, f)
      end
    else
      Tacticals.New.tclZEROMSG (str "Not a proposition or a type.")
  end

let error_uninstantiated_metas t clenv =
  let na = meta_name clenv.evd (List.hd (Metaset.elements (metavars_of t))) in
  let id = match na with Name id -> id | _ -> anomaly (Pp.str "unnamed dependent meta.")
  in user_err  (str "Cannot find an instance for " ++ Id.print id ++ str".")

let check_unresolved_evars_of_metas sigma clenv =
  (* This checks that Metas turned into Evars by *)
  (* Refiner.pose_all_metas_as_evars are resolved *)
  List.iter (fun (mv,b) -> match b with
  | Clval (_,(c,_),_) ->
    (match Constr.kind (EConstr.Unsafe.to_constr c.rebus) with
    | Evar (evk,_) when Evd.is_undefined clenv.evd evk
                     && not (Evd.mem sigma evk) ->
      error_uninstantiated_metas (mkMeta mv) clenv
    | _ -> ())
  | _ -> ())
  (meta_list clenv.evd)

let do_replace id = function
  | NamingMustBe {CAst.v=id'} when Option.equal Id.equal id (Some id') -> true
  | _ -> false

(* For a clenv expressing some lemma [C[?1:T1,...,?n:Tn] : P] and some
   goal [G], [clenv_refine_in] returns [n+1] subgoals, the [n] last
   ones (resp [n] first ones if [sidecond_first] is [true]) being the
   [Ti] and the first one (resp last one) being [G] whose hypothesis
   [id] is replaced by P using the proof given by [tac] *)

let clenv_refine_in ?(sidecond_first=false) with_evars ?(with_classes=true) 
    targetid id sigma0 clenv tac =
  let clenv = Clenvtac.clenv_pose_dependent_evars ~with_evars clenv in
  let clenv =
    if with_classes then
      { clenv with evd = Typeclasses.resolve_typeclasses 
	  ~fail:(not with_evars) clenv.env clenv.evd }
    else clenv
  in
  let new_hyp_typ = clenv_type clenv in
  if not with_evars then check_unresolved_evars_of_metas sigma0 clenv;
  if not with_evars && occur_meta clenv.evd new_hyp_typ then
    error_uninstantiated_metas new_hyp_typ clenv;
  let new_hyp_prf = clenv_value clenv in
  let exact_tac = Proofview.V82.tactic (Tacmach.refine_no_check new_hyp_prf) in
  let naming = NamingMustBe (CAst.make targetid) in
  let with_clear = do_replace (Some id) naming in
  Tacticals.New.tclTHEN
    (Proofview.Unsafe.tclEVARS (clear_metas clenv.evd))
    (if sidecond_first then
       Tacticals.New.tclTHENFIRST
         (assert_before_then_gen with_clear naming new_hyp_typ tac) exact_tac
     else
       Tacticals.New.tclTHENLAST
         (assert_after_then_gen with_clear naming new_hyp_typ tac) exact_tac)

(********************************************)
(*       Elimination tactics                *)
(********************************************)

let last_arg sigma c = match EConstr.kind sigma c with
  | App (f,cl) ->
      Array.last cl
  | _ -> anomaly (Pp.str "last_arg.")

let nth_arg sigma i c =
  if Int.equal i (-1) then last_arg sigma c else
  match EConstr.kind sigma c with
  | App (f,cl) -> cl.(i)
  | _ -> anomaly (Pp.str "nth_arg.")

let index_of_ind_arg sigma t =
  let rec aux i j t = match EConstr.kind sigma t with
  | Prod (_,t,u) ->
      (* heuristic *)
      if isInd sigma (fst (decompose_app sigma t)) then aux (Some j) (j+1) u
      else aux i (j+1) u
  | _ -> match i with
      | Some i -> i
      | None -> error "Could not find inductive argument of elimination scheme."
  in aux None 0 t

let rec contract_letin_in_lam_header sigma c =
  match EConstr.kind sigma c with
  | Lambda (x,t,c)  -> mkLambda (x,t,contract_letin_in_lam_header sigma c)
  | LetIn (x,b,t,c) -> contract_letin_in_lam_header sigma (subst1 b c)
  | _ -> c

let elimination_clause_scheme with_evars ?(with_classes=true) ?(flags=elim_flags ()) 
    rename i (elim, elimty, bindings) indclause =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.New.project gl in
  let elim = contract_letin_in_lam_header sigma elim in
  let elimclause = make_clenv_binding env sigma (elim, elimty) bindings in
  let indmv =
    (match EConstr.kind sigma (nth_arg sigma i elimclause.templval.rebus) with
       | Meta mv -> mv
       | _  -> user_err ~hdr:"elimination_clause"
             (str "The type of elimination clause is not well-formed."))
  in
  let elimclause' = clenv_fchain ~flags indmv elimclause indclause in
  Clenvtac.res_pf elimclause' ~with_evars ~with_classes ~flags
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
  elimbody : EConstr.constr with_bindings
}

let general_elim_clause_gen elimtac indclause elim =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.New.project gl in
  let (elimc,lbindelimc) = elim.elimbody in
  let elimt = Retyping.get_type_of env sigma elimc in
  let i =
    match elim.elimindex with None -> index_of_ind_arg sigma elimt | Some i -> i in
  elimtac elim.elimrename i (elimc, elimt, lbindelimc) indclause
  end

let general_elim with_evars clear_flag (c, lbindc) elim =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.New.project gl in
  let ct = Retyping.get_type_of env sigma c in
  let t = try snd (reduce_to_quantified_ind env sigma ct) with UserError _ -> ct in
  let elimtac = elimination_clause_scheme with_evars in
  let indclause  = make_clenv_binding env sigma (c, t) lbindc in
  let sigma = meta_merge sigma (clear_metas indclause.evd) in
  Proofview.Unsafe.tclEVARS sigma <*>
  Tacticals.New.tclTHEN
    (general_elim_clause_gen elimtac indclause elim)
    (apply_clear_request clear_flag (use_clear_hyp_by_default ()) c)
  end

(* Case analysis tactics *)

let general_case_analysis_in_context with_evars clear_flag (c,lbindc) =
  Proofview.Goal.enter begin fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  let env = Proofview.Goal.env gl in
  let concl = Proofview.Goal.concl gl in
  let t = Retyping.get_type_of env sigma c in
  let (mind,_) = reduce_to_quantified_ind env sigma t in
  let sort = Tacticals.New.elimination_sort_of_goal gl in
  let mind = on_snd (fun u -> EInstance.kind sigma u) mind in
  let (sigma, elim) =
    if dependent sigma c concl then
      build_case_analysis_scheme env sigma mind true sort
    else
      build_case_analysis_scheme_default env sigma mind sort in
  let elim = EConstr.of_constr elim in
  Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
  (general_elim with_evars clear_flag (c,lbindc)
   {elimindex = None; elimbody = (elim,NoBindings);
    elimrename = Some (false, constructors_nrealdecls (fst mind))})
  end

let general_case_analysis with_evars clear_flag (c,lbindc as cx) =
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma c with
    | Var id when lbindc == NoBindings ->
	Tacticals.New.tclTHEN (try_intros_until_id_check id)
	  (general_case_analysis_in_context with_evars clear_flag cx)
    | _ ->
        general_case_analysis_in_context with_evars clear_flag cx

let simplest_case c = general_case_analysis false None (c,NoBindings)
let simplest_ecase c = general_case_analysis true None (c,NoBindings)

(* Elimination tactic with bindings but using the default elimination
 * constant associated with the type. *)

exception IsNonrec

let is_nonrec mind = (Global.lookup_mind (fst mind)).mind_finite == Declarations.BiFinite

let find_ind_eliminator ind s gl =
  let gr = lookup_eliminator ind s in
  Tacmach.New.pf_apply Evd.fresh_global gl gr

let find_eliminator c gl =
  let ((ind,u),t) = Tacmach.New.pf_reduce_to_quantified_ind gl (Tacmach.New.pf_unsafe_type_of gl c) in
  if is_nonrec ind then raise IsNonrec;
  let evd, c = find_ind_eliminator ind (Tacticals.New.elimination_sort_of_goal gl) gl in
    evd, {elimindex = None; elimbody = (c,NoBindings);
          elimrename = Some (true, constructors_nrealdecls ind)}

let default_elim with_evars clear_flag (c,_ as cx) =
  Proofview.tclORELSE
    (Proofview.Goal.enter begin fun gl ->
      let sigma, elim = find_eliminator c gl in
      Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
      (general_elim with_evars clear_flag cx elim)
    end)
    begin function (e, info) -> match e with
      | IsNonrec ->
          (* For records, induction principles aren't there by default
             anymore.  Instead, we do a case analysis. *)
          general_case_analysis with_evars clear_flag cx
      | e -> Proofview.tclZERO ~info e
    end

let elim_in_context with_evars clear_flag c = function
  | Some elim ->
      general_elim with_evars clear_flag c
        {elimindex = Some (-1); elimbody = elim; elimrename = None}
  | None -> default_elim with_evars clear_flag c

let elim with_evars clear_flag (c,lbindc as cx) elim =
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma c with
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
  (** The evarmap of elimclause is assumed to be an extension of hypclause, so
      we do not need to merge the universes coming from hypclause. *)
  try clenv_fchain ~with_univs:false ~flags mv elimclause hypclause
  with PretypeError (env,evd,NoOccurrenceFound (op,_)) ->
    (* Set the hypothesis name in the message *)
    raise (PretypeError (env,evd,NoOccurrenceFound (op,Some id)))

let elimination_in_clause_scheme with_evars ?(flags=elim_flags ()) 
    id rename i (elim, elimty, bindings) indclause =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.New.project gl in
  let elim = contract_letin_in_lam_header sigma elim in
  let elimclause = make_clenv_binding env sigma (elim, elimty) bindings in
  let indmv = destMeta sigma (nth_arg sigma i elimclause.templval.rebus) in
  let hypmv =
    match List.remove Int.equal indmv (clenv_independent elimclause) with
    | [a] -> a
    | _ -> user_err ~hdr:"elimination_clause"
             (str "The type of elimination clause is not well-formed.")
  in
  let elimclause'  = clenv_fchain ~flags indmv elimclause indclause in
  let hyp = mkVar id in
  let hyp_typ = Retyping.get_type_of env sigma hyp in
  let hypclause = mk_clenv_from_env env sigma (Some 0) (hyp, hyp_typ) in
  let elimclause'' = clenv_fchain_in id ~flags hypmv elimclause' hypclause in
  let new_hyp_typ  = clenv_type elimclause'' in
  if EConstr.eq_constr sigma hyp_typ new_hyp_typ then
    user_err ~hdr:"general_rewrite_in"
      (str "Nothing to rewrite in " ++ Id.print id ++ str".");
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
  | DefinedRecord of Constant.t option list
  | NotADefinedRecordUseScheme of constr

let make_projection env sigma params cstr sign elim i n c u =
  let open Context.Rel.Declaration in
  let elim = match elim with
  | NotADefinedRecordUseScheme elim ->
      (* bugs: goes from right to left when i increases! *)
      let cs_args = List.map (fun d -> map_rel_decl EConstr.of_constr d) cstr.cs_args in
      let decl = List.nth cs_args i in
      let t = RelDecl.get_type decl in
      let b = match decl with LocalAssum _ -> mkRel (i+1) | LocalDef (_,b,_) -> b in
      let branch = it_mkLambda_or_LetIn b cs_args in
      if
	(* excludes dependent projection types *)
	noccur_between sigma 1 (n-i-1) t
	(* to avoid surprising unifications, excludes flexible
	projection types or lambda which will be instantiated by Meta/Evar *)
	&& not (isEvar sigma (fst (whd_betaiota_stack sigma t)))
	&& (accept_universal_lemma_under_conjunctions () || not (isRel sigma t))
      then
        let t = lift (i+1-n) t in
	let abselim = beta_applist sigma (elim, params@[t;branch]) in
	let args = Context.Rel.to_extended_vect mkRel 0 sign in
	let c = beta_applist sigma (abselim, [mkApp (c, args)]) in
	  Some (it_mkLambda_or_LetIn c sign, it_mkProd_or_LetIn t sign)
      else
	None
  | DefinedRecord l ->
      (* goes from left to right when i increases! *)
      match List.nth l i with
      | Some proj ->
	  let args = Context.Rel.to_extended_vect mkRel 0 sign in
	  let proj =
            match Recordops.find_primitive_projection proj with
            | Some proj ->
	      mkProj (Projection.make proj false, mkApp (c, args))
            | None ->
	      mkApp (mkConstU (proj,u), Array.append (Array.of_list params)
		[|mkApp (c, args)|])
	  in
	  let app = it_mkLambda_or_LetIn proj sign in
	  let t = Retyping.get_type_of env sigma app in
	    Some (app, t)
      | None -> None
  in elim

let descend_in_conjunctions avoid tac (err, info) c =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.New.project gl in
  try
    let t = Retyping.get_type_of env sigma c in
    let ((ind,u),t) = reduce_to_quantified_ind env sigma t in
    let sign,ccl = EConstr.decompose_prod_assum sigma t in
    match match_with_tuple sigma ccl with
    | Some (_,_,isrec) ->
	let n = (constructors_nrealargs ind).(0) in
	let sort = Tacticals.New.elimination_sort_of_goal gl in
	let IndType (indf,_) = find_rectype env sigma ccl in
	let (_,inst), params = dest_ind_family indf in
	let params = List.map EConstr.of_constr params in
	let cstr = (get_constructors env indf).(0) in
	let elim =
	  try DefinedRecord (Recordops.lookup_projections ind)
	  with Not_found ->
            let u = EInstance.kind sigma u in
	    let (_, elim) = build_case_analysis_scheme env sigma (ind,u) false sort in
	    let elim = EConstr.of_constr elim in
	    NotADefinedRecordUseScheme elim in
	Tacticals.New.tclORELSE0
	(Tacticals.New.tclFIRST
	  (List.init n (fun i ->
            Proofview.Goal.enter begin fun gl ->
            let env = Proofview.Goal.env gl in
            let sigma = Tacmach.New.project gl in
	    match make_projection env sigma params cstr sign elim i n c u with
	    | None -> Tacticals.New.tclFAIL 0 (mt())
	    | Some (p,pt) ->
	      Tacticals.New.tclTHENS
		(assert_before_gen false (NamingAvoid avoid) pt)
		[Proofview.V82.tactic (refine p);
		 (* Might be ill-typed due to forbidden elimination. *)
		 Tacticals.New.onLastHypId (tac (not isrec))]
           end)))
          (Proofview.tclZERO ~info err)
    | None -> Proofview.tclZERO ~info err
  with RefinerError _|UserError _ -> Proofview.tclZERO ~info err
  end

(****************************************************)
(*            Resolution tactics                    *)
(****************************************************)

let tclORELSEOPT t k =
  Proofview.tclORELSE t
    (fun e -> match k e with
    | None ->
      let (e, info) = e in
      Proofview.tclZERO ~info e
    | Some tac -> tac)

let general_apply ?(respect_opaque=false) with_delta with_destruct with_evars
    clear_flag {CAst.loc;v=(c,lbind : EConstr.constr with_bindings)} =
  Proofview.Goal.enter begin fun gl ->
  let concl = Proofview.Goal.concl gl in
  let sigma = Tacmach.New.project gl in
  (* The actual type of the theorem. It will be matched against the
  goal. If this fails, then the head constant will be unfolded step by
  step. *)
  let concl_nprod = nb_prod_modulo_zeta sigma concl in
  let rec try_main_apply with_destruct c =
    Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let ts =
      if respect_opaque then Conv_oracle.get_transp_state (oracle env)
      else full_transparent_state
    in
    let flags =
      if with_delta then default_unify_flags () else default_no_delta_unify_flags ts in
    let thm_ty0 = nf_betaiota env sigma (Retyping.get_type_of env sigma c) in
    let try_apply thm_ty nprod =
      try
        let n = nb_prod_modulo_zeta sigma thm_ty - nprod in
        if n<0 then error "Applied theorem does not have enough premises.";
        let clause = make_clenv_binding_apply env sigma (Some n) (c,thm_ty) lbind in
        Clenvtac.res_pf clause ~with_evars ~flags
      with exn when catchable_exception exn ->
        Proofview.tclZERO exn
    in
    let rec try_red_apply thm_ty (exn0, info) =
      try
        (* Try to head-reduce the conclusion of the theorem *)
        let red_thm = try_red_product env sigma thm_ty in
        tclORELSEOPT
          (try_apply red_thm concl_nprod)
          (function (e, info) -> match e with
          | PretypeError _|RefinerError _|UserError _|Failure _ ->
            Some (try_red_apply red_thm (exn0, info))
          | _ -> None)
      with Redelimination ->
        (* Last chance: if the head is a variable, apply may try
            second order unification *)
        let info = Option.cata (fun loc -> Loc.add_loc info loc) info loc in
        let tac =
          if with_destruct then
            descend_in_conjunctions Id.Set.empty
              (fun b id ->
                Tacticals.New.tclTHEN
                  (try_main_apply b (mkVar id))
                  (clear [id]))
              (exn0, info) c
          else
            Proofview.tclZERO ~info exn0 in
        if not (Int.equal concl_nprod 0) then
          tclORELSEOPT
            (try_apply thm_ty 0)
            (function (e, info) -> match e with
            | PretypeError _|RefinerError _|UserError _|Failure _->
              Some tac
            | _ -> None)
        else
          tac
    in
    tclORELSEOPT
      (try_apply thm_ty0 concl_nprod)
      (function (e, info) -> match e with
      | PretypeError _|RefinerError _|UserError _|Failure _ ->
        Some (try_red_apply thm_ty0 (e, info))
      | _ -> None)
    end
  in
    Tacticals.New.tclTHEN
      (try_main_apply with_destruct c)
      (apply_clear_request clear_flag (use_clear_hyp_by_default ()) c)
  end

let rec apply_with_bindings_gen b e = function
  | [] -> Proofview.tclUNIT ()
  | [k,cb] -> general_apply b b e k cb
  | (k,cb)::cbl ->
      Tacticals.New.tclTHENLAST
        (general_apply b b e k cb)
        (apply_with_bindings_gen b e cbl)

let apply_with_delayed_bindings_gen b e l =
  let one k {CAst.loc;v=f} =
    Proofview.Goal.enter begin fun gl ->
      let sigma = Tacmach.New.project gl in
      let env = Proofview.Goal.env gl in
      let (sigma, cb) = f env sigma in
	Tacticals.New.tclWITHHOLES e
          (general_apply ~respect_opaque:(not b) b b e k CAst.(make ?loc cb)) sigma
    end
  in
  let rec aux = function
    | [] -> Proofview.tclUNIT ()
    | [k,f] -> one k f
    | (k,f)::cbl ->
      Tacticals.New.tclTHENLAST
        (one k f) (aux cbl)
  in aux l

let apply_with_bindings cb = apply_with_bindings_gen false false [None,(CAst.make cb)]

let eapply_with_bindings cb = apply_with_bindings_gen false true [None,(CAst.make cb)]

let apply c = apply_with_bindings_gen false false [None,(CAst.make (c,NoBindings))]

let eapply c = apply_with_bindings_gen false true [None,(CAst.make (c,NoBindings))]

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

exception UnableToApply

let progress_with_clause flags innerclause clause =
  let ordered_metas = List.rev (clenv_independent clause) in
  if List.is_empty ordered_metas then raise UnableToApply;
  let f mv =
    try Some (find_matching_clause (clenv_fchain ~with_univs:false mv ~flags clause) innerclause)
    with Failure _ -> None
  in
  try List.find_map f ordered_metas
  with Not_found -> raise UnableToApply

let explain_unable_to_apply_lemma ?loc env sigma thm innerclause =
  user_err ?loc (hov 0
    (Pp.str "Unable to apply lemma of type" ++ brk(1,1) ++
     Pp.quote (Printer.pr_leconstr_env env sigma thm) ++ spc() ++
     str "on hypothesis of type" ++ brk(1,1) ++
     Pp.quote (Printer.pr_leconstr_env innerclause.env innerclause.evd (clenv_type innerclause)) ++
     str "."))

let apply_in_once_main flags innerclause env sigma (loc,d,lbind) =
  let thm = nf_betaiota env sigma (Retyping.get_type_of env sigma d) in
  let rec aux clause =
    try progress_with_clause flags innerclause clause
    with e when CErrors.noncritical e ->
    let e' = CErrors.push e in
    try aux (clenv_push_prod clause)
    with NotExtensibleClause ->
      match e with
      | UnableToApply -> explain_unable_to_apply_lemma ?loc env sigma thm innerclause
      | _ -> iraise e'
  in
  aux (make_clenv_binding env sigma (d,thm) lbind)

let apply_in_once ?(respect_opaque = false) sidecond_first with_delta
    with_destruct with_evars naming id (clear_flag,{ CAst.loc; v= d,lbind}) tac =
  let open Context.Rel.Declaration in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.New.project gl in
  let t' = Tacmach.New.pf_get_hyp_typ id gl in
  let innerclause = mk_clenv_from_env env sigma (Some 0) (mkVar id,t') in
  let targetid = find_name true (LocalAssum (Anonymous,t')) naming gl in
  let rec aux idstoclear with_destruct c =
    Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let ts =
      if respect_opaque then Conv_oracle.get_transp_state (oracle env)
      else full_transparent_state
    in
    let flags =
      if with_delta then default_unify_flags () else default_no_delta_unify_flags ts in
    try
      let clause = apply_in_once_main flags innerclause env sigma (loc,c,lbind) in
      clenv_refine_in ~sidecond_first with_evars targetid id sigma clause
        (fun id ->
          Tacticals.New.tclTHENLIST [
            apply_clear_request clear_flag false c;
            clear idstoclear;
            tac id
          ])
    with e when with_destruct && CErrors.noncritical e ->
      let (e, info) = CErrors.push e in
        (descend_in_conjunctions (Id.Set.singleton targetid)
           (fun b id -> aux (id::idstoclear) b (mkVar id))
           (e, info) c)
    end
  in
  aux [] with_destruct d
  end

let apply_in_delayed_once ?(respect_opaque = false) sidecond_first with_delta
    with_destruct with_evars naming id (clear_flag,{CAst.loc;v=f}) tac =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let (sigma, c) = f env sigma in
    Tacticals.New.tclWITHHOLES with_evars 
      (apply_in_once ~respect_opaque sidecond_first with_delta with_destruct with_evars
         naming id (clear_flag,CAst.(make ?loc c)) tac)
      sigma
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
  Proofview.Goal.enter begin fun gl ->
    let sigma = Tacmach.New.project gl in
    match EConstr.kind sigma (Tacmach.New.pf_hnf_constr gl (Tacmach.New.pf_unsafe_type_of gl c)) with
      | Prod (_,c1,c2) when Vars.noccurn sigma 1 c2 ->
        let concl = Proofview.Goal.concl gl in
        let env = Tacmach.New.pf_env gl in
        Refine.refine ~typecheck:false begin fun sigma ->
          let typ = mkProd (Anonymous, c2, concl) in
          let (sigma, f) = Evarutil.new_evar env sigma typ in
          let (sigma, x) = Evarutil.new_evar env sigma c1 in
          (sigma, mkApp (f, [|mkApp (c, [|x|])|]))
        end
      | _ -> error "lapply needs a non-dependent product."
  end

(********************************************************************)
(*               Exact tactics                                      *)
(********************************************************************)

(* let convert_leqkey = CProfile.declare_profile "convert_leq";; *)
(* let convert_leq = CProfile.profile3 convert_leqkey convert_leq *)

(* let refine_no_checkkey = CProfile.declare_profile "refine_no_check";; *)
(* let refine_no_check = CProfile.profile2 refine_no_checkkey refine_no_check *)

let exact_no_check c =
  Refine.refine ~typecheck:false (fun h -> (h,c))

let exact_check c =
  Proofview.Goal.enter begin fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  (** We do not need to normalize the goal because we just check convertibility *)
  let concl = Proofview.Goal.concl gl in
  let env = Proofview.Goal.env gl in
  let sigma, ct = Typing.type_of env sigma c in
  Tacticals.New.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
  (Tacticals.New.tclTHEN (convert_leq ct concl) (exact_no_check c))
  end

let cast_no_check cast c =
  Proofview.Goal.enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    exact_no_check (mkCast (c, cast, concl))
  end

let vm_cast_no_check c = cast_no_check VMcast c
let native_cast_no_check c = cast_no_check NATIVEcast c

let exact_proof c =
  let open Tacmach.New in
  Proofview.Goal.enter begin fun gl ->
  Refine.refine ~typecheck:false begin fun sigma ->
    let (c, ctx) = Constrintern.interp_casted_constr (pf_env gl) sigma c (pf_concl gl) in
    let sigma = Evd.merge_universe_context sigma ctx in
    (sigma, c)
  end
  end

let assumption =
  let rec arec gl only_eq = function
  | [] ->
    if only_eq then
      let hyps = Proofview.Goal.hyps gl in
      arec gl false hyps
    else Tacticals.New.tclZEROMSG (str "No such assumption.")
  | decl::rest ->
    let t = NamedDecl.get_type decl in
    let concl = Proofview.Goal.concl gl in
    let sigma = Tacmach.New.project gl in
    let ans =
      if only_eq then
        if EConstr.eq_constr sigma t concl then Some sigma
        else None
      else
        let env = Proofview.Goal.env gl in
        infer_conv env sigma t concl
    in
    match ans with
    | Some sigma ->
      (Proofview.Unsafe.tclEVARS sigma) <*>
	exact_no_check (mkVar (NamedDecl.get_id decl))
    | None -> arec gl only_eq rest
  in
  let assumption_tac gl =
    let hyps = Proofview.Goal.hyps gl in
    arec gl true hyps
  in
  Proofview.Goal.enter assumption_tac

(*****************************************************************)
(*          Modification of a local context                      *)
(*****************************************************************)

let on_the_bodies = function
| [] -> assert false
| [id] -> str " depends on the body of " ++ Id.print id
| l -> str " depends on the bodies of " ++ pr_sequence Id.print l

exception DependsOnBody of Id.t option

let check_is_type env sigma ty =
  try
    let sigma, _ = Typing.sort_of env sigma ty in
    sigma
  with e when CErrors.noncritical e ->
    raise (DependsOnBody None)

let check_decl env sigma decl =
  let open Context.Named.Declaration in
  let ty = NamedDecl.get_type decl in
  try
    let sigma, _ = Typing.sort_of env sigma ty in
    let sigma = match decl with
    | LocalAssum _ -> sigma
    | LocalDef (_,c,_) -> Typing.check env sigma c ty
    in
    sigma
  with e when CErrors.noncritical e ->
    let id = NamedDecl.get_id decl in
    raise (DependsOnBody (Some id))

let clear_body ids =
  let open Context.Named.Declaration in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let concl = Proofview.Goal.concl gl in
    let sigma = Tacmach.New.project gl in
    let ctx = named_context env in
    let map = function
    | LocalAssum (id,t) as decl ->
      let () = if List.mem_f Id.equal id ids then
        user_err  (str "Hypothesis " ++ Id.print id ++ str " is not a local definition")
      in
      decl
    | LocalDef (id,_,t) as decl ->
      if List.mem_f Id.equal id ids then LocalAssum (id, t) else decl
    in
    let ctx = List.map map ctx in
    let base_env = reset_context env in
    let env = push_named_context ctx base_env in
    let check =
      try
        let check (env, sigma, seen) decl =
          (** Do no recheck hypotheses that do not depend *)
          let sigma =
            if not seen then sigma
            else if List.exists (fun id -> occur_var_in_decl env sigma id decl) ids then
              check_decl env sigma decl
            else sigma
          in
          let seen = seen || List.mem_f Id.equal (NamedDecl.get_id decl) ids in
          (push_named decl env, sigma, seen)
        in
        let (env, sigma, _) = List.fold_left check (base_env, sigma, false) (List.rev ctx) in
        let sigma =
          if List.exists (fun id -> occur_var env sigma id concl) ids then
            check_is_type env sigma concl
          else sigma
        in
        Proofview.Unsafe.tclEVARS sigma
      with DependsOnBody where ->
        let msg = match where with
        | None -> str "Conclusion" ++ on_the_bodies ids
        | Some id -> str "Hypothesis " ++ Id.print id ++ on_the_bodies ids
        in
        Tacticals.New.tclZEROMSG msg
    in
    check <*>
    Refine.refine ~typecheck:false begin fun sigma ->
      Evarutil.new_evar env sigma ~principal:true concl
    end
  end

let clear_wildcards ids =
  Tacticals.New.tclMAP (fun {CAst.loc;v=id} -> clear [id]) ids

(*   Takes a list of booleans, and introduces all the variables
 *  quantified in the goal which are associated with a value
 *  true  in the boolean list. *)

let rec intros_clearing = function
  | []          -> Proofview.tclUNIT ()
  | (false::tl) -> Tacticals.New.tclTHEN intro (intros_clearing tl)
  | (true::tl)  ->
      Tacticals.New.tclTHENLIST
        [ intro; Tacticals.New.onLastHypId (fun id -> clear [id]); intros_clearing tl]

(* Keeping only a few hypotheses *)

let keep hyps =
  Proofview.Goal.enter begin fun gl ->
  Proofview.tclENV >>= fun env ->
  let ccl = Proofview.Goal.concl gl in
  let sigma = Tacmach.New.project gl in
  let cl,_ =
    fold_named_context_reverse (fun (clear,keep) decl ->
      let decl = map_named_decl EConstr.of_constr decl in
      let hyp = NamedDecl.get_id decl in
      if Id.List.mem hyp hyps
        || List.exists (occur_var_in_decl env sigma hyp) keep
	|| occur_var env sigma hyp ccl
      then (clear,decl::keep)
      else (hyp::clear,keep))
      ~init:([],[]) (Proofview.Goal.env gl)
  in
  clear cl
  end

(*********************************)
(*  Basic generalization tactics *)
(*********************************)

(* Given a type [T] convertible to [forall x1..xn:A1..An(x1..xn-1), G(x1..xn)]
   and [a1..an:A1..An(a1..an-1)] such that the goal is [G(a1..an)],
   this generalizes [hyps |- goal] into [hyps |- T] *)

let apply_type ~typecheck newcl args =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let store = Proofview.Goal.extra gl in
    Refine.refine ~typecheck begin fun sigma ->
      let newcl = nf_betaiota env sigma newcl (* As in former Logic.refine *) in
      let (sigma, ev) =
        Evarutil.new_evar env sigma ~principal:true ~store newcl in
      (sigma, applist (ev, args))
    end
  end

(* Given a context [hyps] with domain [x1..xn], possibly with let-ins,
   and well-typed in the current goal, [bring_hyps hyps] generalizes
   [ctxt |- G(x1..xn] into [ctxt |- forall hyps, G(x1..xn)] *)

let bring_hyps hyps =
  if List.is_empty hyps then Tacticals.New.tclIDTAC
  else
    Proofview.Goal.enter begin fun gl ->
      let env = Proofview.Goal.env gl in
      let store = Proofview.Goal.extra gl in
      let concl = Tacmach.New.pf_concl gl in
      let newcl = List.fold_right mkNamedProd_or_LetIn hyps concl in
      let args = Array.of_list (Context.Named.to_instance mkVar hyps) in
      Refine.refine ~typecheck:false begin fun sigma ->
        let (sigma, ev) =
          Evarutil.new_evar env sigma ~principal:true ~store newcl in
        (sigma, mkApp (ev, args))
      end
    end

let revert hyps = 
  Proofview.Goal.enter begin fun gl ->
    let ctx = List.map (fun id -> Tacmach.New.pf_get_hyp id gl) hyps in
      (bring_hyps ctx) <*> (clear hyps)
  end

(************************)
(* Introduction tactics *)
(************************)

let check_number_of_constructors expctdnumopt i nconstr =
  if Int.equal i 0 then error "The constructors are numbered starting from 1.";
  begin match expctdnumopt with
    | Some n when not (Int.equal n nconstr) ->
	user_err ~hdr:"Tactics.check_number_of_constructors"
          (str "Not an inductive goal with " ++ int n ++ str (String.plural n " constructor") ++ str ".")
    | _ -> ()
  end;
  if i > nconstr then error "Not enough constructors."

let constructor_core with_evars cstr lbind =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let (sigma, (cons, u)) = Evd.fresh_constructor_instance env sigma cstr in
    let cons = mkConstructU (cons, EInstance.make u) in
    let apply_tac = general_apply true false with_evars None (CAst.make (cons,lbind)) in
    Tacticals.New.tclTHEN (Proofview.Unsafe.tclEVARS sigma) apply_tac
  end

let constructor_tac with_evars expctdnumopt i lbind =
  Proofview.Goal.enter begin fun gl ->
    let cl = Tacmach.New.pf_concl gl in
    let ((ind,_),redcl) = Tacmach.New.pf_apply Tacred.reduce_to_quantified_ind gl cl in
    let nconstr = Array.length (snd (Global.lookup_inductive ind)).mind_consnames in
    check_number_of_constructors expctdnumopt i nconstr;
    Tacticals.New.tclTHENLIST [
      convert_concl_no_check redcl DEFAULTcast;
      intros;
      constructor_core with_evars (ind, i) lbind
    ]
  end

let one_constructor i lbind = constructor_tac false None i lbind

(* Try to apply the constructor of the inductive definition followed by
   a tactic t given as an argument.
   Should be generalize in Constructor (Fun c : I -> tactic)
 *)

let any_constructor with_evars tacopt =
  let one_constr =
    let tac cstr = constructor_core with_evars cstr NoBindings in
    match tacopt with
    | None -> tac
    | Some t -> fun cstr -> Tacticals.New.tclTHEN (tac cstr) t in
  let rec any_constr ind n i () =
    if Int.equal i n then one_constr (ind,i)
    else Tacticals.New.tclORD (one_constr (ind,i)) (any_constr ind n (i + 1)) in
  Proofview.Goal.enter begin fun gl ->
    let cl = Tacmach.New.pf_concl gl in
    let (ind,_),redcl = Tacmach.New.pf_apply Tacred.reduce_to_quantified_ind gl cl in
    let nconstr =
      Array.length (snd (Global.lookup_inductive ind)).mind_consnames in
    if Int.equal nconstr 0 then error "The type has no constructors.";
    Tacticals.New.tclTHENLIST [
      convert_concl_no_check redcl DEFAULTcast;
      intros;
      any_constr ind nconstr 1 ()
    ]
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
  user_err ?loc  (str "Unexpected " ++ str s1 ++ str " (" ++
    (if Int.equal nb 0 then (str s3 ++ str s2) else
      (str "at most " ++ int nb ++ str s2)) ++ spc () ++
       str (if Int.equal nb 1 then "was" else "were") ++
      strbrk " expected in the branch).")

let intro_decomp_eq_function = ref (fun _ -> failwith "Not implemented")

let declare_intro_decomp_eq f = intro_decomp_eq_function := f

let my_find_eq_data_decompose gl t =
  try Some (find_eq_data_decompose gl t)
  with e when is_anomaly e
    (* Hack in case equality is not yet defined... one day, maybe,
       known equalities will be dynamically registered *)
      -> None
  | Constr_matching.PatternMatchingFailure -> None

let intro_decomp_eq ?loc l thin tac id =
  Proofview.Goal.enter begin fun gl ->
  let c = mkVar id in
  let t = Tacmach.New.pf_unsafe_type_of gl c in
  let _,t = Tacmach.New.pf_reduce_to_quantified_ind gl t in
  match my_find_eq_data_decompose gl t with
  | Some (eq,u,eq_args) ->
    !intro_decomp_eq_function
    (fun n -> tac ((CAst.make id)::thin) (Some (true,n)) l)
    (eq,t,eq_args) (c, t)
  | None ->
    Tacticals.New.tclZEROMSG (str "Not a primitive equality here.")
  end

let intro_or_and_pattern ?loc with_evars bracketed ll thin tac id =
  Proofview.Goal.enter begin fun gl ->
  let c = mkVar id in
  let t = Tacmach.New.pf_unsafe_type_of gl c in
  let (ind,t) = Tacmach.New.pf_reduce_to_quantified_ind gl t in
  let branchsigns = compute_constructor_signatures ~rec_flag:false ind in
  let nv_with_let = Array.map List.length branchsigns in
  let ll = fix_empty_or_and_pattern (Array.length branchsigns) ll in
  let ll = get_and_check_or_and_pattern ?loc ll branchsigns in
  Tacticals.New.tclTHENLASTn
    (Tacticals.New.tclTHEN (simplest_ecase c) (clear [id]))
    (Array.map2 (fun n l -> tac thin (Some (bracketed,n)) l)
       nv_with_let ll)
  end

let rewrite_hyp_then assert_style with_evars thin l2r id tac =
  let rew_on l2r =
    Hook.get forward_general_rewrite_clause l2r with_evars (mkVar id,NoBindings) in
  let subst_on l2r x rhs =
    Hook.get forward_subst_one true x (id,rhs,l2r) in
  let clear_var_and_eq id' = clear [id';id] in
  let early_clear id' thin =
    List.filter (fun {CAst.v=id} -> not (Id.equal id id')) thin in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let type_of = Tacmach.New.pf_unsafe_type_of gl in
    let whd_all = Tacmach.New.pf_apply whd_all gl in
    let t = whd_all (type_of (mkVar id)) in
    let eqtac, thin = match match_with_equality_type sigma t with
    | Some (hdcncl,[_;lhs;rhs]) ->
        if l2r && isVar sigma lhs && not (occur_var env sigma (destVar sigma lhs) rhs) then
          let id' = destVar sigma lhs in
          subst_on l2r id' rhs, early_clear id' thin
        else if not l2r && isVar sigma rhs && not (occur_var env sigma (destVar sigma rhs) lhs) then
          let id' = destVar sigma rhs in
          subst_on l2r id' lhs, early_clear id' thin
        else
          Tacticals.New.tclTHEN (rew_on l2r onConcl) (clear [id]),
          thin
    | Some (hdcncl,[c]) ->
        let l2r = not l2r in (* equality of the form eq_true *)
        if isVar sigma c then
          let id' = destVar sigma c in
          Tacticals.New.tclTHEN (rew_on l2r allHypsAndConcl) 
	    (clear_var_and_eq id'),
          early_clear id' thin
        else
          Tacticals.New.tclTHEN (rew_on l2r onConcl) (clear [id]),
          thin
    | _ ->
        Tacticals.New.tclTHEN (rew_on l2r onConcl) (clear [id]),
        thin in
    (* Skip the side conditions of the rewriting step *)
    Tacticals.New.tclTHENFIRST eqtac (tac thin)
  end 

let prepare_naming ?loc = function
  | IntroIdentifier id -> NamingMustBe (CAst.make ?loc id)
  | IntroAnonymous -> NamingAvoid Id.Set.empty
  | IntroFresh id -> NamingBasedOn (id, Id.Set.empty)

let rec explicit_intro_names = let open CAst in function
| {v=IntroForthcoming _} :: l -> explicit_intro_names l
| {v=IntroNaming (IntroIdentifier id)} :: l -> Id.Set.add id (explicit_intro_names l)
| {v=IntroAction (IntroOrAndPattern l)} :: l' ->
    let ll = match l with IntroAndPattern l -> [l] | IntroOrPattern ll -> ll in
    let fold accu l = Id.Set.union accu (explicit_intro_names (l@l')) in
    List.fold_left fold Id.Set.empty ll
| {v=IntroAction (IntroInjection l)} :: l' ->
    explicit_intro_names (l@l')
| {v=IntroAction (IntroApplyOn (c,pat))} :: l' ->
    explicit_intro_names (pat::l')
| {v=(IntroNaming (IntroAnonymous | IntroFresh _)
     | IntroAction (IntroWildcard | IntroRewrite _))} :: l ->
     explicit_intro_names l
| [] -> Id.Set.empty

let rec check_name_unicity env ok seen = let open CAst in function
| {v=IntroForthcoming _} :: l -> check_name_unicity env ok seen l
| {loc;v=IntroNaming (IntroIdentifier id)} :: l ->
   (try
      ignore (if List.mem_f Id.equal id ok then raise Not_found else lookup_named id env);
      user_err ?loc (Id.print id ++ str" is already used.")
   with Not_found ->
     if List.mem_f Id.equal id seen then
       user_err ?loc (Id.print id ++ str" is used twice.")
     else
       check_name_unicity env ok (id::seen) l)
| {v=IntroAction (IntroOrAndPattern l)} :: l' ->
    let ll = match l with IntroAndPattern l -> [l] | IntroOrPattern ll -> ll in
    List.iter (fun l -> check_name_unicity env ok seen (l@l')) ll
| {v=IntroAction (IntroInjection l)} :: l' ->
    check_name_unicity env ok seen (l@l')
| {v=IntroAction (IntroApplyOn (c,pat))} :: l' ->
    check_name_unicity env ok seen (pat::l')
| {v=(IntroNaming (IntroAnonymous | IntroFresh _)
     | IntroAction (IntroWildcard | IntroRewrite _))} :: l ->
     check_name_unicity env ok seen l
| [] -> ()

let wild_id = Id.of_string "_tmp"

let rec list_mem_assoc_right id = function
  | [] -> false
  | {CAst.v=id'}::l -> Id.equal id id' || list_mem_assoc_right id l

let check_thin_clash_then id thin avoid tac =
  if list_mem_assoc_right id thin then
    let newid = next_ident_away (add_suffix id "'") avoid in
    let thin =
      List.map CAst.(map (fun id' -> if Id.equal id id' then newid else id')) thin in
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
  | IntroWildcard -> NamingBasedOn (wild_id, Id.Set.union avoid (explicit_intro_names l))
  | pat -> NamingAvoid(Id.Set.union avoid (explicit_intro_names ((CAst.make @@ IntroAction pat)::l)))

let fit_bound n = function
  | None -> true
  | Some (use_bound,n') -> not use_bound || n = n'

let exceed_bound n = function
  | None -> false
  | Some (use_bound,n') -> use_bound && n >= n'

  (* We delay thinning until the completion of the whole intros tactic
     to ensure that dependent hypotheses are cleared in the right
     dependency order (see BZ#1000); we use fresh names, not used in
     the tactic, for the hyps to clear *)
  (* In [intro_patterns_core b avoid ids thin destopt bound n tac patl]:
     [b]: compatibility flag, if false at toplevel, do not complete incomplete
          trailing toplevel or_and patterns (as in "intros []", see
          [bracketing_last_or_and_intro_pattern])
     [avoid]: names to avoid when creating an internal name
     [ids]: collect introduced names for possible use by the [tac] continuation
     [thin]: collect names to erase at the end
     [destopt]: position in the context where to introduce the hypotheses
     [bound]: number of pending intros to do in the current or-and pattern,
              with remembering of [b] flag if at toplevel
     [n]: number of introduction done in the current or-and pattern
     [tac]: continuation tactic
     [patl]: introduction patterns to interpret
  *)

let rec intro_patterns_core with_evars b avoid ids thin destopt bound n tac =
  function
  | [] when fit_bound n bound ->
      tac ids thin
  | [] ->
      (* Behave as IntroAnonymous *)
      intro_patterns_core with_evars b avoid ids thin destopt bound n tac
        [CAst.make @@ IntroNaming IntroAnonymous]
  | {CAst.loc;v=pat} :: l ->
  if exceed_bound n bound then error_unexpected_extra_pattern loc bound pat else
  match pat with
  | IntroForthcoming onlydeps ->
      intro_forthcoming_then_gen (NamingAvoid (Id.Set.union avoid (explicit_intro_names l)))
	  destopt onlydeps n bound
        (fun ids -> intro_patterns_core with_evars b avoid ids thin destopt bound
          (n+List.length ids) tac l)
  | IntroAction pat ->
      intro_then_gen (make_tmp_naming avoid l pat)
	destopt true false
        (intro_pattern_action ?loc with_evars (b || not (List.is_empty l)) false
          pat thin destopt
          (fun thin bound' -> intro_patterns_core with_evars b avoid ids thin destopt bound' 0
            (fun ids thin ->
              intro_patterns_core with_evars b avoid ids thin destopt bound (n+1) tac l)))
  | IntroNaming pat ->
      intro_pattern_naming loc with_evars b avoid ids pat thin destopt bound (n+1) tac l

  (* Pi-introduction rule, used backwards *)
and intro_pattern_naming loc with_evars b avoid ids pat thin destopt bound n tac l =
  match pat with
  | IntroIdentifier id ->
      check_thin_clash_then id thin avoid (fun thin ->
        intro_then_gen (NamingMustBe CAst.(make ?loc id)) destopt true false
          (fun id -> intro_patterns_core with_evars b avoid (id::ids) thin destopt bound n tac l))
  | IntroAnonymous ->
      intro_then_gen (NamingAvoid (Id.Set.union avoid (explicit_intro_names l)))
	destopt true false
        (fun id -> intro_patterns_core with_evars b avoid (id::ids) thin destopt bound n tac l)
  | IntroFresh id ->
      (* todo: avoid thinned names to interfere with generation of fresh name *)
      intro_then_gen (NamingBasedOn (id, Id.Set.union avoid (explicit_intro_names l)))
	destopt true false
        (fun id -> intro_patterns_core with_evars b avoid (id::ids) thin destopt bound n tac l)

and intro_pattern_action ?loc with_evars b style pat thin destopt tac id =
  match pat with
  | IntroWildcard ->
      tac (CAst.(make ?loc id)::thin) None []
  | IntroOrAndPattern ll ->
      intro_or_and_pattern ?loc with_evars b ll thin tac id
  | IntroInjection l' ->
      intro_decomp_eq ?loc l' thin tac id
  | IntroRewrite l2r ->
      rewrite_hyp_then style with_evars thin l2r id (fun thin -> tac thin None [])
  | IntroApplyOn ({CAst.loc=loc';v=f},{CAst.loc;v=pat}) ->
      let naming,tac_ipat =
        prepare_intros ?loc with_evars (IntroIdentifier id) destopt pat in
      let doclear =
        if naming = NamingMustBe (CAst.make ?loc id) then
          Proofview.tclUNIT () (* apply_in_once do a replacement *)
        else
          clear [id] in
      let f env sigma = let (sigma, c) = f env sigma in (sigma,(c, NoBindings))
      in
      apply_in_delayed_once false true true with_evars naming id (None,CAst.make ?loc:loc' f)
        (fun id -> Tacticals.New.tclTHENLIST [doclear; tac_ipat id; tac thin None []])

and prepare_intros ?loc with_evars dft destopt = function
  | IntroNaming ipat ->
      prepare_naming ?loc ipat,
      (fun id -> move_hyp id destopt)
  | IntroAction ipat ->
      prepare_naming ?loc dft,
      (let tac thin bound =
        intro_patterns_core with_evars true Id.Set.empty [] thin destopt bound 0
          (fun _ l -> clear_wildcards l) in
      fun id ->
        intro_pattern_action ?loc with_evars true true ipat [] destopt tac id)
  | IntroForthcoming _ -> user_err ?loc 
      (str "Introduction pattern for one hypothesis expected.")

let intro_patterns_head_core with_evars b destopt bound pat =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    check_name_unicity env [] [] pat;
    intro_patterns_core with_evars b Id.Set.empty [] [] destopt
      bound 0 (fun _ l -> clear_wildcards l) pat
  end

let intro_patterns_bound_to with_evars n destopt =
  intro_patterns_head_core with_evars true destopt
    (Some (true,n))

let intro_patterns_to with_evars destopt =
  intro_patterns_head_core with_evars (use_bracketing_last_or_and_intro_pattern ())
    destopt None

let intro_pattern_to with_evars destopt pat =
  intro_patterns_to with_evars destopt [CAst.make pat]

let intro_patterns with_evars = intro_patterns_to with_evars MoveLast

(* Implements "intros" *)
let intros_patterns with_evars = function
  | [] -> intros
  | l -> intro_patterns_to with_evars MoveLast l

(**************************)
(*   Forward reasoning    *)
(**************************)

let prepare_intros_opt with_evars dft destopt = function
  | None -> prepare_naming dft, (fun _id -> Proofview.tclUNIT ())
  | Some {CAst.loc;v=ipat} -> prepare_intros ?loc with_evars dft destopt ipat

let ipat_of_name = function
  | Anonymous -> None
  | Name id -> Some (CAst.make @@ IntroNaming (IntroIdentifier id))

let head_ident sigma c =
   let c = fst (decompose_app sigma (snd (decompose_lam_assum sigma c))) in
   if isVar sigma c then Some (destVar sigma c) else None

let assert_as first hd ipat t =
  let naming,tac = prepare_intros_opt false IntroAnonymous MoveLast ipat in
  let repl = do_replace hd naming in
  let tac = if repl then (fun id -> Proofview.tclUNIT ()) else tac in
  if first then assert_before_then_gen repl naming t tac
  else assert_after_then_gen repl naming t tac

(* apply in as *)

let general_apply_in ?(respect_opaque=false) sidecond_first with_delta
    with_destruct with_evars id lemmas ipat =
  let tac (naming,lemma) tac id =
    apply_in_delayed_once ~respect_opaque sidecond_first with_delta
      with_destruct with_evars naming id lemma tac in
  Proofview.Goal.enter begin fun gl ->
  let destopt =
    if with_evars then MoveLast (* evars would depend on the whole context *)
    else (
      let env, sigma = Proofview.Goal.(env gl, sigma gl) in
      get_previous_hyp_position env sigma id (Proofview.Goal.hyps gl)
    ) in
  let naming,ipat_tac =
    prepare_intros_opt with_evars (IntroIdentifier id) destopt ipat in
  let lemmas_target, last_lemma_target =
    let last,first = List.sep_last lemmas in
    List.map (fun lem -> (NamingMustBe (CAst.make id),lem)) first, (naming,last)
  in
  (* We chain apply_in_once, ending with an intro pattern *)
  List.fold_right tac lemmas_target (tac last_lemma_target ipat_tac) id
  end

(*
  if sidecond_first then
    (* Skip the side conditions of the applied lemma *)
    Tacticals.New.tclTHENLAST (tclMAPLAST tac lemmas_target) (ipat_tac id)
  else
    Tacticals.New.tclTHENFIRST (tclMAPFIRST tac lemmas_target) (ipat_tac id)
*)

let apply_in simple with_evars id lemmas ipat =
  let lemmas = List.map (fun (k,{CAst.loc;v=l}) -> k, CAst.make ?loc (fun _ sigma -> (sigma,l))) lemmas in
  general_apply_in false simple simple with_evars id lemmas ipat

let apply_delayed_in simple with_evars id lemmas ipat =
  general_apply_in ~respect_opaque:true false simple simple with_evars id lemmas ipat

(*****************************)
(* Tactics abstracting terms *)
(*****************************)

(* Implementation without generalisation: abbrev will be lost in hyps in *)
(* in the extracted proof *)

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
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let (sigma, t) = match ty with
    | Some t -> (sigma, t)
    | None ->
      let t = typ_of env sigma c in
      Evarsolve.refresh_universes ~onlyalg:true (Some false) env sigma t
    in
    let (sigma, (newcl, eq_tac)) = match with_eq with
      | Some (lr,{CAst.loc;v=ido}) ->
          let heq = match ido with
            | IntroAnonymous -> new_fresh_id (Id.Set.singleton id) (add_prefix "Heq" id) gl
            | IntroFresh heq_base -> new_fresh_id (Id.Set.singleton id) heq_base gl
            | IntroIdentifier id -> id in
          let eqdata = build_coq_eq_data () in
          let args = if lr then [t;mkVar id;c] else [t;c;mkVar id]in
          let (sigma, eq) = Evd.fresh_global env sigma eqdata.eq in
          let (sigma, refl) = Evd.fresh_global env sigma eqdata.refl in
          let eq = applist (eq,args) in
          let refl = applist (refl, [t;mkVar id]) in
	  let term = mkNamedLetIn id c t (mkLetIn (Name heq, refl, eq, ccl)) in
	  let sigma, _ = Typing.type_of env sigma term in
          let ans = term,
            Tacticals.New.tclTHENLIST
	      [
               intro_gen (NamingMustBe CAst.(make ?loc heq)) (decode_hyp lastlhyp) true false;
	      clear_body [heq;id]]
          in
          (sigma, ans)
      | None ->
          (sigma, (mkNamedLetIn id c t ccl, Proofview.tclUNIT ()))
    in
      Tacticals.New.tclTHENLIST
      [ Proofview.Unsafe.tclEVARS sigma;
        convert_concl_no_check newcl DEFAULTcast;
        intro_gen (NamingMustBe (CAst.make id)) (decode_hyp lastlhyp) true false;
        Tacticals.New.tclMAP convert_hyp_no_check depdecls;
        eq_tac ]
  end

let insert_before decls lasthyp env =
  match lasthyp with
  | None -> push_named_context decls env
  | Some id ->
  Environ.fold_named_context
    (fun _ d env ->
      let d = map_named_decl EConstr.of_constr d in
      let env = if Id.equal id (NamedDecl.get_id d) then push_named_context decls env else env in
      push_named d env)
    ~init:(reset_context env) env

let mk_eq_name env id {CAst.loc;v=ido} =
  match ido with
  | IntroAnonymous -> fresh_id_in_env (Id.Set.singleton id) (add_prefix "Heq" id) env
  | IntroFresh heq_base -> fresh_id_in_env (Id.Set.singleton id) heq_base env
  | IntroIdentifier id ->
    if List.mem id (ids_of_named_context (named_context env)) then
      user_err ?loc  (Id.print id ++ str" is already used.");
    id

(* unsafe *)

let mkletin_goal env sigma store with_eq dep (id,lastlhyp,ccl,c) ty =
  let open Context.Named.Declaration in
  let t = match ty with Some t -> t | _ -> typ_of env sigma c in
  let decl = if dep then LocalDef (id,c,t)
	     else LocalAssum (id,t)
  in
  match with_eq with
  | Some (lr,heq) ->
      let eqdata = build_coq_eq_data () in
      let args = if lr then [t;mkVar id;c] else [t;c;mkVar id]in
      let (sigma, eq) = Evd.fresh_global env sigma eqdata.eq in
      let (sigma, refl) = Evd.fresh_global env sigma eqdata.refl in
      let eq = applist (eq,args) in
      let refl = applist (refl, [t;mkVar id]) in
      let newenv = insert_before [LocalAssum (heq,eq); decl] lastlhyp env in
      let (sigma, x) = new_evar newenv sigma ~principal:true ~store ccl in
      (sigma, mkNamedLetIn id c t (mkNamedLetIn heq refl eq x))
  | None ->
      let newenv = insert_before [decl] lastlhyp env in
      let (sigma, x) = new_evar newenv sigma ~principal:true ~store ccl in
      (sigma, mkNamedLetIn id c t x)

let letin_tac with_eq id c ty occs =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let ccl = Proofview.Goal.concl gl in
    let abs = AbstractExact (id,c,ty,occs,true) in
    let (id,_,depdecls,lastlhyp,ccl,res) = make_abstraction env sigma ccl abs in
    (* We keep the original term to match but record the potential side-effects
       of unifying universes. *)
    let (sigma, c) = match res with
      | None -> (sigma, c)
      | Some (sigma, _) -> (sigma, c)
    in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (letin_tac_gen with_eq (id,depdecls,lastlhyp,ccl,c) ty)
  end

let letin_pat_tac with_evars with_eq id c occs =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let ccl = Proofview.Goal.concl gl in
    let check t = true in
    let abs = AbstractPattern (false,check,id,c,occs,false) in
    let (id,_,depdecls,lastlhyp,ccl,res) = make_abstraction env sigma ccl abs in
    let (sigma, c) = match res with
    | None -> finish_evar_resolution ~flags:(tactic_infer_flags with_evars) env sigma c
    | Some res -> res in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (letin_tac_gen with_eq (id,depdecls,lastlhyp,ccl,c) None)
  end

(* Tactics "pose proof" (usetac=None) and "assert"/"enough" (otherwise) *)
let forward b usetac ipat c =
  match usetac with
  | None ->
      Proofview.Goal.enter begin fun gl ->
      let t = Tacmach.New.pf_get_type_of gl c in
      let sigma = Tacmach.New.project gl in
      let hd = head_ident sigma c in
      Tacticals.New.tclTHENFIRST (assert_as true hd ipat t) (exact_no_check c)
      end
  | Some tac ->
      let tac = match tac with
        | None -> Tacticals.New.tclIDTAC
        | Some tac -> Tacticals.New.tclCOMPLETE tac in
      if b then
        Tacticals.New.tclTHENFIRST (assert_as b None ipat c) tac
      else
        Tacticals.New.tclTHENS3PARTS
          (assert_as b None ipat c) [||] tac [|Tacticals.New.tclIDTAC|]

let pose_proof na c = forward true None (ipat_of_name na) c
let assert_by na t tac = forward true (Some (Some tac)) (ipat_of_name na) t
let enough_by na t tac = forward false (Some (Some tac)) (ipat_of_name na) t

(***************************)
(*  Generalization tactics *)
(***************************)

(* Compute a name for a generalization *)

let generalized_name env sigma c t ids cl = function
  | Name id as na ->
      if Id.List.mem id ids then
	user_err  (Id.print id ++ str " is already used.");
      na
  | Anonymous ->
      match EConstr.kind sigma c with
      | Var id ->
	 (* Keep the name even if not occurring: may be used by intros later *)
	  Name id
      | _ ->
	  if noccurn sigma 1 cl then Anonymous else
	    (* On ne s'etait pas casse la tete : on avait pris pour nom de
               variable la premiere lettre du type, meme si "c" avait ete une
               constante dont on aurait pu prendre directement le nom *)
	    named_hd env sigma t Anonymous

(* Abstract over [c] in [forall x1:A1(c)..xi:Ai(c).T(c)] producing
   [forall x, x1:A1(x1), .., xi:Ai(x). T(x)] with all [c] abtracted in [Ai]
   but only those at [occs] in [T] *)

let generalize_goal_gen env sigma ids i ((occs,c,b),na) t cl =
  let open Context.Rel.Declaration in
  let decls,cl = decompose_prod_n_assum sigma i cl in
  let dummy_prod = it_mkProd_or_LetIn mkProp decls in
  let newdecls,_ = decompose_prod_n_assum sigma i (subst_term_gen sigma EConstr.eq_constr_nounivs c dummy_prod) in
  let cl',sigma' = subst_closed_term_occ env sigma (AtOccs occs) c (it_mkProd_or_LetIn cl newdecls) in
  let na = generalized_name env sigma c t ids cl' na in
  let decl = match b with
    | None -> LocalAssum (na,t)
    | Some b -> LocalDef (na,b,t)
  in
  mkProd_or_LetIn decl cl', sigma'

let generalize_goal gl i ((occs,c,b),na as o) (cl,sigma) =
  let open Tacmach.New in
  let env = pf_env gl in
  let ids = pf_ids_of_hyps gl in
  let sigma, t = Typing.type_of env sigma c in
  generalize_goal_gen env sigma ids i o t cl

let generalize_dep ?(with_let=false) c =
  let open Tacmach.New in
  let open Tacticals.New in
  Proofview.Goal.nf_enter begin fun gl ->
  let env = pf_env gl in
  let sign = Proofview.Goal.hyps gl in
  let sigma = project gl in
  let init_ids = ids_of_named_context (Global.named_context()) in
  let seek (d:named_declaration) (toquant:named_context) =
    if List.exists (fun d' -> occur_var_in_decl env sigma (NamedDecl.get_id d') d) toquant
      || dependent_in_decl sigma c d then
      d::toquant
    else
      toquant in
  let to_quantify = Context.Named.fold_outside seek sign ~init:[] in
  let to_quantify_rev = List.rev to_quantify in
  let qhyps = List.map NamedDecl.get_id to_quantify_rev in
  let tothin = List.filter (fun id -> not (Id.List.mem id init_ids)) qhyps in
  let tothin' =
    match EConstr.kind sigma c with
      | Var id when mem_named_context_val id (val_of_named_context sign) && not (Id.List.mem id init_ids)
	  -> id::tothin
      | _ -> tothin
  in
  let cl' = it_mkNamedProd_or_LetIn (pf_concl gl) to_quantify in
  let body =
    if with_let then
      match EConstr.kind sigma c with
      | Var id -> id |> (fun id -> pf_get_hyp id gl) |> NamedDecl.get_value
      | _ -> None
    else None
  in
  let cl'',evd = generalize_goal gl 0 ((AllOccurrences,c,body),Anonymous)
    (cl',project gl) in
  (** Check that the generalization is indeed well-typed *)
  let (evd, _) = Typing.type_of env evd cl'' in
  let args = Context.Named.to_instance mkVar to_quantify_rev in
  tclTHENLIST
    [ Proofview.Unsafe.tclEVARS evd;
      apply_type ~typecheck:false cl'' (if Option.is_empty body then c::args else args);
      clear (List.rev tothin')]
  end

(**  *)
let generalize_gen_let lconstr = Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let newcl, evd =
    List.fold_right_i (generalize_goal gl) 0 lconstr
      (Tacmach.New.pf_concl gl,Tacmach.New.project gl)
  in
  let (evd, _) = Typing.type_of env evd newcl in
  let map ((_, c, b),_) = if Option.is_empty b then Some c else None in
  Proofview.tclTHEN (Proofview.Unsafe.tclEVARS evd)
  (apply_type ~typecheck:false newcl (List.map_filter map lconstr))
end

let new_generalize_gen_let lconstr =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in
    let env = Proofview.Goal.env gl in
    let ids = Tacmach.New.pf_ids_of_hyps gl in
    let newcl, sigma, args =
      List.fold_right_i 
	(fun i ((_,c,b),_ as o) (cl, sigma, args) ->
	  let sigma, t = Typing.type_of env sigma c in
	  let args = if Option.is_empty b then c :: args else args in
          let cl, sigma = generalize_goal_gen env sigma ids i o t cl in
          (cl, sigma, args))
	0 lconstr (concl, sigma, [])
    in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
	(Refine.refine ~typecheck:false begin fun sigma ->
          let (sigma, ev) = Evarutil.new_evar env sigma ~principal:true newcl in
          (sigma, applist (ev, args))
	 end)
  end

let generalize_gen lconstr =
  generalize_gen_let (List.map (fun (occs_c,na) ->
    let (occs,c) = Redexpr.out_with_occurrences occs_c in
    (occs,c,None),na) lconstr)

let new_generalize_gen lconstr =
  new_generalize_gen_let (List.map (fun ((occs,c),na) ->
    (occs,c,None),na) lconstr)

let generalize l =
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

(* Modifying/Adding an hypothesis  *)

(* Instantiating some arguments (whatever their position) of an hypothesis
   or any term, leaving other arguments quantified. If operating on an
   hypothesis of the goal, the new hypothesis replaces it.

   (c,lbind) are supposed to be of the form
   ((t t1 t2 ... tm) , someBindings)

   in which case we pose a proof with body

   (fun y1...yp => H t1 t2 ... tm u1 ... uq) where yi are the
   remaining arguments of H that lbind could not resolve, ui are a mix
   of inferred args and yi. The overall effect is to remove from H as
   much quantification as possible given lbind. *)
let specialize (c,lbind) ipat =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let sigma, term =
    if lbind == NoBindings then
      sigma, c
    else
      let typ_of_c = Retyping.get_type_of env sigma c in
      (* If the term is lambda then we put a letin to put avoid
         interaction between the term and the bindings. *)
      let c = match EConstr.kind sigma c with
        | Lambda(_,_,_) ->
          mkLetIn(Name.Anonymous, c, typ_of_c, (mkRel 1))
        | _ -> c in
      let clause = make_clenv_binding env sigma (c,typ_of_c) lbind in
      let flags = { (default_unify_flags ()) with resolve_evars = true } in
      let clause = clenv_unify_meta_types ~flags clause in
      let sigma = clause.evd in
      let (thd,tstack) = whd_nored_stack sigma (clenv_value clause) in
      let c_hd , c_args = decompose_app sigma c in
      let liftrel x =
        match kind sigma x with
        | Rel n -> mkRel (n+1)
        | _ -> x in
      (* We grab names used in product to remember them at re-abstracting phase *)
      let typ_of_c_hd = pf_get_type_of gl c_hd in
      let lprod, concl = decompose_prod_assum sigma typ_of_c_hd in
      (* accumulator args: arguments to apply to c_hd: all infered
         args + re-abstracted rels *)
      let rec rebuild_lambdas sigma lprd args hd l =
        match lprd , l with
        | _, [] -> sigma,applist (hd, (List.map (nf_evar sigma) args))
        | Context.Rel.Declaration.LocalAssum(nme,_)::lp' , t::l' when occur_meta sigma t ->
          (* nme has not been resolved, let us re-abstract it. Same
             name but type updated by instanciation of other args. *)
          let sigma,new_typ_of_t = Typing.type_of clause.env sigma t in
          let liftedargs = List.map liftrel args in
          (* lifting rels in the accumulator args *)
          let sigma,hd' = rebuild_lambdas sigma lp' (liftedargs@[mkRel 1 ]) hd l' in
          (* replace meta variable by the abstracted variable *)
          let hd'' = subst_term sigma t hd' in
          (* lambda expansion *)
          sigma,mkLambda (nme,new_typ_of_t,hd'')
        | Context.Rel.Declaration.LocalAssum(_,_)::lp' , t::l' ->
          let sigma,hd' = rebuild_lambdas sigma lp' (args@[t]) hd l' in
          sigma,hd'
        | _ ,_ -> assert false in
      let sigma,hd = rebuild_lambdas sigma (List.rev lprod) [] c_hd tstack in
      Evd.clear_metas sigma, hd
  in
  let typ = Retyping.get_type_of env sigma term in
  let tac =
    match EConstr.kind sigma (fst(EConstr.decompose_app sigma (snd(EConstr.decompose_lam_assum sigma c)))) with
    | Var id when Id.List.mem id (Tacmach.New.pf_ids_of_hyps gl) ->
      (* Like assert (id:=id args) but with the concept of specialization *)
      let naming,tac =
        prepare_intros_opt false (IntroIdentifier id) MoveLast ipat in
      let repl = do_replace (Some id) naming in
      Tacticals.New.tclTHENFIRST
        (assert_before_then_gen repl naming typ tac)
	(exact_no_check term)
    | _ ->
      match ipat with
      | None ->
        (* Like generalize with extra support for "with" bindings *)
        (* even though the "with" bindings forces full application *)
        (* TODO: add intro to be more homogeneous. It will break
           scripts but will be easy to fix *)
         (Tacticals.New.tclTHENLAST (cut typ) (exact_no_check term))
      | Some {CAst.loc;v=ipat} ->
        (* Like pose proof with extra support for "with" bindings *)
        (* even though the "with" bindings forces full application *)
        let naming,tac = prepare_intros ?loc false IntroAnonymous MoveLast ipat in
        Tacticals.New.tclTHENFIRST
          (assert_before_then_gen false naming typ tac)
	  (exact_no_check term)
  in
  Tacticals.New.tclTHEN (Proofview.Unsafe.tclEVARS sigma) tac
  end

(*****************************)
(* Ad hoc unfold             *)
(*****************************)

(* The two following functions should already exist, but found nowhere *)
(* Unfolds x by its definition everywhere *)
let unfold_body x =
  let open Context.Named.Declaration in
  Proofview.Goal.enter begin fun gl ->
  (** We normalize the given hypothesis immediately. *)
  let env = Proofview.Goal.env gl in
  let xval = match Environ.lookup_named x env with
  | LocalAssum _ -> user_err ~hdr:"unfold_body"
    (Id.print x ++ str" is not a defined hypothesis.")
  | LocalDef (_,xval,_) -> xval
  in
  let xval = EConstr.of_constr xval in
  Tacticals.New.afterHyp x begin fun aft ->
  let hl = List.fold_right (fun decl cl -> (NamedDecl.get_id decl, InHyp) :: cl) aft [] in
  let rfun _ _ c = replace_vars [x, xval] c in
  let reducth h = reduct_in_hyp rfun h in
  let reductc = reduct_in_concl (rfun, DEFAULTcast) in
  Tacticals.New.tclTHENLIST [Tacticals.New.tclMAP reducth hl; reductc]
  end
  end

let warn_cannot_remove_as_expected =
  CWarnings.create ~name:"cannot-remove-as-expected" ~category:"tactics"
         (fun (id,inglobal) ->
           let pp = match inglobal with
             | None -> mt ()
             | Some ref -> str ", it is used implicitly in " ++ Printer.pr_global ref in
           str "Cannot remove " ++ Id.print id ++ pp ++ str ".")

let clear_for_destruct ids =
  Proofview.tclORELSE
    (clear_gen (fun env sigma id err inglobal -> raise (ClearDependencyError (id,err,inglobal))) ids)
    (function
     | ClearDependencyError (id,err,inglobal),_ -> warn_cannot_remove_as_expected (id,inglobal); Proofview.tclUNIT ()
     | e -> iraise e)

(* Either unfold and clear if defined or simply clear if not a definition *)
let expand_hyp id =
  Tacticals.New.tclTRY (unfold_body id) <*> clear_for_destruct [id]

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
  - clear those of [indvars] that are variables and [hyp0]
  - in the i-th subgoal, intro the arguments of the i-th constructor
    of the inductive type after [hyp0succ] (done in
    [induct_discharge]) let the induction hypotheses on top of the
    hyps because they may depend on variables between [hyp0] and the
    top. A counterpart is that the dep hyps programmed to be intro-ed
    on top must now be intro-ed after the induction hypotheses
  - move each of [dephyps] at the right place following the
    [statuslist]

 *)

let warn_unused_intro_pattern env sigma =
  CWarnings.create ~name:"unused-intro-pattern" ~category:"tactics"
    (fun names ->
       strbrk"Unused introduction " ++ str (String.plural (List.length names) "pattern") ++
       str": " ++ prlist_with_sep spc
         (Miscprint.pr_intro_pattern
            (fun c -> Printer.pr_econstr_env env sigma (snd (c env sigma)))) names)

let check_unused_names env sigma names =
  if not (List.is_empty names) then
    warn_unused_intro_pattern env sigma names

let intropattern_of_name gl avoid = function
  | Anonymous -> IntroNaming IntroAnonymous
  | Name id -> IntroNaming (IntroIdentifier (new_fresh_id avoid id gl))

let rec consume_pattern avoid na isdep gl = let open CAst in function
  | [] -> ((CAst.make @@ intropattern_of_name gl avoid na), [])
  | {loc;v=IntroForthcoming true}::names when not isdep ->
      consume_pattern avoid na isdep gl names
  | {loc;v=IntroForthcoming _}::names as fullpat ->
      let avoid = Id.Set.union avoid (explicit_intro_names names) in
      (CAst.make ?loc @@ intropattern_of_name gl avoid na, fullpat)
  | {loc;v=IntroNaming IntroAnonymous}::names ->
      let avoid = Id.Set.union avoid (explicit_intro_names names) in
      (CAst.make ?loc @@ intropattern_of_name gl avoid na, names)
  | {loc;v=IntroNaming (IntroFresh id')}::names ->
      let avoid = Id.Set.union avoid (explicit_intro_names names) in
      (CAst.make ?loc @@ IntroNaming (IntroIdentifier (new_fresh_id avoid id' gl)), names)
  | pat::names -> (pat,names)

let re_intro_dependent_hypotheses (lstatus,rstatus) (_,tophyp) =
  let tophyp = match tophyp with None -> MoveLast | Some hyp -> MoveAfter hyp in
  let newlstatus = (* if some IH has taken place at the top of hyps *)
    List.map (function (hyp,MoveLast) -> (hyp,tophyp) | x -> x) lstatus
  in
  Tacticals.New.tclTHEN
    (intros_move rstatus)
    (intros_move newlstatus)

let dest_intro_patterns with_evars avoid thin dest pat tac =
  intro_patterns_core with_evars true avoid [] thin dest None 0 tac pat

let safe_dest_intro_patterns with_evars avoid thin dest pat tac =
  Proofview.tclORELSE
    (dest_intro_patterns with_evars avoid thin dest pat tac)
    begin function (e, info) -> match e with
      | UserError (Some "move_hyp",_) ->
       (* May happen e.g. with "destruct x using s" with an hypothesis
          which is morally an induction hypothesis to be "MoveLast" if
          known as such but which is considered instead as a subterm of
          a constructor to be move at the place of x. *)
          dest_intro_patterns with_evars avoid thin MoveLast pat tac
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

let induct_discharge with_evars dests avoid' tac (avoid,ra) names =
  let avoid = Id.Set.union avoid avoid' in
  let rec peel_tac ra dests names thin =
    match ra with
    | (RecArg,_,deprec,recvarname) ::
        (IndArg,_,depind,hyprecname) :: ra' ->
        Proofview.Goal.enter begin fun gl ->
        let (recpat,names) = match names with
          | [{CAst.loc;v=IntroNaming (IntroIdentifier id)} as pat] ->
              let id' = next_ident_away (add_prefix "IH" id) avoid in
              (pat, [CAst.make @@ IntroNaming (IntroIdentifier id')])
          | _ -> consume_pattern avoid (Name recvarname) deprec gl names in
        let dest = get_recarg_dest dests in
        dest_intro_patterns with_evars avoid thin dest [recpat] (fun ids thin ->
        Proofview.Goal.enter begin fun gl ->
          let (hyprec,names) =
            consume_pattern avoid (Name hyprecname) depind gl names
          in
	  dest_intro_patterns with_evars avoid thin MoveLast [hyprec] (fun ids' thin ->
	    peel_tac ra' (update_dest dests ids') names thin)
                             end)
        end
    | (IndArg,_,dep,hyprecname) :: ra' ->
        Proofview.Goal.enter begin fun gl ->
	(* Rem: does not happen in Coq schemes, only in user-defined schemes *)
        let pat,names =
          consume_pattern avoid (Name hyprecname) dep gl names in
	dest_intro_patterns with_evars avoid thin MoveLast [pat] (fun ids thin ->
        peel_tac ra' (update_dest dests ids) names thin)
        end
    | (RecArg,_,dep,recvarname) :: ra' ->
        Proofview.Goal.enter begin fun gl ->
        let (pat,names) =
          consume_pattern avoid (Name recvarname) dep gl names in
        let dest = get_recarg_dest dests in
	dest_intro_patterns with_evars avoid thin dest [pat] (fun ids thin ->
        peel_tac ra' dests names thin)
        end
    | (OtherArg,_,dep,_) :: ra' ->
        Proofview.Goal.enter begin fun gl ->
        let (pat,names) = consume_pattern avoid Anonymous dep gl names in
        let dest = get_recarg_dest dests in
	safe_dest_intro_patterns with_evars avoid thin dest [pat] (fun ids thin ->
        peel_tac ra' dests names thin)
        end
    | [] ->
        Proofview.Goal.enter begin fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        check_unused_names env sigma names;
        Tacticals.New.tclTHEN (clear_wildcards thin) (tac dests)
        end
  in
  peel_tac ra dests names []

(* - le recalcul de indtyp à chaque itération de atomize_one est pour ne pas
     s'embêter à regarder si un letin_tac ne fait pas des
     substitutions aussi sur l'argument voisin *)

let expand_projections env sigma c =
  let rec aux env c =
    match EConstr.kind sigma c with
    | Proj (p, c) -> Retyping.expand_projection env sigma p (aux env c) []
    | _ -> map_constr_with_full_binders sigma push_rel aux env c
  in
  aux env c
			       
	   
(* Marche pas... faut prendre en compte l'occurrence précise... *)

let atomize_param_of_ind_then (indref,nparams,_) hyp0 tac =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.New.project gl in
  let tmptyp0 = Tacmach.New.pf_get_hyp_typ hyp0 gl in
  let reduce_to_quantified_ref = Tacmach.New.pf_apply reduce_to_quantified_ref gl in
  let typ0 = reduce_to_quantified_ref indref tmptyp0 in
  let prods, indtyp = decompose_prod_assum sigma typ0 in
  let hd,argl = decompose_app sigma indtyp in
  let env' = push_rel_context prods env in
  let params = List.firstn nparams argl in
  let params' = List.map (expand_projections env' sigma) params in
  (* le gl est important pour ne pas préévaluer *)
  let rec atomize_one i args args' avoid =
    if Int.equal i nparams then
      let t = applist (hd, params@args) in
      Tacticals.New.tclTHEN
        (change_in_hyp None (make_change_arg t) (hyp0,InHypTypeOnly))
        (tac avoid)
    else
      let c = List.nth argl (i-1) in
      match EConstr.kind sigma c with
	| Var id when not (List.exists (fun c -> occur_var env sigma id c) args') &&
                      not (List.exists (fun c -> occur_var env sigma id c) params') ->
            (* Based on the knowledge given by the user, all
               constraints on the variable are generalizable in the
               current environment so that it is clearable after destruction *)
	    atomize_one (i-1) (c::args) (c::args') (Id.Set.add id avoid)
	| _ ->
	   let c' = expand_projections env' sigma c in
            let dependent t = dependent sigma c t in
            if List.exists dependent params' ||
               List.exists dependent args'
            then
              (* This is a case where the argument is constrained in a
                 way which would require some kind of inversion; we
                 follow the (old) discipline of not generalizing over
                 this term, since we don't try to invert the
                 constraint anyway. *)
	      atomize_one (i-1) (c::args) (c'::args') avoid
            else
            (* We reason blindly on the term and do as if it were
               generalizable, ignoring the constraints coming from
               its structure *)
            let id = match EConstr.kind sigma c with
            | Var id -> id
            | _ ->
            let type_of = Tacmach.New.pf_unsafe_type_of gl in
            id_of_name_using_hdchar env sigma (type_of c) Anonymous in
            let x = fresh_id_in_env avoid id env in
	    Tacticals.New.tclTHEN
	      (letin_tac None (Name x) c None allHypsAndConcl)
	      (atomize_one (i-1) (mkVar x::args) (mkVar x::args') (Id.Set.add x avoid))
  in
  atomize_one (List.length argl) [] [] Id.Set.empty
  end

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

let cook_sign hyp0_opt inhyps indvars env sigma =
  (* First phase from L to R: get [toclear], [decldep] and [statuslist]
     for the hypotheses before (= more ancient than) hyp0 (see above) *)
  let toclear = ref [] in
  let avoid = ref Id.Set.empty in
  let decldeps = ref [] in
  let ldeps = ref [] in
  let rstatus = ref [] in
  let lstatus = ref [] in
  let before = ref true in
  let maindep = ref false in
  let seek_deps env decl rhyp =
    let decl = map_named_decl EConstr.of_constr decl in
    let hyp = NamedDecl.get_id decl in
    if (match hyp0_opt with Some hyp0 -> Id.equal hyp hyp0 | _ -> false)
    then begin
      before:=false;
      (* Note that if there was no main induction hypotheses, then hyp
         is one of indvars too *)
      toclear := hyp::!toclear;
      MoveFirst (* fake value *)
    end else if Id.Set.mem hyp indvars then begin
      (* The variables in indvars are such that they don't occur any
         more after generalization, so declare them to clear. *)
      toclear := hyp::!toclear;
      rhyp
    end else
      let dephyp0 = List.is_empty inhyps && 
	(Option.cata (fun id -> occur_var_in_decl env sigma id decl) false hyp0_opt)
      in
      let depother = List.is_empty inhyps &&
	(Id.Set.exists (fun id -> occur_var_in_decl env sigma id decl) indvars ||
         List.exists (fun decl' -> occur_var_in_decl env sigma (NamedDecl.get_id decl') decl) !decldeps)
      in
      if not (List.is_empty inhyps) && Id.List.mem hyp inhyps
         || dephyp0 || depother
      then begin
	decldeps := decl::!decldeps;
	avoid := Id.Set.add hyp !avoid;
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
  let compute_lstatus lhyp decl =
    let hyp = NamedDecl.get_id decl in
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
  indref: GlobRef.t option;
  params: rel_context;      (* (prm1,tprm1);(prm2,tprm2)...(prmp,tprmp) *)
  nparams: int;               (* number of parameters *)
  predicates: rel_context;  (* (Qq, (Tq_1 -> Tq_2 ->...-> Tq_nq)), (Q1,...) *)
  npredicates: int;           (* Number of predicates *)
  branches: rel_context;    (* branchr,...,branch1 *)
  nbranches: int;             (* Number of branches *)
  args: rel_context;        (* (xni, Ti_ni) ... (x1, Ti_1) *)
  nargs: int;                 (* number of arguments *)
  indarg: rel_declaration option; (* Some (H,I prm1..prmp x1...xni)
                                               if HI is in premisses, None otherwise *)
  concl: types;               (* Qi x1...xni HI (f...), HI and (f...)
			         are optional and mutually exclusive *)
  indarg_in_concl: bool;      (* true if HI appears at the end of conclusion *)
  farg_in_concl: bool;        (* true if (f...) appears at the end of conclusion *)
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
    if Int.equal n 1 (* Only one recursive argument *) || Int.equal n 0 then Id.Set.empty
    else
      (* Forbid to use cname, cname0, hyprecname and hyprecname0 *)
      (* in order to get names such as f1, f2, ... *)
      let avoid =
        Id.Set.add (make_ident (Id.to_string hyprecname) None)
        (Id.Set.singleton (make_ident (Id.to_string hyprecname) (Some 0))) in
      if not (String.equal (atompart_of_id cname) "H") then
        Id.Set.add (make_ident base (Some 0)) (Id.Set.add (make_ident base None) avoid)
      else avoid in
  Id.of_string base, hyprecname, avoid

let error_ind_scheme s =
  let s = if not (String.is_empty s) then s^" " else s in
  user_err ~hdr:"Tactics" (str "Cannot recognize " ++ str s ++ str "an induction scheme.")

let coq_eq sigma       = Evarutil.new_global sigma (Coqlib.build_coq_eq ())
let coq_eq_refl sigma  = Evarutil.new_global sigma (Coqlib.build_coq_eq_refl ())

let coq_heq_ref        = lazy (Coqlib.coq_reference"mkHEq" ["Logic";"JMeq"] "JMeq")
let coq_heq sigma      = Evarutil.new_global sigma (Lazy.force coq_heq_ref)
let coq_heq_refl sigma = Evarutil.new_global sigma (Coqlib.coq_reference "mkHEq" ["Logic";"JMeq"] "JMeq_refl")

let mkEq sigma t x y =
  let sigma, eq = coq_eq sigma in
  sigma, mkApp (eq, [| t; x; y |])

let mkRefl sigma t x =
  let sigma, refl = coq_eq_refl sigma in
  sigma, mkApp (refl, [| t; x |])

let mkHEq sigma t x u y =
  let sigma, c = coq_heq sigma in
  sigma, mkApp (c,[| t; x; u; y |])

let mkHRefl sigma t x =
  let sigma, c = coq_heq_refl sigma in
  sigma, mkApp (c, [| t; x |])

let lift_togethern n l =
  let l', _ =
    List.fold_right
      (fun x (acc, n) ->
	(lift n x :: acc, succ n))
      l ([], n)
  in l'

let lift_list l = List.map (lift 1) l

let ids_of_constr sigma ?(all=false) vars c =
  let rec aux vars c =
    match EConstr.kind sigma c with
    | Var id -> Id.Set.add id vars
    | App (f, args) ->
	(match EConstr.kind sigma f with
	| Construct ((ind,_),_)
	| Ind (ind,_) ->
            let (mib,mip) = Global.lookup_inductive ind in
	      Array.fold_left_from
		(if all then 0 else mib.Declarations.mind_nparams)
		aux vars args
	| _ -> EConstr.fold sigma aux vars c)
    | _ -> EConstr.fold sigma aux vars c
  in aux vars c

let decompose_indapp sigma f args =
  match EConstr.kind sigma f with
  | Construct ((ind,_),_)
  | Ind (ind,_) ->
      let (mib,mip) = Global.lookup_inductive ind in
      let first = mib.Declarations.mind_nparams_rec in
      let pars, args = Array.chop first args in
	mkApp (f, pars), args
  | _ -> f, args

let mk_term_eq homogeneous env sigma ty t ty' t' =
  if homogeneous then
    let sigma, eq = mkEq sigma ty t t' in
    let sigma, refl = mkRefl sigma ty' t' in
    sigma, (eq, refl)
  else
    let sigma, heq = mkHEq sigma ty t ty' t' in
    let sigma, hrefl = mkHRefl sigma ty' t' in
    sigma, (heq, hrefl)

let make_abstract_generalize env id typ concl dep ctx body c eqs args refls =
  let open Context.Rel.Declaration in
  Refine.refine ~typecheck:false begin fun sigma ->
  let eqslen = List.length eqs in
    (* Abstract by the "generalized" hypothesis equality proof if necessary. *)
  let sigma, abshypeq, abshypt =
    if dep then
      let ty = lift 1 c in
      let homogeneous = Reductionops.is_conv env sigma ty typ in
      let sigma, (eq, refl) =
        mk_term_eq homogeneous (push_rel_context ctx env) sigma ty (mkRel 1) typ (mkVar id) in
      sigma, mkProd (Anonymous, eq, lift 1 concl), [| refl |]
    else sigma, concl, [||]
  in
    (* Abstract by equalities *)
  let eqs = lift_togethern 1 eqs in (* lift together and past genarg *)
  let abseqs = it_mkProd_or_LetIn (lift eqslen abshypeq) (List.map (fun x -> LocalAssum (Anonymous, x)) eqs) in
  let decl = match body with
    | None -> LocalAssum (Name id, c)
    | Some body -> LocalDef (Name id, body, c)
  in
    (* Abstract by the "generalized" hypothesis. *)
  let genarg = mkProd_or_LetIn decl abseqs in
    (* Abstract by the extension of the context *)
  let genctyp = it_mkProd_or_LetIn genarg ctx in
    (* The goal will become this product. *)
  let (sigma, genc) = Evarutil.new_evar env sigma ~principal:true genctyp in
    (* Apply the old arguments giving the proper instantiation of the hyp *)
  let instc = mkApp (genc, Array.of_list args) in
    (* Then apply to the original instantiated hyp. *)
  let instc = Option.cata (fun _ -> instc) (mkApp (instc, [| mkVar id |])) body in
    (* Apply the reflexivity proofs on the indices. *)
  let appeqs = mkApp (instc, Array.of_list refls) in
    (* Finally, apply the reflexivity proof for the original hyp, to get a term of type gl again. *)
  (sigma, mkApp (appeqs, abshypt))
  end

let hyps_of_vars env sigma sign nogen hyps =
  if Id.Set.is_empty hyps then []
  else
    let (_,lh) =
      Context.Named.fold_inside
        (fun (hs,hl) d ->
          let x = NamedDecl.get_id d in
	  if Id.Set.mem x nogen then (hs,hl)
	  else if Id.Set.mem x hs then (hs,x::hl)
	  else
	    let xvars = global_vars_set_of_decl env sigma d in
	      if not (Id.Set.is_empty (Id.Set.diff xvars hs)) then
		(Id.Set.add x hs, x :: hl)
	      else (hs, hl))
        ~init:(hyps,[])
        sign
    in lh

exception Seen

let linear sigma vars args =
  let seen = ref vars in
    try
      Array.iter (fun i ->
	let rels = ids_of_constr sigma ~all:true Id.Set.empty i in
	let seen' =
	  Id.Set.fold (fun id acc ->
	    if Id.Set.mem id acc then raise Seen
	    else Id.Set.add id acc)
	    rels !seen
	in seen := seen')
	args;
      true
    with Seen -> false

let is_defined_variable env id =
  env |> lookup_named id |> is_local_def

let abstract_args gl generalize_vars dep id defined f args =
  let open Tacmach.New in
  let open Context.Rel.Declaration in
  let sigma = ref (Tacmach.New.project gl) in
  let env = Tacmach.New.pf_env gl in
  let concl = Tacmach.New.pf_concl gl in
  let dep = dep || local_occur_var !sigma id concl in
  let avoid = ref Id.Set.empty in
  let get_id name =
    let id = new_fresh_id !avoid (match name with Name n -> n | Anonymous -> Id.of_string "gen_x") gl in
      avoid := Id.Set.add id !avoid; id
  in
    (* Build application generalized w.r.t. the argument plus the necessary eqs.
       From env |- c : forall G, T and args : G we build
       (T[G'], G' : ctx, env ; G' |- args' : G, eqs := G'_i = G_i, refls : G' = G, vars to generalize)

       eqs are not lifted w.r.t. each other yet. (* will be needed when going to dependent indexes *)
    *)
  let aux (prod, ctx, ctxenv, c, args, eqs, refls, nongenvars, vars, env) arg =
    let name, ty, arity =
      let rel, c = Reductionops.splay_prod_n env !sigma 1 prod in
      let decl = List.hd rel in
      RelDecl.get_name decl, RelDecl.get_type decl, c
    in
    let argty = Tacmach.New.pf_unsafe_type_of gl arg in
    let sigma', ty = Evarsolve.refresh_universes (Some true) env !sigma ty in
    let () = sigma := sigma' in
    let lenctx = List.length ctx in
    let liftargty = lift lenctx argty in
    let leq = constr_cmp !sigma Reduction.CUMUL liftargty ty in
      match EConstr.kind !sigma arg with
      | Var id when not (is_defined_variable env id) && leq && not (Id.Set.mem id nongenvars) ->
      	  (subst1 arg arity, ctx, ctxenv, mkApp (c, [|arg|]), args, eqs, refls,
      	  Id.Set.add id nongenvars, Id.Set.remove id vars, env)
      | _ ->
	  let name = get_id name in
	  let decl = LocalAssum (Name name, ty) in
	  let ctx = decl :: ctx in
	  let c' = mkApp (lift 1 c, [|mkRel 1|]) in
	  let args = arg :: args in
	  let liftarg = lift (List.length ctx) arg in
	  let eq, refl =
	    if leq then
	      let sigma', eq = mkEq !sigma (lift 1 ty) (mkRel 1) liftarg in
              let sigma', refl = mkRefl sigma' (lift (-lenctx) ty) arg in
              sigma := sigma'; eq, refl
	    else
	      let sigma', eq = mkHEq !sigma (lift 1 ty) (mkRel 1) liftargty liftarg in
              let sigma', refl = mkHRefl sigma' argty arg in
              sigma := sigma'; eq, refl
	  in
	  let eqs = eq :: lift_list eqs in
	  let refls = refl :: refls in
	  let argvars = ids_of_constr !sigma vars arg in
	    (arity, ctx, push_rel decl ctxenv, c', args, eqs, refls,
	    nongenvars, Id.Set.union argvars vars, env)
  in
  let f', args' = decompose_indapp !sigma f args in
  let dogen, f', args' =
    let parvars = ids_of_constr !sigma ~all:true Id.Set.empty f' in
      if not (linear !sigma parvars args') then true, f, args
      else
	match Array.findi (fun i x -> not (isVar !sigma x) || is_defined_variable env (destVar !sigma x)) args' with
	| None -> false, f', args'
	| Some nonvar ->
	    let before, after = Array.chop nonvar args' in
	      true, mkApp (f', before), after
  in
    if dogen then
      let tyf' = Tacmach.New.pf_unsafe_type_of gl f' in
      let arity, ctx, ctxenv, c', args, eqs, refls, nogen, vars, env =
	Array.fold_left aux (tyf',[],env,f',[],[],[],Id.Set.empty,Id.Set.empty,env) args'
      in
      let args, refls = List.rev args, List.rev refls in
      let vars =
	if generalize_vars then
	  let nogen = Id.Set.add id nogen in
	    hyps_of_vars (pf_env gl) (project gl) (Proofview.Goal.hyps gl) nogen vars
	else []
      in
      let body, c' =
	if defined then Some c', Retyping.get_type_of ctxenv !sigma c'
	else None, c'
      in
      let typ = Tacmach.New.pf_get_hyp_typ id gl in
      let tac = make_abstract_generalize (pf_env gl) id typ concl dep ctx body c' eqs args refls in
      let tac = Proofview.Unsafe.tclEVARS !sigma <*> tac in
	Some (tac, dep, succ (List.length ctx), vars)
    else None

let abstract_generalize ?(generalize_vars=true) ?(force_dep=false) id =
  let open Context.Named.Declaration in
  Proofview.Goal.enter begin fun gl ->
  Coqlib.check_required_library Coqlib.jmeq_module_name;
  let sigma = Tacmach.New.project gl in
  let (f, args, def, id, oldid) =
    let oldid = Tacmach.New.pf_get_new_id id gl in
      match Tacmach.New.pf_get_hyp id gl with
      | LocalAssum (_,t) -> let f, args = decompose_app sigma t in
	        (f, args, false, id, oldid)
      | LocalDef (_,t,_) ->
	  let f, args = decompose_app sigma t in
	  (f, args, true, id, oldid)
  in
  if List.is_empty args then Proofview.tclUNIT ()
  else
    let args = Array.of_list args in
    let newc = abstract_args gl generalize_vars force_dep id def f args in
      match newc with
      | None -> Proofview.tclUNIT ()
      | Some (tac, dep, n, vars) ->
	  let tac =
	    if dep then
              Tacticals.New.tclTHENLIST [
                tac;
		 rename_hyp [(id, oldid)]; Tacticals.New.tclDO n intro;
		 generalize_dep ~with_let:true (mkVar oldid)]
            else Tacticals.New.tclTHENLIST [
                    tac;
		    clear [id];
		    Tacticals.New.tclDO n intro]
	  in
	    if List.is_empty vars then tac
	    else Tacticals.New.tclTHEN tac
              (Tacticals.New.tclFIRST
                [revert vars ;
		 Tacticals.New.tclMAP (fun id ->
		      Tacticals.New.tclTRY (generalize_dep ~with_let:true (mkVar id))) vars])
  end

let compare_upto_variables sigma x y =
  let rec compare x y =
    if (isVar sigma x || isRel sigma x) && (isVar sigma y || isRel sigma y) then true
    else compare_constr sigma compare x y
  in
  compare x y

let specialize_eqs id =
  let open Context.Rel.Declaration in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let ty = Tacmach.New.pf_get_hyp_typ id gl in
  let evars = ref (Proofview.Goal.sigma gl) in
  let unif env evars c1 c2 =
    compare_upto_variables !evars c1 c2 &&
    (match Evarconv.conv env !evars c1 c2 with
     | Some sigma -> evars := sigma; true
     | None -> false)
  in
  let rec aux in_eqs ctx acc ty =
    match EConstr.kind !evars ty with
    | Prod (na, t, b) ->
	(match EConstr.kind !evars t with
	| App (eq, [| eqty; x; y |]) when EConstr.is_global !evars (Lazy.force coq_eq_ref) eq ->
	    let c = if noccur_between !evars 1 (List.length ctx) x then y else x in
	    let pt = mkApp (eq, [| eqty; c; c |]) in
            let ind = destInd !evars eq in
	    let p = mkApp (mkConstructUi (ind,0), [| eqty; c |]) in
	      if unif (push_rel_context ctx env) evars pt t then
		aux true ctx (mkApp (acc, [| p |])) (subst1 p b)
	      else acc, in_eqs, ctx, ty
	| App (heq, [| eqty; x; eqty'; y |]) when EConstr.is_global !evars (Lazy.force coq_heq_ref) heq ->
	    let eqt, c = if noccur_between !evars 1 (List.length ctx) x then eqty', y else eqty, x in
	    let pt = mkApp (heq, [| eqt; c; eqt; c |]) in
            let ind = destInd !evars heq in
	    let p = mkApp (mkConstructUi (ind,0), [| eqt; c |]) in
	      if unif (push_rel_context ctx env) evars pt t then
		aux true ctx (mkApp (acc, [| p |])) (subst1 p b)
	      else acc, in_eqs, ctx, ty
	| _ ->
	    if in_eqs then acc, in_eqs, ctx, ty
	    else
              let sigma, e = Evarutil.new_evar (push_rel_context ctx env) !evars t in
              evars := sigma;
		aux false (LocalDef (na,e,t) :: ctx) (mkApp (lift 1 acc, [| mkRel 1 |])) b)
    | t -> acc, in_eqs, ctx, ty
  in
  let acc, worked, ctx, ty = aux false [] (mkVar id) ty in
  let ctx' = nf_rel_context_evar !evars ctx in
  let ctx'' = List.map (function
    | LocalDef (n,k,t) when isEvar !evars k -> LocalAssum (n,t)
    | decl -> decl) ctx'
  in
  let ty' = it_mkProd_or_LetIn ty ctx'' in
  let acc' = it_mkLambda_or_LetIn acc ctx'' in
  let ty' = Tacred.whd_simpl env !evars ty'
  and acc' = Tacred.whd_simpl env !evars acc' in
  let ty' = Evarutil.nf_evar !evars ty' in
    if worked then
      Tacticals.New.tclTHENFIRST
        (internal_cut true id ty')
	(exact_no_check ((* refresh_universes_strict *) acc'))
    else
      Tacticals.New.tclFAIL 0 (str "Nothing to do in hypothesis " ++ Id.print id)
  end

let specialize_eqs id = Proofview.Goal.enter begin fun gl ->
  let msg = str "Specialization not allowed on dependent hypotheses" in
  Proofview.tclOR (clear [id])
    (fun _ -> Tacticals.New.tclZEROMSG msg) >>= fun () ->
    specialize_eqs id
end

let occur_rel sigma n c =
  let res = not (noccurn sigma n c) in
  res

(* This function splits the products of the induction scheme [elimt] into four
   parts:
   - branches, easily detectable (they are not referred by rels in the subterm)
   - what was found before branches (acc1) that is: parameters and predicates
   - what was found after branches (acc3) that is: args and indarg if any
   if there is no branch, we try to fill in acc3 with args/indargs.
   We also return the conclusion.
*)
let decompose_paramspred_branch_args sigma elimt =
  let open Context.Rel.Declaration in
  let rec cut_noccur elimt acc2 =
    match EConstr.kind sigma elimt with
      | Prod(nme,tpe,elimt') ->
	  let hd_tpe,_ = decompose_app sigma (snd (decompose_prod_assum sigma tpe)) in
	  if not (occur_rel sigma 1 elimt') && isRel sigma hd_tpe
	  then cut_noccur elimt' (LocalAssum (nme,tpe)::acc2)
	  else let acc3,ccl = decompose_prod_assum sigma elimt in acc2 , acc3 , ccl
      | App(_, _) | Rel _ -> acc2 , [] , elimt
      | _ -> error_ind_scheme "" in
  let rec cut_occur elimt acc1 =
    match EConstr.kind sigma elimt with
      | Prod(nme,tpe,c) when occur_rel sigma 1 c -> cut_occur c (LocalAssum (nme,tpe)::acc1)
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
    let hyps,ccl = decompose_prod_assum sigma elimt in
    let hd_ccl_pred,_ = decompose_app sigma ccl in
    begin match EConstr.kind sigma hd_ccl_pred with
      | Rel i  -> let acc3,acc1 = List.chop (i-1) hyps in acc1 , [] , acc3 , ccl
      | _ -> error_ind_scheme ""
    end
  | _ -> acc1, acc2 , acc3, ccl


let exchange_hd_app sigma subst_hd t =
  let hd,args= decompose_app sigma t in mkApp (subst_hd,Array.of_list args)

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
let compute_elim_sig sigma ?elimc elimt =
  let open Context.Rel.Declaration in
  let params_preds,branches,args_indargs,conclusion =
    decompose_paramspred_branch_args sigma elimt in

  let ccl = exchange_hd_app sigma (mkVar (Id.of_string "__QI_DUMMY__")) conclusion in
  let concl_with_args = it_mkProd_or_LetIn ccl args_indargs in
  let nparams = Int.Set.cardinal (free_rels sigma concl_with_args) in
  let preds,params = List.chop (List.length params_preds - nparams) params_preds in

  (* A first approximation, further analysis will tweak it *)
  let res = ref { empty_scheme with
    (* This fields are ok: *)
    elimc = elimc; elimt = elimt; concl = conclusion;
    predicates = preds; npredicates = List.length preds;
    branches = branches; nbranches = List.length branches;
    farg_in_concl = isApp sigma ccl && isApp sigma (last_arg sigma ccl);
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
	| LocalDef (hiname,_,hi) -> error_ind_scheme ""
	| LocalAssum (hiname,hi) ->
	    let hi_ind, hi_args = decompose_app sigma hi in
	    let hi_is_ind = (* hi est d'un type globalisable *)
	      match EConstr.kind sigma hi_ind with
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
		indarg_in_concl = occur_rel sigma 1 ccl;
		args = List.tl !res.args; nargs = !res.nargs - 1;
	      };
	    raise Exit);
    raise Exit(* exit anyway *)
  with Exit -> (* Ending by computing indref: *)
    match !res.indarg with
      | None -> !res (* No indref *)
      | Some (LocalDef _) -> error_ind_scheme ""
      | Some (LocalAssum (_,ind)) ->
	  let indhd,indargs = decompose_app sigma ind in
	  try {!res with indref = Some (fst (Termops.global_of_constr sigma indhd)) }
	  with e when CErrors.noncritical e ->
            error "Cannot find the inductive type of the inductive scheme."

let compute_scheme_signature evd scheme names_info ind_type_guess =
  let open Context.Rel.Declaration in
  let f,l = decompose_app evd scheme.concl in
  (* Vérifier que les arguments de Qi sont bien les xi. *)
  let cond, check_concl =
    match scheme.indarg with
      | Some (LocalDef _) ->
	  error "Strange letin, cannot recognize an induction scheme."
      | None -> (* Non standard scheme *)
	  let cond hd = EConstr.eq_constr evd hd ind_type_guess && not scheme.farg_in_concl
	  in (cond, fun _ _ -> ())
      | Some (LocalAssum (_,ind)) -> (* Standard scheme from an inductive type *)
	  let indhd,indargs = decompose_app evd ind in
	  let cond hd = EConstr.eq_constr evd hd indhd in
	  let check_concl is_pred p =
	    (* Check again conclusion *)
	    let ccl_arg_ok = is_pred (p + scheme.nargs + 1) f == IndArg in
	    let ind_is_ok =
	      List.equal (fun c1 c2 -> EConstr.eq_constr evd c1 c2)
		(List.lastn scheme.nargs indargs)
		(Context.Rel.to_extended_list mkRel 0 scheme.args) in
	    if not (ccl_arg_ok && ind_is_ok) then
	      error_ind_scheme "the conclusion of"
	  in (cond, check_concl)
  in
  let is_pred n c =
    let hd = fst (decompose_app evd c) in
    match EConstr.kind evd hd with
      | Rel q when n < q && q <= n+scheme.npredicates -> IndArg
      | _ when cond hd -> RecArg
      | _ -> OtherArg
  in
  let rec check_branch p c =
    match EConstr.kind evd c with
      | Prod (_,t,c) ->
	(is_pred p t, true, not (Vars.noccurn evd 1 c)) :: check_branch (p+1) c
      | LetIn (_,_,_,c) ->
	(OtherArg, false, not (Vars.noccurn evd 1 c)) :: check_branch (p+1) c
      | _ when is_pred p c == IndArg -> []
      | _ -> raise Exit
  in
  let rec find_branches p lbrch =
    match lbrch with
      | LocalAssum (_,t) :: brs ->
	(try
	   let lchck_brch = check_branch p t in
	   let n = List.fold_left
	     (fun n (b,_,_) -> if b == RecArg then n+1 else n) 0 lchck_brch in
	   let recvarname, hyprecname, avoid =
	     make_up_names n scheme.indref names_info in
	   let namesign =
	     List.map (fun (b,is_assum,dep) ->
	       (b,is_assum,dep,if b == IndArg then hyprecname else recvarname))
	       lchck_brch in
	   (avoid,namesign) :: find_branches (p+1) brs
	 with Exit-> error_ind_scheme "the branches of")
      | LocalDef _ :: _ -> error_ind_scheme "the branches of"
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
  let scheme = compute_elim_sig evd ~elimc:elimc elimt in
    evd, (compute_scheme_signature evd scheme names_info ind_type_guess, scheme)

let guess_elim isrec dep s hyp0 gl =
  let tmptyp0 =	Tacmach.New.pf_get_hyp_typ hyp0 gl in
  let (mind, u), _ = Tacmach.New.pf_reduce_to_quantified_ind gl tmptyp0 in
  let evd, elimc =
    if isrec && not (is_nonrec mind) then find_ind_eliminator mind s gl
    else
      let env = Tacmach.New.pf_env gl in
      let sigma = Tacmach.New.project gl in
      let u = EInstance.kind (Tacmach.New.project gl) u in
      if dep then
        let (sigma, ind) = build_case_analysis_scheme env sigma (mind, u) true s in
        let ind = EConstr.of_constr ind in
        (sigma, ind)
      else
        let (sigma, ind) = build_case_analysis_scheme_default env sigma (mind, u) s in
        let ind = EConstr.of_constr ind in
        (sigma, ind)
  in
  let elimt = Tacmach.New.pf_unsafe_type_of gl elimc in
    evd, ((elimc, NoBindings), elimt), mkIndU (mind, u)

let given_elim hyp0 (elimc,lbind as e) gl =
  let sigma = Tacmach.New.project gl in
  let tmptyp0 = Tacmach.New.pf_get_hyp_typ hyp0 gl in
  let ind_type_guess,_ = decompose_app sigma (snd (decompose_prod sigma tmptyp0)) in
  let elimt = Tacmach.New.pf_unsafe_type_of gl elimc in
  Tacmach.New.project gl, (e, elimt), ind_type_guess

type scheme_signature =
    (Id.Set.t * (elim_arg_kind * bool * bool * Id.t) list) array

type eliminator_source =
  | ElimUsing of (eliminator * EConstr.types) * scheme_signature
  | ElimOver of bool * Id.t

let find_induction_type isrec elim hyp0 gl =
  let sigma = Tacmach.New.project gl in
  let scheme,elim =
    match elim with
    | None ->
       let sort = Tacticals.New.elimination_sort_of_goal gl in
       let _, (elimc,elimt),_ = guess_elim isrec false sort hyp0 gl in
       let scheme = compute_elim_sig sigma ~elimc elimt in
       (* We drop the scheme waiting to know if it is dependent *)
       scheme, ElimOver (isrec,hyp0)
    | Some e ->
	let evd, (elimc,elimt),ind_guess = given_elim hyp0 e gl in
	let scheme = compute_elim_sig sigma ~elimc elimt in
	if Option.is_empty scheme.indarg then error "Cannot find induction type";
	let indsign = compute_scheme_signature evd scheme hyp0 ind_guess in
	let elim = ({elimindex = Some(-1); elimbody = elimc; elimrename = None},elimt) in
	scheme, ElimUsing (elim,indsign)
  in
  match scheme.indref with
  | None -> error_ind_scheme ""
  | Some ref -> ref, scheme.nparams, elim

let get_elim_signature elim hyp0 gl =
  compute_elim_signature (given_elim hyp0 elim gl) hyp0

let is_functional_induction elimc gl =
  let sigma = Tacmach.New.project gl in
  let scheme = compute_elim_sig sigma ~elimc (Tacmach.New.pf_unsafe_type_of gl (fst elimc)) in
  (* The test is not safe: with non-functional induction on non-standard
     induction scheme, this may fail *)
  Option.is_empty scheme.indarg

(* Wait the last moment to guess the eliminator so as to know if we
   need a dependent one or not *)

let get_eliminator elim dep s gl =
  match elim with
  | ElimUsing (elim,indsign) ->
      Tacmach.New.project gl, (* bugged, should be computed *) true, elim, indsign
  | ElimOver (isrec,id) ->
      let evd, (elimc,elimt),_ as elims = guess_elim isrec dep s id gl in
      let _, (l, s) = compute_elim_signature elims id in
      let branchlengthes = List.map (fun d -> assert (RelDecl.is_local_assum d); pi1 (decompose_prod_letin (Tacmach.New.project gl) (RelDecl.get_type d)))
                                    (List.rev s.branches)
      in
      evd, isrec, ({elimindex = None; elimbody = elimc; elimrename = Some (isrec,Array.of_list branchlengthes)}, elimt), l

(* Instantiate all meta variables of elimclause using lid, some elts
   of lid are parameters (first ones), the other are
   arguments. Returns the clause obtained.  *)
let recolle_clenv i params args elimclause gl =
  let _,arr = destApp elimclause.evd elimclause.templval.rebus in
  let lindmv =
    Array.map
      (fun x ->
	match EConstr.kind elimclause.evd x with
	  | Meta mv -> mv
	  | _  -> user_err ~hdr:"elimination_clause"
              (str "The type of the elimination clause is not well-formed."))
      arr in
  let k = match i with -1 -> Array.length lindmv - List.length args | _ -> i in
  (* parameters correspond to first elts of lid. *)
  let clauses_params =
    List.map_i (fun i id -> mkVar id , pf_get_hyp_typ id gl, lindmv.(i))
      0 params in
  let clauses_args =
    List.map_i (fun i id -> mkVar id , pf_get_hyp_typ id gl, lindmv.(k+i))
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
      let elimclause' = clenv_fchain ~with_univs:false i acc indclause in
      elimclause')
    (List.rev clauses)
    elimclause

(* Unification of the goal and the principle applied to meta variables:
   (elimc ?i ?j ?k...?l). This solves partly meta variables (and may
    produce new ones). Then refine with the resulting term with holes.
*)
let induction_tac with_evars params indvars elim =
  Proofview.Goal.enter begin fun gl ->
  let sigma = Tacmach.New.project gl in
  let ({elimindex=i;elimbody=(elimc,lbindelimc);elimrename=rename},elimt) = elim in
  let i = match i with None -> index_of_ind_arg sigma elimt | Some i -> i in
  (* elimclause contains this: (elimc ?i ?j ?k...?l) *)
  let elimc = contract_letin_in_lam_header sigma elimc in
  let elimc = mkCast (elimc, DEFAULTcast, elimt) in
  let elimclause = Tacmach.New.pf_apply make_clenv_binding gl (elimc,elimt) lbindelimc in
  (* elimclause' is built from elimclause by instanciating all args and params. *)
  let elimclause' = recolle_clenv i params indvars elimclause gl in
  (* one last resolution (useless?) *)
  let resolved = clenv_unique_resolver ~flags:(elim_flags ()) elimclause' gl in
  Clenvtac.clenv_refine ~with_evars resolved
  end

(* Apply induction "in place" taking into account dependent
   hypotheses from the context, replacing the main hypothesis on which
   induction applies with the induction hypotheses *)

let apply_induction_in_context with_evars hyp0 inhyps elim indvars names induct_tac =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let concl = Tacmach.New.pf_concl gl in
    let statuslists,lhyp0,toclear,deps,avoid,dep_in_hyps = cook_sign hyp0 inhyps indvars env sigma in
    let dep_in_concl = Option.cata (fun id -> occur_var env sigma id concl) false hyp0 in
    let dep = dep_in_hyps || dep_in_concl in
    let tmpcl = it_mkNamedProd_or_LetIn concl deps in
    let s = Retyping.get_sort_family_of env sigma tmpcl in
    let deps_cstr =
      List.fold_left
        (fun a decl -> if NamedDecl.is_local_assum decl then (mkVar (NamedDecl.get_id decl))::a else a) [] deps in
    let (sigma, isrec, elim, indsign) = get_eliminator elim dep s gl in
    let branchletsigns =
      let f (_,is_not_let,_,_) = is_not_let in
      Array.map (fun (_,l) -> List.map f l) indsign in
    let names = compute_induction_names branchletsigns names in
    Array.iter (check_name_unicity env toclear []) names;
    let tac =
    (if isrec then Tacticals.New.tclTHENFIRSTn else Tacticals.New.tclTHENLASTn)
      (Tacticals.New.tclTHENLIST [
        (* Generalize dependent hyps (but not args) *)
        if deps = [] then Proofview.tclUNIT () else apply_type ~typecheck:false tmpcl deps_cstr;
        (* side-conditions in elim (resp case) schemes come last (resp first) *)
        induct_tac elim;
        Tacticals.New.tclMAP expand_hyp toclear;
      ])
      (Array.map2
         (induct_discharge with_evars lhyp0 avoid
            (re_intro_dependent_hypotheses statuslists))
         indsign names)
    in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma) tac
  end

let induction_with_atomization_of_ind_arg isrec with_evars elim names hyp0 inhyps =
  Proofview.Goal.enter begin fun gl ->
  let elim_info = find_induction_type isrec elim hyp0 gl in
  atomize_param_of_ind_then elim_info hyp0 (fun indvars ->
    apply_induction_in_context with_evars (Some hyp0) inhyps (pi3 elim_info) indvars names
      (fun elim -> induction_tac with_evars [] [hyp0] elim))
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
  Proofview.Goal.enter begin fun gl ->
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
    if List.is_empty indvars then Id.Set.singleton (List.hd lid_params) else Id.Set.of_list indvars in
  let induct_tac elim = Tacticals.New.tclTHENLIST [
    (* pattern to make the predicate appear. *)
    reduce (Pattern (List.map inj_with_occurrences lidcstr)) onConcl;
    (* Induction by "refine (indscheme ?i ?j ?k...)" + resolution of all
       possible holes using arguments given by the user (but the
       functional one). *)
    (* FIXME: Tester ca avec un principe dependant et non-dependant *)
    induction_tac with_evars params realindvars elim;
  ] in
  let elim = ElimUsing (({elimindex = Some (-1); elimbody = Option.get scheme.elimc; elimrename = None}, scheme.elimt), indsign) in
  apply_induction_in_context with_evars None [] elim indvars names induct_tac
  end

(* assume that no occurrences are selected *)
let clear_unselected_context id inhyps cls =
  Proofview.Goal.enter begin fun gl ->
  if occur_var (Tacmach.New.pf_env gl) (Tacmach.New.project gl) id (Tacmach.New.pf_concl gl) &&
    cls.concl_occs == NoOccurrences
  then user_err 
    (str "Conclusion must be mentioned: it depends on " ++ Id.print id
     ++ str ".");
  match cls.onhyps with
  | Some hyps ->
      let to_erase d =
        let id' = NamedDecl.get_id d in
	if Id.List.mem id' inhyps then (* if selected, do not erase *) None
	else
	  (* erase if not selected and dependent on id or selected hyps *)
	  let test id = occur_var_in_decl (Tacmach.New.pf_env gl) (Tacmach.New.project gl) id d in
	  if List.exists test (id::inhyps) then Some id' else None in
      let ids = List.map_filter to_erase (Proofview.Goal.hyps gl) in
      clear ids
  | None -> Proofview.tclUNIT ()
  end

let use_bindings env sigma elim must_be_closed (c,lbind) typ =
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
      if must_be_closed && occur_meta indclause.evd (clenv_value indclause) then
        error "Need a fully applied argument.";
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
  let (_,u,_) = destProd sigma cl.cl_concl in
  fun t -> Option.has_some (Evarconv.cumul env sigma t u)

let check_enough_applied env sigma elim =
  (* A heuristic to decide whether the induction arg is enough applied *)
  match elim with
  | None ->
      (* No eliminator given *)
      fun u ->
      let t,_ = decompose_app sigma (whd_all env sigma u) in isInd sigma t
  | Some elimc ->
      let elimt = Retyping.get_type_of env sigma (fst elimc) in
      let scheme = compute_elim_sig sigma ~elimc elimt in
      match scheme.indref with
      | None ->
         (* in the absence of information, do not assume it may be
            partially applied *)
          fun _ -> true
      | Some _ ->
          (* Last argument is supposed to be the induction argument *)
          check_expected_type env sigma elimc elimt

let guard_no_unifiable = Proofview.guard_no_unifiable >>= function
  | None -> Proofview.tclUNIT ()
  | Some l ->
    Proofview.tclENV     >>= function env ->
    Proofview.tclEVARMAP >>= function sigma ->
    Proofview.tclZERO (RefinerError (env, sigma, UnresolvedBindings l))

let pose_induction_arg_then isrec with_evars (is_arg_pure_hyp,from_prefix) elim
     id ((pending,(c0,lbind)),(eqname,names)) t0 inhyps cls tac =
  Proofview.Goal.enter begin fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  let env = Proofview.Goal.env gl in
  let ccl = Proofview.Goal.concl gl in
  let store = Proofview.Goal.extra gl in
  let check = check_enough_applied env sigma elim in
  let (sigma', c) = use_bindings env sigma elim false (c0,lbind) t0 in
  let abs = AbstractPattern (from_prefix,check,Name id,(pending,c),cls,false) in
  let (id,sign,_,lastlhyp,ccl,res) = make_abstraction env sigma' ccl abs in
  match res with
  | None ->
      (* pattern not found *)
      let with_eq = Option.map (fun eq -> (false,mk_eq_name env id eq)) eqname in
      let inhyps = if List.is_empty inhyps then inhyps else Option.fold_left (fun inhyps (_,heq) -> heq::inhyps) inhyps with_eq in
      (* we restart using bindings after having tried type-class
         resolution etc. on the term given by the user *)
      let flags = tactic_infer_flags (with_evars && (* do not give a success semantics to edestruct on an open term yet *) false) in
      let (sigma, c0) = finish_evar_resolution ~flags env sigma (pending,c0) in
      let tac =
      (if isrec then
          (* Historically, induction has side conditions last *)
          Tacticals.New.tclTHENFIRST
       else
          (* and destruct has side conditions first *)
          Tacticals.New.tclTHENLAST)
      (Tacticals.New.tclTHENLIST [
        Refine.refine ~typecheck:false begin fun sigma ->
          let b = not with_evars && with_eq != None in
          let (sigma, c) = use_bindings env sigma elim b (c0,lbind) t0 in
          let t = Retyping.get_type_of env sigma c in
          mkletin_goal env sigma store with_eq false (id,lastlhyp,ccl,c) (Some t)
        end;
        if with_evars then Proofview.shelve_unifiable else guard_no_unifiable;
        if is_arg_pure_hyp
        then Proofview.tclEVARMAP >>= fun sigma -> Tacticals.New.tclTRY (clear [destVar sigma c0])
        else Proofview.tclUNIT ();
        if isrec then Proofview.cycle (-1) else Proofview.tclUNIT ()
      ])
      (tac inhyps)
      in
      Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma) tac

  | Some (sigma', c) ->
      (* pattern found *)
      (* TODO: if ind has predicate parameters, use JMeq instead of eq *)
      let env = reset_with_named_context sign env in
      let with_eq = Option.map (fun eq -> (false,mk_eq_name env id eq)) eqname in
      let inhyps = if List.is_empty inhyps then inhyps else Option.fold_left (fun inhyps (_,heq) -> heq::inhyps) inhyps with_eq in
      let tac =
      Tacticals.New.tclTHENLIST [
        Refine.refine ~typecheck:false begin fun sigma ->
          mkletin_goal env sigma store with_eq true (id,lastlhyp,ccl,c) None
        end;
        (tac inhyps)
      ]
      in
      Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma') tac
  end

let has_generic_occurrences_but_goal cls id env sigma ccl =
  clause_with_generic_context_selection cls &&
  (* TODO: whd_evar of goal *)
  (cls.concl_occs != NoOccurrences || not (occur_var env sigma id ccl))

let induction_gen clear_flag isrec with_evars elim
    ((_pending,(c,lbind)),(eqname,names) as arg) cls =
  let inhyps = match cls with
  | Some {onhyps=Some hyps} -> List.map (fun ((_,id),_) -> id) hyps
  | _ -> [] in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let evd = Proofview.Goal.sigma gl in
  let ccl = Proofview.Goal.concl gl in
  let cls = Option.default allHypsAndConcl cls in
  let t = typ_of env evd c in
  let is_arg_pure_hyp =
    isVar evd c && not (mem_named_context_val (destVar evd c) (Global.named_context_val ()))
    && lbind == NoBindings && not with_evars && Option.is_empty eqname
    && clear_flag == None
    && has_generic_occurrences_but_goal cls (destVar evd c) env evd ccl in
  let enough_applied = check_enough_applied env evd elim t in
  if is_arg_pure_hyp && enough_applied then
    (* First case: induction on a variable already in an inductive type and
       with maximal abstraction over the variable.
       This is a situation where the induction argument is a
       clearable variable of the goal w/o occurrence selection
       and w/o equality kept: no need to generalize *)
    let id = destVar evd c in
    Tacticals.New.tclTHEN
      (clear_unselected_context id inhyps cls)
      (induction_with_atomization_of_ind_arg
         isrec with_evars elim names id inhyps)
  else
  (* Otherwise, we look for the pattern, possibly adding missing arguments and
     declaring the induction argument as a new local variable *)
    let id =
    (* Type not the right one if partially applied but anyway for internal use*)
      let x = id_of_name_using_hdchar env evd t Anonymous in
      new_fresh_id Id.Set.empty x gl in
    let info_arg = (is_arg_pure_hyp, not enough_applied) in
    pose_induction_arg_then
      isrec with_evars info_arg elim id arg t inhyps cls
    (induction_with_atomization_of_ind_arg
       isrec with_evars elim names id)
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
    | (c,Some{CAst.loc;v=eqname}) ->
      user_err ?loc  (str "Do not know what to do with " ++
                         Miscprint.pr_intro_pattern_naming eqname)) lc in
  let rec atomize_list l =
    match l with
      | [] -> Proofview.tclUNIT ()
      | c::l' ->
          Proofview.tclEVARMAP >>= fun sigma ->
	  match EConstr.kind sigma c with
	    | Var id when not (mem_named_context_val id (Global.named_context_val ()))
		&& not with_evars ->
		let _ = newlc:= id::!newlc in
		atomize_list l'

	    | _ ->
                Proofview.Goal.enter begin fun gl ->
                let type_of = Tacmach.New.pf_unsafe_type_of gl in
                let sigma = Tacmach.New.project gl in
                Proofview.tclENV >>= fun env ->
                let x =
		  id_of_name_using_hdchar env sigma (type_of c) Anonymous in

                let id = new_fresh_id Id.Set.empty x gl in
		let newl' = List.map (fun r -> replace_term sigma c (mkVar id) r) l' in
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
    Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    match elim with
    | Some elim when is_functional_induction elim gl ->
      (* Standard induction on non-standard induction schemes *)
      (* will be removable when is_functional_induction will be more clever *)
      if not (Option.is_empty cls) then error "'in' clause not supported here.";
      let _,c = force_destruction_arg false env sigma c in
      onInductionArg
	(fun _clear_flag c ->
	  induction_gen_l isrec with_evars elim names
            [with_no_bindings c,eqname]) c
    | _ ->
      (* standard induction *)
      onOpenInductionArg env sigma
      (fun clear_flag c -> induction_gen clear_flag isrec with_evars elim (c,allnames) cls) c
    end
  | _ ->
    Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
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
          let sigma = Tacmach.New.project gl in
          onOpenInductionArg env sigma (fun clear_flag a ->
            induction_gen clear_flag false with_evars None (a,b) cl) a
          end) l)
    | Some elim ->
      (* Several induction hyps with induction scheme *)
      let lc = List.map (on_pi1 (fun c -> snd (force_destruction_arg false env sigma c))) lc in
      let newlc =
        List.map (fun (x,(eqn,names),cls) ->
          if cls != None then error "'in' clause not yet supported here.";
	  match x with (* FIXME: should we deal with ElimOnIdent? *)
          | _clear_flag,ElimOnConstr x ->
              if eqn <> None then error "'eqn' clause not supported here.";
              (with_no_bindings x,names)
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
    ((Evd.empty,(c,NoBindings)),(None,l)) None

let destruct ev clr c l e =
  induction_gen clr false ev e
    ((Evd.empty,(c,NoBindings)),(None,l)) None

(*
 *  Eliminations giving the type instead of the proof.
 * These tactics use the default elimination constant and
 * no substitutions at all.
 * May be they should be integrated into Elim ...
 *)

let elim_scheme_type elim t =
  Proofview.Goal.enter begin fun gl ->
  let clause = mk_clenv_type_of gl elim in
  match EConstr.kind clause.evd (last_arg clause.evd clause.templval.rebus) with
    | Meta mv ->
        let clause' =
	  (* t is inductive, then CUMUL or CONV is irrelevant *)
	  clenv_unify ~flags:(elim_flags ()) Reduction.CUMUL t
            (clenv_meta_type clause mv) clause in
	Clenvtac.res_pf clause' ~flags:(elim_flags ()) ~with_evars:false
    | _ -> anomaly (Pp.str "elim_scheme_type.")
  end

let elim_type t =
  Proofview.Goal.enter begin fun gl ->
  let (ind,t) = Tacmach.New.pf_apply reduce_to_atomic_ind gl t in
  let evd, elimc = find_ind_eliminator (fst ind) (Tacticals.New.elimination_sort_of_goal gl) gl in
  Proofview.tclTHEN (Proofview.Unsafe.tclEVARS evd) (elim_scheme_type elimc t)
  end

let case_type t =
  Proofview.Goal.enter begin fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  let env = Tacmach.New.pf_env gl in
  let ((ind, u), t) = reduce_to_atomic_ind env sigma t in
  let u = EInstance.kind sigma u in
  let s = Tacticals.New.elimination_sort_of_goal gl in
  let (evd, elimc) = build_case_analysis_scheme_default env sigma (ind, u) s in
  let elimc = EConstr.of_constr elimc in
  Proofview.tclTHEN (Proofview.Unsafe.tclEVARS evd) (elim_scheme_type elimc t)
  end


(************************************************)
(*  Tactics related with logic connectives      *)
(************************************************)

(* Reflexivity tactics *)

let (forward_setoid_reflexivity, setoid_reflexivity) = Hook.make ()

let maybe_betadeltaiota_concl allowred gl =
  let concl = Tacmach.New.pf_concl gl in
  let sigma = Tacmach.New.project gl in
  if not allowred then concl
  else
    let env = Proofview.Goal.env gl in
    whd_all env sigma concl

let reflexivity_red allowred =
  Proofview.Goal.enter begin fun gl ->
  (* PL: usual reflexivity don't perform any reduction when searching
     for an equality, but we may need to do some when called back from
     inside setoid_reflexivity (see Optimize cases in setoid_replace.ml). *)
    let sigma = Tacmach.New.project gl in
    let concl = maybe_betadeltaiota_concl allowred gl in
    match match_with_equality_type sigma concl with
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

let match_with_equation sigma c =
  Proofview.tclENV >>= fun env ->
  try
    let res = match_with_equation env sigma c in
    Proofview.tclUNIT res
  with NoEquationFound ->
    Proofview.tclZERO NoEquationFound

let symmetry_red allowred =
  Proofview.Goal.enter begin fun gl ->
  (* PL: usual symmetry don't perform any reduction when searching
     for an equality, but we may need to do some when called back from
     inside setoid_reflexivity (see Optimize cases in setoid_replace.ml). *)
  let sigma = Tacmach.New.project gl in
  let concl = maybe_betadeltaiota_concl allowred gl in
  match_with_equation sigma concl >>= fun with_eqn ->
  match with_eqn with
  | Some eq_data,_,_ ->
      Tacticals.New.tclTHEN
        (convert_concl_no_check concl DEFAULTcast)
        (Tacticals.New.pf_constr_of_global eq_data.sym >>= apply)
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
  let sigma = Tacmach.New.project gl in
  let ctype = Tacmach.New.pf_unsafe_type_of gl (mkVar id) in
  let sign,t = decompose_prod_assum sigma ctype in
  Proofview.tclORELSE
    begin
      match_with_equation sigma t >>= fun (_,hdcncl,eq) ->
        let symccl =
          match eq with
          | MonomorphicLeibnizEq (c1,c2) -> mkApp (hdcncl, [| c2; c1 |])
          | PolymorphicLeibnizEq (typ,c1,c2) -> mkApp (hdcncl, [| typ; c2; c1 |])
          | HeterogenousEq (t1,c1,t2,c2) -> mkApp (hdcncl, [| t2; c2; t1; c1 |]) in
        Tacticals.New.tclTHENS (cut (EConstr.it_mkProd_or_LetIn symccl sign))
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
      let sigma = Tacmach.New.project gl in
      let type_of = Typing.unsafe_type_of env sigma in
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
  let sigma = Tacmach.New.project gl in
  let concl = maybe_betadeltaiota_concl allowred gl in
  match_with_equation sigma concl >>= fun with_eqn ->
  match with_eqn with
  | Some eq_data,_,_ ->
      Tacticals.New.tclTHEN
        (convert_concl_no_check concl DEFAULTcast)
        (match t with
	  | None -> Tacticals.New.pf_constr_of_global eq_data.trans >>= eapply
	  | Some t -> Tacticals.New.pf_constr_of_global eq_data.trans >>= fun trans -> apply_list [trans; t])
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
let interpretable_as_section_decl env evd d1 d2 =
  let open Context.Named.Declaration in
  let e_eq_constr_univs sigma c1 c2 = match eq_constr_universes env !sigma c1 c2 with
  | None -> false
  | Some cstr ->
    try ignore (Evd.add_universe_constraints !sigma cstr); true
    with UniversesDiffer -> false
  in
  match d2, d1 with
  | LocalDef _, LocalAssum _ -> false
  | LocalDef (_,b1,t1), LocalDef (_,b2,t2) ->
    e_eq_constr_univs evd b1 b2 && e_eq_constr_univs evd t1 t2
  | LocalAssum (_,t1), d2 -> e_eq_constr_univs evd t1 (NamedDecl.get_type d2)

let rec decompose len c t accu =
  let open Context.Rel.Declaration in
  if len = 0 then (c, t, accu)
  else match Constr.kind c, Constr.kind t with 
  | Lambda (na, u, c), Prod (_, _, t) ->
    decompose (pred len) c t (LocalAssum (na, u) :: accu)
  | LetIn (na, b, u, c), LetIn (_, _, _, t) ->
    decompose (pred len) c t (LocalDef (na, b, u) :: accu)
  | _ -> assert false

let rec shrink ctx sign c t accu =
  let open Constr in
  let open CVars in
  match ctx, sign with
  | [], [] -> (c, t, accu)
  | p :: ctx, decl :: sign ->
      if noccurn 1 c && noccurn 1 t then
        let c = subst1 mkProp c in
        let t = subst1 mkProp t in
        shrink ctx sign c t accu
      else
        let c = Term.mkLambda_or_LetIn p c in
        let t = Term.mkProd_or_LetIn p t in
        let accu = if RelDecl.is_local_assum p
                   then mkVar (NamedDecl.get_id decl) :: accu
                   else accu
    in
    shrink ctx sign c t accu
| _ -> assert false

let shrink_entry sign const =
  let open Entries in
  let typ = match const.const_entry_type with
  | None -> assert false
  | Some t -> t
  in
  (** The body has been forced by the call to [build_constant_by_tactic] *)
  let () = assert (Future.is_over const.const_entry_body) in
  let ((body, uctx), eff) = Future.force const.const_entry_body in
  let (body, typ, ctx) = decompose (List.length sign) body typ [] in
  let (body, typ, args) = shrink ctx sign body typ [] in
  let const = { const with
    const_entry_body = Future.from_val ((body, uctx), eff);
    const_entry_type = Some typ;
  } in
  (const, args)

let cache_term_by_tactic_then ~opaque ?(goal_type=None) id gk tac tacK =
  let open Tacticals.New in
  let open Tacmach.New in
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let current_sign = Global.named_context_val ()
  and global_sign = Proofview.Goal.hyps gl in
  let evdref = ref sigma in
  let sign,secsign =
    List.fold_right
      (fun d (s1,s2) ->
        let id = NamedDecl.get_id d in
	if mem_named_context_val id current_sign &&
          interpretable_as_section_decl env evdref (lookup_named_val id current_sign) d
        then (s1,push_named_context_val d s2)
	else (Context.Named.add d s1,s2))
      global_sign (Context.Named.empty, empty_named_context_val) in
  let id = next_global_ident_away id (pf_ids_set_of_hyps gl) in
  let concl = match goal_type with
              | None ->  Proofview.Goal.concl gl
              | Some ty -> ty in
  let concl = it_mkNamedProd_or_LetIn concl sign in
  let concl =
    try flush_and_check_evars !evdref concl
    with Uninstantiated_evar _ ->
      error "\"abstract\" cannot handle existentials." in

  let evd, ctx, concl =
    (* FIXME: should be done only if the tactic succeeds *)
    let evd = Evd.minimize_universes !evdref in
    let ctx = Evd.universe_context_set evd in
      evd, ctx, Evarutil.nf_evars_universes evd concl
  in
  let concl = EConstr.of_constr concl in
  let solve_tac = tclCOMPLETE (tclTHEN (tclDO (List.length sign) intro) tac) in
  let ectx = Evd.evar_universe_context evd in
  let (const, safe, ectx) =
    try Pfedit.build_constant_by_tactic ~goal_kind:gk id ectx secsign concl solve_tac
    with Logic_monad.TacticFailure e as src ->
    (* if the tactic [tac] fails, it reports a [TacticFailure e],
       which is an error irrelevant to the proof system (in fact it
       means that [e] comes from [tac] failing to yield enough
       success). Hence it reraises [e]. *)
    let (_, info) = CErrors.push src in
    iraise (e, info)
  in
  let const, args = shrink_entry sign const in
  let args = List.map EConstr.of_constr args in
  let cd = Entries.DefinitionEntry { const with Entries.const_entry_opaque = opaque } in
  let decl = (cd, if opaque then IsProof Lemma else IsDefinition Definition) in
  let cst () =
    (** do not compute the implicit arguments, it may be costly *)
    let () = Impargs.make_implicit_args false in
    (** ppedrot: seems legit to have abstracted subproofs as local*)
    Declare.declare_constant ~internal:Declare.InternalTacticRequest ~local:true id decl
  in
  let cst = Impargs.with_implicit_protection cst () in
  let lem =
    match const.Entries.const_entry_universes with
    | Entries.Polymorphic_const_entry uctx ->
      let uctx = Univ.ContextSet.of_context uctx in
      (** Hack: the kernel may generate definitions whose universe variables are
          not the same as requested in the entry because of constraints delayed
          in the body, even in polymorphic mode. We mimick what it does for now
          in hope it is fixed at some point. *)
      let (_, body_uctx), _ = Future.force const.Entries.const_entry_body in
      let uctx = Univ.ContextSet.to_context (Univ.ContextSet.union uctx body_uctx) in
      let u = Univ.UContext.instance uctx in
      mkConstU (cst, EInstance.make u)
    | Entries.Monomorphic_const_entry _ ->
      mkConst cst
  in
  let evd = Evd.set_universe_context evd ectx in
  let open Safe_typing in
  let eff = private_con_of_con (Global.safe_env ()) cst in
  let effs = concat_private eff
    Entries.(snd (Future.force const.const_entry_body)) in
  let solve =
    Proofview.tclEFFECTS effs <*>
    tacK lem args
  in
  let tac = if not safe then Proofview.mark_as_unsafe <*> solve else solve in
  Proofview.tclTHEN (Proofview.Unsafe.tclEVARS evd) tac
  end

let abstract_subproof ~opaque id gk tac =
  cache_term_by_tactic_then ~opaque id gk tac (fun lem args -> exact_no_check (applist (lem, args)))

let anon_id = Id.of_string "anonymous"

let name_op_to_name name_op object_kind suffix =
  let open Proof_global in
  let default_gk = (Global, false, object_kind) in
  let name, gk = match Proof_global.V82.get_current_initial_conclusions () with
  | (id, (_, gk)) -> Some id, gk
  | exception NoCurrentProof -> None, default_gk
  in
  match name_op with
  | Some s -> s, gk
  | None ->
    let name = Option.default anon_id name in
    add_suffix name suffix, gk

let tclABSTRACT ?(opaque=true) name_op tac =
  let s, gk = if opaque
    then name_op_to_name name_op (Proof Theorem) "_subproof"
    else name_op_to_name name_op (DefinitionBody Definition) "_subterm" in
  abstract_subproof ~opaque s gk tac

let constr_eq ~strict x y =
  let fail = Tacticals.New.tclFAIL 0 (str "Not equal") in
  let fail_universes = Tacticals.New.tclFAIL 0 (str "Not equal (due to universes)") in
  Proofview.Goal.enter begin fun gl ->
    let env = Tacmach.New.pf_env gl in
    let evd = Tacmach.New.project gl in
      match EConstr.eq_constr_universes env evd x y with
      | Some csts ->
        let csts = UnivProblem.to_constraints ~force_weak:false (Evd.universes evd) csts in
        if strict then
          if Evd.check_constraints evd csts then Proofview.tclUNIT ()
          else fail_universes
        else
          (match Evd.add_constraints evd csts with
           | evd -> Proofview.Unsafe.tclEVARS evd
           | exception Univ.UniverseInconsistency _ ->
             fail_universes)
      | None -> fail
  end

let unify ?(state=full_transparent_state) x y =
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
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
    let sigma = w_unify (Tacmach.New.pf_env gl) sigma Reduction.CONV ~flags x y in
    Proofview.Unsafe.tclEVARS sigma
  with e when CErrors.noncritical e ->
    Proofview.tclZERO (PretypeError (env, sigma, CannotUnify (x, y, None)))
  end

module Simple = struct
  (** Simplified version of some of the above tactics *)

  let intro x = intro_move (Some x) MoveLast

  let apply c =
    apply_with_bindings_gen false false [None,(CAst.make (c,NoBindings))]
  let eapply c =
    apply_with_bindings_gen false true [None,(CAst.make (c,NoBindings))]
  let elim c   = elim false None (c,NoBindings) None
  let case   c = general_case_analysis false None (c,NoBindings)

  let apply_in id c =
    apply_in false false id [None,(CAst.make (c, NoBindings))] None

end


(** Tacticals defined directly in term of Proofview *)
module New = struct
  open Genredexpr
  open Locus

  let reduce_after_refine =
    reduce
      (Lazy {rBeta=true;rMatch=true;rFix=true;rCofix=true;
	     rZeta=false;rDelta=false;rConst=[]})
      {onhyps = Some []; concl_occs = AllOccurrences }

  let refine ~typecheck c =
    Refine.refine ~typecheck c <*>
    reduce_after_refine
end
