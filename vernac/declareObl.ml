(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Environ
open Context
open Constr
open Vars
open Decl_kinds
open Entries

type 'a obligation_body = DefinedObl of 'a | TermObl of constr

type obligation =
  { obl_name : Id.t
  ; obl_type : types
  ; obl_location : Evar_kinds.t Loc.located
  ; obl_body : pconstant obligation_body option
  ; obl_status : bool * Evar_kinds.obligation_definition_status
  ; obl_deps : Int.Set.t
  ; obl_tac : unit Proofview.tactic option }

type obligations = obligation array * int

type notations =
  (lstring * Constrexpr.constr_expr * Notation_term.scope_name option) list

type fixpoint_kind =
  | IsFixpoint of lident option list
  | IsCoFixpoint

type program_info =
  { prg_name : Id.t
  ; prg_body : constr
  ; prg_type : constr
  ; prg_ctx : UState.t
  ; prg_univdecl : UState.universe_decl
  ; prg_obligations : obligations
  ; prg_deps : Id.t list
  ; prg_fixkind : fixpoint_kind option
  ; prg_implicits : Impargs.manual_implicits
  ; prg_notations : notations
  ; prg_poly : bool
  ; prg_scope : DeclareDef.locality
  ; prg_kind : definition_object_kind
  ; prg_reduce : constr -> constr
  ; prg_hook : DeclareDef.Hook.t option
  ; prg_opaque : bool
  ; prg_sign : named_context_val }

(* Saving an obligation *)

let get_shrink_obligations =
  Goptions.declare_bool_option_and_ref ~depr:true (* remove in 8.8 *)
    ~name:"Shrinking of Program obligations" ~key:["Shrink"; "Obligations"]
    ~value:true

(* XXX: Is this the right place for this? *)
let it_mkLambda_or_LetIn_or_clean t ctx =
  let open Context.Rel.Declaration in
  let fold t decl =
    if is_local_assum decl then Term.mkLambda_or_LetIn decl t
    else if noccurn 1 t then subst1 mkProp t
    else Term.mkLambda_or_LetIn decl t
  in
  Context.Rel.fold_inside fold ctx ~init:t

(* XXX: Is this the right place for this? *)
let decompose_lam_prod c ty =
  let open Context.Rel.Declaration in
  let rec aux ctx c ty =
    match (Constr.kind c, Constr.kind ty) with
    | LetIn (x, b, t, c), LetIn (x', b', t', ty)
      when Constr.equal b b' && Constr.equal t t' ->
      let ctx' = Context.Rel.add (LocalDef (x, b', t')) ctx in
      aux ctx' c ty
    | _, LetIn (x', b', t', ty) ->
      let ctx' = Context.Rel.add (LocalDef (x', b', t')) ctx in
      aux ctx' (lift 1 c) ty
    | LetIn (x, b, t, c), _ ->
      let ctx' = Context.Rel.add (LocalDef (x, b, t)) ctx in
      aux ctx' c (lift 1 ty)
    | Lambda (x, b, t), Prod (x', b', t')
    (* By invariant, must be convertible *) ->
      let ctx' = Context.Rel.add (LocalAssum (x, b')) ctx in
      aux ctx' t t'
    | Cast (c, _, _), _ -> aux ctx c ty
    | _, _ -> (ctx, c, ty)
  in
  aux Context.Rel.empty c ty

(* XXX: What's the relation of this with Abstract.shrink ? *)
let shrink_body c ty =
  let ctx, b, ty =
    match ty with
    | None ->
      let ctx, b = Term.decompose_lam_assum c in
      (ctx, b, None)
    | Some ty ->
      let ctx, b, ty = decompose_lam_prod c ty in
      (ctx, b, Some ty)
  in
  let b', ty', n, args =
    List.fold_left
      (fun (b, ty, i, args) decl ->
        if noccurn 1 b && Option.cata (noccurn 1) true ty then
          (subst1 mkProp b, Option.map (subst1 mkProp) ty, succ i, args)
        else
          let open Context.Rel.Declaration in
          let args = if is_local_assum decl then mkRel i :: args else args in
          ( Term.mkLambda_or_LetIn decl b
          , Option.map (Term.mkProd_or_LetIn decl) ty
          , succ i
          , args ) )
      (b, ty, 1, []) ctx
  in
  (ctx, b', ty', Array.of_list args)

let unfold_entry cst = Hints.HintsUnfoldEntry [EvalConstRef cst]

let add_hint local prg cst =
  Hints.add_hints ~local [Id.to_string prg.prg_name] (unfold_entry cst)

(***********************************************************************)
(* Saving an obligation                                                *)
(***********************************************************************)

(* true = hide obligations *)
let get_hide_obligations =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~name:"Hidding of Program obligations"
    ~key:["Hide"; "Obligations"]
    ~value:false

let declare_obligation prg obl body ty uctx =
  let body = prg.prg_reduce body in
  let ty = Option.map prg.prg_reduce ty in
  match obl.obl_status with
  | _, Evar_kinds.Expand -> (false, {obl with obl_body = Some (TermObl body)})
  | force, Evar_kinds.Define opaque ->
    let opaque = (not force) && opaque in
    let poly = prg.prg_poly in
    let ctx, body, ty, args =
      if get_shrink_obligations () && not poly then shrink_body body ty
      else ([], body, ty, [||])
    in
    let body =
      ((body, Univ.ContextSet.empty), Evd.empty_side_effects)
    in
    let ce =
      Proof_global.{ proof_entry_body = Future.from_val ~fix_exn:(fun x -> x) body
      ; proof_entry_secctx = None
      ; proof_entry_type = ty
      ; proof_entry_universes = uctx
      ; proof_entry_opaque = opaque
      ; proof_entry_inline_code = false
      ; proof_entry_feedback = None }
    in
    (* ppedrot: seems legit to have obligations as local *)
    let constant =
      Declare.declare_constant obl.obl_name ~local:Declare.ImportNeedQualified
        (Declare.DefinitionEntry ce, IsProof Property)
    in
    if not opaque then
      add_hint (Locality.make_section_locality None) prg constant;
    Declare.definition_message obl.obl_name;
    let body =
      match uctx with
      | Polymorphic_entry (_, uctx) ->
        Some (DefinedObl (constant, Univ.UContext.instance uctx))
      | Monomorphic_entry _ ->
        Some
          (TermObl
             (it_mkLambda_or_LetIn_or_clean
                (mkApp (mkConst constant, args))
                ctx))
    in
    (true, {obl with obl_body = body})

(* Updating the obligation meta-info on close *)

let not_transp_msg =
  Pp.(
    str "Obligation should be transparent but was declared opaque."
    ++ spc ()
    ++ str "Use 'Defined' instead.")

let pperror cmd = CErrors.user_err ~hdr:"Program" cmd
let err_not_transp () = pperror not_transp_msg

module ProgMap = Id.Map

let from_prg, program_tcc_summary_tag =
  Summary.ref_tag ProgMap.empty ~name:"program-tcc-table"

(* In all cases, the use of the map is read-only so we don't expose the ref *)
let get_prg_info_map () = !from_prg

let map_keys m = ProgMap.fold (fun k _ l -> k :: l) m []

let close sec =
  if not (ProgMap.is_empty !from_prg) then
    let keys = map_keys !from_prg in
    CErrors.user_err ~hdr:"Program"
      Pp.(
        str "Unsolved obligations when closing "
        ++ str sec ++ str ":" ++ spc ()
        ++ prlist_with_sep spc (fun x -> Id.print x) keys
        ++ ( str (if Int.equal (List.length keys) 1 then " has " else " have ")
           ++ str "unsolved obligations" ))

let input : program_info CEphemeron.key ProgMap.t -> Libobject.obj =
  let open Libobject in
  declare_object
    { (default_object "Program state") with
      cache_function = (fun (na, pi) -> from_prg := pi)
    ; load_function = (fun _ (_, pi) -> from_prg := pi)
    ; discharge_function =
        (fun _ ->
          close "section";
          None )
    ; classify_function =
        (fun _ ->
          close "module";
          Dispose ) }

let map_replace k v m =
  ProgMap.add k (CEphemeron.create v) (ProgMap.remove k m)

let progmap_remove prg =
  Lib.add_anonymous_leaf (input (ProgMap.remove prg.prg_name !from_prg))

let progmap_add n prg =
  Lib.add_anonymous_leaf (input (ProgMap.add n prg !from_prg))

let progmap_replace prg' =
  Lib.add_anonymous_leaf (input (map_replace prg'.prg_name prg' !from_prg))

let obligations_solved prg = Int.equal (snd prg.prg_obligations) 0

let obligations_message rem =
  if rem > 0 then
    if Int.equal rem 1 then
      Flags.if_verbose Feedback.msg_info
        Pp.(int rem ++ str " obligation remaining")
    else
      Flags.if_verbose Feedback.msg_info
        Pp.(int rem ++ str " obligations remaining")
  else
    Flags.if_verbose Feedback.msg_info Pp.(str "No more obligations remaining")

type progress = Remain of int | Dependent | Defined of GlobRef.t

let get_obligation_body expand obl =
  match obl.obl_body with
  | None -> None
  | Some c -> (
    if expand && snd obl.obl_status == Evar_kinds.Expand then
      match c with
      | DefinedObl pc -> Some (constant_value_in (Global.env ()) pc)
      | TermObl c -> Some c
    else
      match c with DefinedObl pc -> Some (mkConstU pc) | TermObl c -> Some c )

let obl_substitution expand obls deps =
  Int.Set.fold
    (fun x acc ->
      let xobl = obls.(x) in
      match get_obligation_body expand xobl with
      | None -> acc
      | Some oblb -> (xobl.obl_name, (xobl.obl_type, oblb)) :: acc )
    deps []

let rec intset_to = function
  | -1 -> Int.Set.empty
  | n -> Int.Set.add n (intset_to (pred n))

let obligation_substitution expand prg =
  let obls, _ = prg.prg_obligations in
  let ints = intset_to (pred (Array.length obls)) in
  obl_substitution expand obls ints

let hide_obligation () =
  Coqlib.check_required_library ["Coq"; "Program"; "Tactics"];
  UnivGen.constr_of_monomorphic_global
    (Coqlib.lib_ref "program.tactics.obligation")

(* XXX: Is this the right place? *)
let rec prod_app t n =
  match
    Constr.kind
      (EConstr.Unsafe.to_constr
         (Termops.strip_outer_cast Evd.empty (EConstr.of_constr t)))
    (* FIXME *)
  with
  | Prod (_, _, b) -> subst1 n b
  | LetIn (_, b, t, b') -> prod_app (subst1 b b') n
  | _ ->
    CErrors.user_err ~hdr:"prod_app"
      Pp.(str "Needed a product, but didn't find one" ++ fnl ())

(* prod_appvect T [| a1 ; ... ; an |] -> (T a1 ... an) *)
let prod_applist t nL = List.fold_left prod_app t nL

let replace_appvars subst =
  let rec aux c =
    let f, l = decompose_app c in
    if isVar f then
      try
        let c' = List.map (Constr.map aux) l in
        let t, b = Id.List.assoc (destVar f) subst in
        mkApp
          ( delayed_force hide_obligation
          , [|prod_applist t c'; Term.applistc b c'|] )
      with Not_found -> Constr.map aux c
    else Constr.map aux c
  in
  Constr.map aux

let subst_prog subst prg =
  if get_hide_obligations () then
    ( replace_appvars subst prg.prg_body
    , replace_appvars subst (* Termops.refresh_universes *) prg.prg_type )
  else
    let subst' = List.map (fun (n, (_, b)) -> (n, b)) subst in
    ( Vars.replace_vars subst' prg.prg_body
    , Vars.replace_vars subst' (* Termops.refresh_universes *) prg.prg_type )

let get_fix_exn, stm_get_fix_exn = Hook.make ()

let declare_definition prg =
  let varsubst = obligation_substitution true prg in
  let body, typ = subst_prog varsubst prg in
  let nf =
    UnivSubst.nf_evars_and_universes_opt_subst
      (fun x -> None)
      (UState.subst prg.prg_ctx)
  in
  let opaque = prg.prg_opaque in
  let fix_exn = Hook.get get_fix_exn () in
  let typ = nf typ in
  let body = nf body in
  let obls = List.map (fun (id, (_, c)) -> (id, nf c)) varsubst in
  let uvars =
    Univ.LSet.union
      (Vars.universes_of_constr typ)
      (Vars.universes_of_constr body)
  in
  let uctx = UState.restrict prg.prg_ctx uvars in
  let univs =
    UState.check_univ_decl ~poly:prg.prg_poly uctx prg.prg_univdecl
  in
  let ce = Declare.definition_entry ~fix_exn ~opaque ~types:typ ~univs body in
  let () = progmap_remove prg in
  let ubinders = UState.universe_binders uctx in
  let hook_data = Option.map (fun hook -> hook, uctx, obls) prg.prg_hook in
  DeclareDef.declare_definition
    ~name:prg.prg_name ~scope:prg.prg_scope ubinders ~kind:prg.prg_kind ce
    prg.prg_implicits ?hook_data

let rec lam_index n t acc =
  match Constr.kind t with
  | Lambda ({binder_name=Name n'}, _, _) when Id.equal n n' -> acc
  | Lambda (_, _, b) -> lam_index n b (succ acc)
  | _ -> raise Not_found

let compute_possible_guardness_evidences n fixbody fixtype =
  match n with
  | Some {CAst.loc; v = n} -> [lam_index n fixbody 0]
  | None ->
    (* If recursive argument was not given by user, we try all args.
         An earlier approach was to look only for inductive arguments,
         but doing it properly involves delta-reduction, and it finally
         doesn't seem to worth the effort (except for huge mutual
         fixpoints ?) *)
    let m =
      Termops.nb_prod Evd.empty (EConstr.of_constr fixtype)
      (* FIXME *)
    in
    let ctx = fst (Term.decompose_prod_n_assum m fixtype) in
    List.map_i (fun i _ -> i) 0 ctx

let mk_proof c =
  ((c, Univ.ContextSet.empty), Evd.empty_side_effects)

let declare_mutual_definition l =
  let len = List.length l in
  let first = List.hd l in
  let defobl x =
    let oblsubst = obligation_substitution true x in
    let subs, typ = subst_prog oblsubst x in
    let env = Global.env () in
    let sigma = Evd.from_ctx x.prg_ctx in
    let r = Retyping.relevance_of_type env sigma (EConstr.of_constr typ) in
    let term = snd (Reductionops.splay_lam_n env sigma len (EConstr.of_constr subs)) in
    let typ = snd (Reductionops.splay_prod_n env sigma len (EConstr.of_constr typ)) in
    let term = EConstr.to_constr sigma term in
    let typ = EConstr.to_constr sigma typ in
    let def = (x.prg_reduce term, r, x.prg_reduce typ, x.prg_implicits) in
    let oblsubst = List.map (fun (id, (_, c)) -> (id, c)) oblsubst in
    def, oblsubst
  in
  let defs, obls =
    List.fold_right (fun x (defs, obls) ->
        let xdef, xobls = defobl x in
        (xdef :: defs, xobls @ obls)) l ([], [])
  in
  (*   let fixdefs = List.map reduce_fix fixdefs in *)
  let fixdefs, fixrs,fixtypes, fiximps = List.split4 defs in
  let fixkind = Option.get first.prg_fixkind in
  let arrrec, recvec = (Array.of_list fixtypes, Array.of_list fixdefs) in
  let rvec = Array.of_list fixrs in
  let namevec = Array.of_list (List.map (fun x -> Name x.prg_name) l) in
  let fixdecls = (Array.map2 make_annot namevec rvec, arrrec, recvec) in
  let fixnames = first.prg_deps in
  let opaque = first.prg_opaque in
  let kind = if fixkind != IsCoFixpoint then Fixpoint else CoFixpoint in
  let indexes, fixdecls =
    match fixkind with
    | IsFixpoint wfl ->
      let possible_indexes =
        List.map3 compute_possible_guardness_evidences wfl fixdefs fixtypes
      in
      let indexes =
        Pretyping.search_guard (Global.env ()) possible_indexes fixdecls
      in
      ( Some indexes
      , List.map_i (fun i _ -> mk_proof (mkFix ((indexes, i), fixdecls))) 0 l
      )
    | IsCoFixpoint ->
      (None, List.map_i (fun i _ -> mk_proof (mkCoFix (i, fixdecls))) 0 l)
  in
  (* Declare the recursive definitions *)
  let poly = first.prg_poly in
  let scope = first.prg_scope in
  let univs = UState.univ_entry ~poly first.prg_ctx in
  let fix_exn = Hook.get get_fix_exn () in
  let kns =
    List.map4
      (fun name -> DeclareDef.declare_fix ~name ~opaque ~scope ~kind
          UnivNames.empty_binders univs)
      fixnames fixdecls fixtypes fiximps
  in
  (* Declare notations *)
  List.iter
    (Metasyntax.add_notation_interpretation (Global.env ()))
    first.prg_notations;
  Declare.recursive_message (fixkind != IsCoFixpoint) indexes fixnames;
  let dref = List.hd kns in
  DeclareDef.Hook.(call ?hook:first.prg_hook ~fix_exn { S.uctx = first.prg_ctx; obls; scope; dref });
  List.iter progmap_remove l;
  dref

let update_obls prg obls rem =
  let prg' = {prg with prg_obligations = (obls, rem)} in
  progmap_replace prg';
  obligations_message rem;
  if rem > 0 then Remain rem
  else
    match prg'.prg_deps with
    | [] ->
      let kn = declare_definition prg' in
      progmap_remove prg';
      Defined kn
    | l ->
      let progs =
        List.map
          (fun x -> CEphemeron.get (ProgMap.find x !from_prg))
          prg'.prg_deps
      in
      if List.for_all (fun x -> obligations_solved x) progs then
        let kn = declare_mutual_definition progs in
        Defined kn
      else Dependent

let dependencies obls n =
  let res = ref Int.Set.empty in
  Array.iteri
    (fun i obl ->
      if (not (Int.equal i n)) && Int.Set.mem n obl.obl_deps then
        res := Int.Set.add i !res )
    obls;
  !res

type obligation_qed_info =
  { name : Id.t
  ; num : int
  ; auto : Id.t option -> Int.Set.t -> unit Proofview.tactic option -> progress
  }

let obligation_terminator entries uctx { name; num; auto } =
  let open Proof_global in
  match entries with
  | [entry] ->
    let env = Global.env () in
    let ty = entry.proof_entry_type in
    let body, eff = Future.force entry.proof_entry_body in
    let (body, cstr) = Safe_typing.inline_private_constants env (body, eff.Evd.seff_private) in
    let sigma = Evd.from_ctx uctx in
    let sigma = Evd.merge_context_set ~sideff:true Evd.univ_rigid sigma cstr in
    Inductiveops.control_only_guard (Global.env ()) sigma (EConstr.of_constr body);
    (* Declare the obligation ourselves and drop the hook *)
    let prg = CEphemeron.get (ProgMap.find name !from_prg) in
    (* Ensure universes are substituted properly in body and type *)
    let body = EConstr.to_constr sigma (EConstr.of_constr body) in
    let ty = Option.map (fun x -> EConstr.to_constr sigma (EConstr.of_constr x)) ty in
    let ctx = Evd.evar_universe_context sigma in
    let obls, rem = prg.prg_obligations in
    let obl = obls.(num) in
    let status =
      match obl.obl_status, entry.proof_entry_opaque with
      | (_, Evar_kinds.Expand), true -> err_not_transp ()
      | (true, _), true -> err_not_transp ()
      | (false, _), true -> Evar_kinds.Define true
      | (_, Evar_kinds.Define true), false ->
        Evar_kinds.Define false
      | (_, status), false -> status
    in
    let obl = { obl with obl_status = false, status } in
    let ctx =
      if prg.prg_poly then ctx
      else UState.union prg.prg_ctx ctx
    in
    let uctx = UState.univ_entry ~poly:prg.prg_poly ctx in
    let (defined, obl) = declare_obligation prg obl body ty uctx in
    let obls = Array.copy obls in
    let () = obls.(num) <- obl in
    let prg_ctx =
      if prg.prg_poly then (* Polymorphic *)
        (* We merge the new universes and constraints of the
           polymorphic obligation with the existing ones *)
        UState.union prg.prg_ctx ctx
      else
        (* The first obligation, if defined,
           declares the univs of the constant,
           each subsequent obligation declares its own additional
           universes and constraints if any *)
        if defined then UState.make (Global.universes ())
        else ctx
    in
    let prg = {prg with prg_ctx} in
    begin try
      ignore (update_obls prg obls (pred rem));
      if pred rem > 0 then
        let deps = dependencies obls num in
        if not (Int.Set.is_empty deps) then
          ignore (auto (Some name) deps None)
    with e when CErrors.noncritical e ->
      let e = CErrors.push e in
      pperror (CErrors.iprint (ExplainErr.process_vernac_interp_error e))
    end
  | _ ->
    CErrors.anomaly
      Pp.(
        str
          "[obligation_terminator] close_proof returned more than one proof \
           term")
