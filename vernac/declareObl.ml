(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
open Entries

type 'a obligation_body = DefinedObl of 'a | TermObl of constr

module Obligation = struct
  type t =
    { obl_name : Id.t
    ; obl_type : types
    ; obl_location : Evar_kinds.t Loc.located
    ; obl_body : pconstant obligation_body option
    ; obl_status : bool * Evar_kinds.obligation_definition_status
    ; obl_deps : Int.Set.t
    ; obl_tac : unit Proofview.tactic option }

  let set_type ~typ obl = { obl with obl_type = typ }
  let set_body ~body obl = { obl with obl_body = Some body }

end

type obligations =
  { obls : Obligation.t array
  ; remaining : int }

type fixpoint_kind =
  | IsFixpoint of lident option list
  | IsCoFixpoint

module ProgramDecl = struct

  type t =
    { prg_name : Id.t
    ; prg_body : constr
    ; prg_type : constr
    ; prg_ctx : UState.t
    ; prg_univdecl : UState.universe_decl
    ; prg_obligations : obligations
    ; prg_deps : Id.t list
    ; prg_fixkind : fixpoint_kind option
    ; prg_implicits : Impargs.manual_implicits
    ; prg_notations : Vernacexpr.decl_notation list
    ; prg_poly : bool
    ; prg_scope : DeclareDef.locality
    ; prg_kind : Decls.definition_object_kind
    ; prg_reduce : constr -> constr
    ; prg_hook : DeclareDef.Hook.t option
    ; prg_opaque : bool
    }

  open Obligation

  let make ?(opaque = false) ?hook n ~udecl ~uctx ~impargs
      ~poly ~scope ~kind b t deps fixkind notations obls reduce =
    let obls', b =
      match b with
      | None ->
        assert(Int.equal (Array.length obls) 0);
        let n = Nameops.add_suffix n "_obligation" in
        [| { obl_name = n; obl_body = None;
             obl_location = Loc.tag Evar_kinds.InternalHole; obl_type = t;
             obl_status = false, Evar_kinds.Expand; obl_deps = Int.Set.empty;
             obl_tac = None } |],
        mkVar n
      | Some b ->
        Array.mapi
          (fun i (n, t, l, o, d, tac) ->
             { obl_name = n ; obl_body = None;
               obl_location = l; obl_type = t; obl_status = o;
               obl_deps = d; obl_tac = tac })
          obls, b
    in
    let ctx = UState.make_flexible_nonalgebraic uctx in
    { prg_name = n
    ; prg_body = b
    ; prg_type = reduce t
    ; prg_ctx = ctx
    ; prg_univdecl = udecl
    ; prg_obligations = { obls = obls' ; remaining = Array.length obls' }
    ; prg_deps = deps
    ; prg_fixkind = fixkind
    ; prg_notations = notations
    ; prg_implicits = impargs
    ; prg_poly = poly
    ; prg_scope = scope
    ; prg_kind = kind
    ; prg_reduce = reduce
    ; prg_hook = hook
    ; prg_opaque = opaque
    }

  let set_uctx ~uctx prg = {prg with prg_ctx = uctx}
end

open Obligation
open ProgramDecl

(* Saving an obligation *)

let get_shrink_obligations =
  Goptions.declare_bool_option_and_ref ~depr:true (* remove in 8.8 *)
    ~key:["Shrink"; "Obligations"]
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

(***********************************************************************)
(* Saving an obligation                                                *)
(***********************************************************************)

let unfold_entry cst = Hints.HintsUnfoldEntry [EvalConstRef cst]

let add_hint local prg cst =
  let locality = if local then Goptions.OptLocal else Goptions.OptExport in
  Hints.add_hints ~locality [Id.to_string prg.prg_name] (unfold_entry cst)

(* true = hide obligations *)
let get_hide_obligations =
  Goptions.declare_bool_option_and_ref
    ~depr:false
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
    let ce = Declare.definition_entry ?types:ty ~opaque ~univs:uctx body in

    (* ppedrot: seems legit to have obligations as local *)
    let constant =
      Declare.declare_constant ~name:obl.obl_name
        ~local:Declare.ImportNeedQualified ~kind:Decls.(IsProof Property)
        (Declare.DefinitionEntry ce)
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

let check_can_close sec =
  if not (ProgMap.is_empty !from_prg) then
    let keys = map_keys !from_prg in
    CErrors.user_err ~hdr:"Program"
      Pp.(
        str "Unsolved obligations when closing "
        ++ Id.print sec ++ str ":" ++ spc ()
        ++ prlist_with_sep spc (fun x -> Id.print x) keys
        ++ ( str (if Int.equal (List.length keys) 1 then " has " else " have ")
           ++ str "unsolved obligations" ))

let map_replace k v m = ProgMap.add k (CEphemeron.create v) (ProgMap.remove k m)
let prgmap_op f = from_prg := f !from_prg
let progmap_remove prg = prgmap_op (ProgMap.remove prg.prg_name)
let progmap_add n prg = prgmap_op (ProgMap.add n prg)
let progmap_replace prg = prgmap_op (map_replace prg.prg_name prg)

let obligations_solved prg = Int.equal prg.prg_obligations.remaining 0

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
  let obls = prg.prg_obligations.obls in
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
  let ubind = UState.universe_binders uctx in
  let hook_data = Option.map (fun hook -> hook, uctx, obls) prg.prg_hook in
  DeclareDef.declare_definition
    ~name:prg.prg_name ~scope:prg.prg_scope ~ubind
    ~kind:Decls.(IsDefinition prg.prg_kind) ce
    ~impargs:prg.prg_implicits ?hook_data

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
  let fixdefs, fixrs, fixtypes, fixitems =
    List.fold_right2 (fun (d,r,typ,impargs) name (a1,a2,a3,a4) ->
        d :: a1, r :: a2, typ :: a3,
        DeclareDef.Recthm.{ name; typ; impargs; args = [] } :: a4
      ) defs first.prg_deps ([],[],[],[])
  in
  let fixkind = Option.get first.prg_fixkind in
  let arrrec, recvec = (Array.of_list fixtypes, Array.of_list fixdefs) in
  let rvec = Array.of_list fixrs in
  let namevec = Array.of_list (List.map (fun x -> Name x.prg_name) l) in
  let rec_declaration = (Array.map2 make_annot namevec rvec, arrrec, recvec) in
  let possible_indexes =
    match fixkind with
    | IsFixpoint wfl ->
      Some (List.map3 compute_possible_guardness_evidences wfl fixdefs fixtypes)
    | IsCoFixpoint -> None
  in
  (* In the future we will pack all this in a proper record *)
  let poly, scope, ntns, opaque = first.prg_poly, first.prg_scope, first.prg_notations, first.prg_opaque in
  let kind = if fixkind != IsCoFixpoint then Decls.(IsDefinition Fixpoint) else Decls.(IsDefinition CoFixpoint) in
  (* Declare the recursive definitions *)
  let udecl = UState.default_univ_decl in
  let kns =
    DeclareDef.declare_mutually_recursive ~scope ~opaque ~kind
      ~udecl ~ntns ~uctx:first.prg_ctx ~rec_declaration ~possible_indexes ~poly
      ~restrict_ucontext:false fixitems
  in
  (* Only for the first constant *)
  let dref = List.hd kns in
  DeclareDef.Hook.(call ?hook:first.prg_hook { S.uctx = first.prg_ctx; obls; scope; dref });
  List.iter progmap_remove l;
  dref

let update_obls prg obls rem =
  let prg_obligations = { obls; remaining = rem } in
  let prg' = {prg with prg_obligations} in
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

let update_program_decl_on_defined prg obls num obl ~uctx rem ~auto =
  let obls = Array.copy obls in
  let () = obls.(num) <- obl in
  let prg = { prg with prg_ctx = uctx } in
  let () = ignore (update_obls prg obls (pred rem)) in
  if pred rem > 0 then begin
    let deps = dependencies obls num in
    if not (Int.Set.is_empty deps) then
      ignore (auto (Some prg.prg_name) deps None)
  end

type obligation_qed_info =
  { name : Id.t
  ; num : int
  ; auto : Id.t option -> Int.Set.t -> unit Proofview.tactic option -> progress
  }

let obligation_terminator entries uctx { name; num; auto } =
  match entries with
  | [entry] ->
    let env = Global.env () in
    let ty = entry.Declare.proof_entry_type in
    let body, uctx = Declare.inline_private_constants ~uctx env entry in
    let sigma = Evd.from_ctx uctx in
    Inductiveops.control_only_guard (Global.env ()) sigma (EConstr.of_constr body);
    (* Declare the obligation ourselves and drop the hook *)
    let prg = CEphemeron.get (ProgMap.find name !from_prg) in
    (* Ensure universes are substituted properly in body and type *)
    let body = EConstr.to_constr sigma (EConstr.of_constr body) in
    let ty = Option.map (fun x -> EConstr.to_constr sigma (EConstr.of_constr x)) ty in
    let ctx = Evd.evar_universe_context sigma in
    let { obls; remaining=rem } = prg.prg_obligations in
    let obl = obls.(num) in
    let status =
      match obl.obl_status, entry.Declare.proof_entry_opaque with
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
        if defined then UState.make ~lbound:(Global.universes_lbound ()) (Global.universes ())
        else ctx
    in
    update_program_decl_on_defined prg obls num obl ~uctx:prg_ctx rem ~auto
  | _ ->
    CErrors.anomaly
      Pp.(
        str
          "[obligation_terminator] close_proof returned more than one proof \
           term")

(* Similar to the terminator but for interactive paths, as the
   terminator is only called in interactive proof mode *)
let obligation_hook prg obl num auto { DeclareDef.Hook.S.uctx = ctx'; dref; _ } =
  let { obls; remaining=rem } = prg.prg_obligations in
  let cst = match dref with GlobRef.ConstRef cst -> cst | _ -> assert false in
  let transparent = evaluable_constant cst (Global.env ()) in
  let () = match obl.obl_status with
      (true, Evar_kinds.Expand)
    | (true, Evar_kinds.Define true) ->
       if not transparent then err_not_transp ()
    | _ -> ()
  in
  let inst, ctx' =
    if not prg.prg_poly (* Not polymorphic *) then
      (* The universe context was declared globally, we continue
         from the new global environment. *)
      let ctx = UState.make ~lbound:(Global.universes_lbound ()) (Global.universes ()) in
      let ctx' = UState.merge_subst ctx (UState.subst ctx') in
      Univ.Instance.empty, ctx'
    else
      (* We get the right order somehow, but surely it could be enforced in a clearer way. *)
      let uctx = UState.context ctx' in
      Univ.UContext.instance uctx, ctx'
  in
  let obl = { obl with obl_body = Some (DefinedObl (cst, inst)) } in
  let () = if transparent then add_hint true prg cst in
  update_program_decl_on_defined prg obls num obl ~uctx:ctx' rem ~auto
