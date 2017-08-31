(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Jacek Chrzaszcz, Aug 2002 as part of the implementation of
   the Coq module system *)

(* This module provides the main entry points for type-checking basic
   declarations *)

open CErrors
open Util
open Names
open Constr
open Declarations
open Environ
open Entries
open Typeops

module NamedDecl = Context.Named.Declaration

(* Insertion of constants and parameters in environment. *)

let equal_eff e1 e2 =
  let open Entries in
  match e1, e2 with
  | { eff = SEsubproof (c1,_,_) }, { eff = SEsubproof (c2,_,_) } ->
        Names.Constant.equal c1 c2
  | { eff = SEscheme (cl1,_) }, { eff = SEscheme (cl2,_) } ->
        CList.for_all2eq
          (fun (_,c1,_,_) (_,c2,_,_) -> Names.Constant.equal c1 c2)
          cl1 cl2
  | _ -> false

module SideEffects :
sig
  type t
  val repr : t -> side_effect list
  val empty : t
  val add : side_effect -> t -> t
  val concat : t -> t -> t
end =
struct

let compare_seff e1 e2 = match e1, e2 with
| SEsubproof (c1, _, _), SEsubproof (c2, _, _) -> Constant.CanOrd.compare c1 c2
| SEscheme (cl1, _), SEscheme (cl2, _) ->
  let cmp (_, c1, _, _) (_, c2, _, _) = Constant.CanOrd.compare c1 c2 in
  CList.compare cmp cl1 cl2
| SEsubproof _, SEscheme _ -> -1
| SEscheme _, SEsubproof _ -> 1

module SeffOrd = struct
type t = side_effect
let compare e1 e2 = compare_seff e1.eff e2.eff
end

module SeffSet = Set.Make(SeffOrd)

type t = { seff : side_effect list; elts : SeffSet.t }
(** Invariant: [seff] is a permutation of the elements of [elts] *)

let repr eff = eff.seff
let empty = { seff = []; elts = SeffSet.empty }
let add x es =
  if SeffSet.mem x es.elts then es
  else { seff = x :: es.seff; elts = SeffSet.add x es.elts }
let concat xes yes =
  List.fold_right add xes.seff yes

end

type side_effects = SideEffects.t

type _ trust =
| Pure : unit trust
| SideEffects : structure_body -> side_effects trust

let uniq_seff_rev = SideEffects.repr
let uniq_seff l = List.rev (SideEffects.repr l)

let empty_seff = SideEffects.empty
let add_seff = SideEffects.add
let concat_seff = SideEffects.concat

let mk_pure_proof c = (c, Univ.ContextSet.empty), empty_seff

let inline_side_effects env body ctx side_eff =
  (** First step: remove the constants that are still in the environment *)
  let filter { eff = se; from_env = mb } =
    let cbl = match se with
    | SEsubproof (c, cb, b) -> [c, cb, b]
    | SEscheme (cl,_) ->
      List.map (fun (_, c, cb, b) -> c, cb, b) cl
    in
    let not_exists (c,_,_) =
      try ignore(Environ.lookup_constant c env); false
      with Not_found -> true in 
    let cbl = List.filter not_exists cbl in
    (cbl, mb)
  in
  (* CAVEAT: we assure that most recent effects come first *)
  let side_eff = List.map filter (uniq_seff_rev side_eff) in
  let sigs = List.rev_map (fun (cbl, mb) -> mb, List.length cbl) side_eff in
  let side_eff = List.fold_left (fun accu (cbl, _) -> cbl @ accu) [] side_eff in
  let side_eff = List.rev side_eff in
  (** Most recent side-effects first in side_eff *)
  if List.is_empty side_eff then (body, ctx, sigs)
  else
    (** Second step: compute the lifts and substitutions to apply *)
    let cname c =
      let name = Constant.to_string c in
      let map c = if c == '.' || c == '#' then '_' else c in
      let name = String.map map name in
      Name (Id.of_string name)
    in
    let fold (subst, var, ctx, args) (c, cb, b) =
      let (b, opaque) = match cb.const_body, b with
      | Def b, _ -> (Mod_subst.force_constr b, false)
      | OpaqueDef _, `Opaque (b,_) -> (b, true)
      | _ -> assert false
      in
      match cb.const_universes with
      | Monomorphic_const univs ->
        (** Abstract over the term at the top of the proof *)
        let ty = cb.const_type in
        let subst = Cmap_env.add c (Inr var) subst in
        let ctx = Univ.ContextSet.union ctx univs in
        (subst, var + 1, ctx, (cname c, b, ty, opaque) :: args)
      | Polymorphic_const auctx ->
        (** Inline the term to emulate universe polymorphism *)
        let subst = Cmap_env.add c (Inl b) subst in
        (subst, var, ctx, args)
    in
    let (subst, len, ctx, args) = List.fold_left fold (Cmap_env.empty, 1, ctx, []) side_eff in
    (** Third step: inline the definitions *)
    let rec subst_const i k t = match Constr.kind t with
    | Const (c, u) ->
      let data = try Some (Cmap_env.find c subst) with Not_found -> None in
      begin match data with
      | None -> t
      | Some (Inl b) ->
        (** [b] is closed but may refer to other constants *)
        subst_const i k (Vars.subst_instance_constr u b)
      | Some (Inr n) ->
        mkRel (k + n - i)
      end
    | Rel n ->
      (** Lift free rel variables *)
      if n <= k then t
      else mkRel (n + len - i - 1)
    | _ -> Constr.map_with_binders ((+) 1) (fun k t -> subst_const i k t) k t
    in
    let map_args i (na, b, ty, opaque) =
      (** Both the type and the body may mention other constants *)
      let ty = subst_const (len - i - 1) 0 ty in
      let b = subst_const (len - i - 1) 0 b in
      (na, b, ty, opaque)
    in
    let args = List.mapi map_args args in
    let body = subst_const 0 0 body in
    let fold_arg (na, b, ty, opaque) accu =
      if opaque then mkApp (mkLambda (na, ty, accu), [|b|])
      else mkLetIn (na, b, ty, accu)
    in
    let body = List.fold_right fold_arg args body in
    (body, ctx, sigs)

let rec is_nth_suffix n l suf =
  if Int.equal n 0 then l == suf
  else match l with
  | [] -> false
  | _ :: l -> is_nth_suffix (pred n) l suf

(* Given the list of signatures of side effects, checks if they match.
 * I.e. if they are ordered descendants of the current revstruct.
   Returns the number of effects that can be trusted. *)
let check_signatures curmb sl =
  let is_direct_ancestor accu (mb, how_many) =
    match accu with
    | None -> None
    | Some (n, curmb) ->
        try
          let mb = CEphemeron.get mb in
          if is_nth_suffix how_many mb curmb
          then Some (n + how_many, mb)
          else None
        with CEphemeron.InvalidKey -> None in
  let sl = List.fold_left is_direct_ancestor (Some (0, curmb)) sl in
  match sl with
  | None -> 0
  | Some (n, _) -> n

let skip_trusted_seff sl b e =
  let rec aux sl b e acc =
    let open Context.Rel.Declaration in
    if Int.equal sl 0 then b, e, acc
    else match kind b with
    | LetIn (n,c,ty,bo) ->
       aux (sl - 1) bo
         (Environ.push_rel (LocalDef (n,c,ty)) e) (`Let(n,c,ty)::acc)
    | App(hd,arg) ->
       begin match kind hd with
       | Lambda (n,ty,bo) ->
           aux (sl - 1) bo
             (Environ.push_rel (LocalAssum (n,ty)) e) (`Cut(n,ty,arg)::acc)
       | _ -> assert false
       end
    | _ -> assert false
    in
  aux sl b e []

let rec unzip ctx j =
  match ctx with
  | [] -> j
  | `Let (n,c,ty) :: ctx ->
      unzip ctx { j with uj_val = mkLetIn (n,c,ty,j.uj_val) }
  | `Cut (n,ty,arg) :: ctx ->
      unzip ctx { j with uj_val = mkApp (mkLambda (n,ty,j.uj_val),arg) }

let feedback_completion_typecheck =
  Option.iter (fun state_id ->
      Feedback.feedback ~id:state_id Feedback.Complete)

let abstract_constant_universes = function
  | Monomorphic_const_entry uctx ->
    Univ.empty_level_subst, Monomorphic_const uctx
  | Polymorphic_const_entry uctx ->
    let sbst, auctx = Univ.abstract_universes uctx in
    let sbst = Univ.make_instance_subst sbst in
    sbst, Polymorphic_const auctx

let infer_declaration (type a) ~(trust : a trust) env (dcl : a constant_entry) =
  match dcl with
    | ParameterEntry (ctx,(t,uctx),nl) ->
      let env = match uctx with
        | Monomorphic_const_entry uctx -> push_context_set ~strict:true uctx env
        | Polymorphic_const_entry uctx -> push_context ~strict:false uctx env
      in
      let j = infer env t in
      let usubst, univs = abstract_constant_universes uctx in
      let c = Typeops.assumption_of_judgment env j in
      let t = Constr.hcons (Vars.subst_univs_level_constr usubst c) in
      {
        Cooking.cook_body = Undef nl;
        cook_type = t;
        cook_universes = univs;
        cook_inline = false;
        cook_context = ctx;
      }

  (** Definition [c] is opaque (Qed), non polymorphic and with a specified type,
      so we delay the typing and hash consing of its body.
      Remark: when the universe quantification is given explicitly, we could
      delay even in the polymorphic case.  *)
  | DefinitionEntry ({ const_entry_type = Some typ;
                       const_entry_opaque = true;
		       const_entry_universes = Monomorphic_const_entry univs } as c) ->
      let env = push_context_set ~strict:true univs env in
      let { const_entry_body = body; const_entry_feedback = feedback_id } = c in
      let tyj = infer_type env typ in
      let proofterm =
        Future.chain body (fun ((body,uctx),side_eff) ->
          let j, uctx = match trust with
          | Pure ->
            let env = push_context_set uctx env in
            let j = infer env body in
            let _ = judge_of_cast env j DEFAULTcast tyj in
            j, uctx
          | SideEffects mb ->
            let (body, uctx, signatures) = inline_side_effects env body uctx side_eff in
            let valid_signatures = check_signatures mb signatures in
            let env = push_context_set uctx env in
            let body,env,ectx = skip_trusted_seff valid_signatures body env in
            let j = infer env body in
            let j = unzip ectx j in
            let _ = judge_of_cast env j DEFAULTcast tyj in
            j, uctx
          in
          let c = Constr.hcons j.uj_val in
          feedback_completion_typecheck feedback_id;
          c, uctx) in
      let def = OpaqueDef (Opaqueproof.create proofterm) in
      {
        Cooking.cook_body = def;
        cook_type = typ;
        cook_universes = Monomorphic_const univs;
        cook_inline = c.const_entry_inline_code;
        cook_context = c.const_entry_secctx;
      }

  (** Other definitions have to be processed immediately. *)
  | DefinitionEntry c ->
      let { const_entry_type = typ; const_entry_opaque = opaque } = c in
      let { const_entry_body = body; const_entry_feedback = feedback_id } = c in
      let (body, ctx), side_eff = Future.join body in
      let body, ctx, _ = match trust with
      | Pure -> body, ctx, []
      | SideEffects _ -> inline_side_effects env body ctx side_eff
      in
      let env, usubst, univs = match c.const_entry_universes with
      | Monomorphic_const_entry univs ->
        let ctx = Univ.ContextSet.union univs ctx in
        let env = push_context_set ~strict:true ctx env in
        env, Univ.empty_level_subst, Monomorphic_const ctx
      | Polymorphic_const_entry uctx ->
        (** Ensure not to generate internal constraints in polymorphic mode.
            The only way for this to happen would be that either the body
            contained deferred universes, or that it contains monomorphic
            side-effects. The first property is ruled out by upper layers,
            and the second one is ensured by the fact we currently
            unconditionally export side-effects from polymorphic definitions,
            i.e. [trust] is always [Pure]. *)
        let () = assert (Univ.ContextSet.is_empty ctx) in
        let env = push_context ~strict:false uctx env in
        let sbst, auctx = Univ.abstract_universes uctx in
        let sbst = Univ.make_instance_subst sbst in
        env, sbst, Polymorphic_const auctx
      in
      let j = infer env body in
      let typ = match typ with
        | None ->
          Vars.subst_univs_level_constr usubst j.uj_type
        | Some t ->
           let tj = infer_type env t in
           let _ = judge_of_cast env j DEFAULTcast tj in
           Vars.subst_univs_level_constr usubst t
      in
      let def = Constr.hcons (Vars.subst_univs_level_constr usubst j.uj_val) in
      let def = 
	if opaque then OpaqueDef (Opaqueproof.create (Future.from_val (def, Univ.ContextSet.empty)))
	else Def (Mod_subst.from_val def) 
      in
	feedback_completion_typecheck feedback_id;
      {
        Cooking.cook_body = def;
        cook_type = typ;
        cook_universes = univs;
        cook_inline = c.const_entry_inline_code;
        cook_context = c.const_entry_secctx;
      }

let record_aux env s_ty s_bo =
  let in_ty = keep_hyps env s_ty in
  let v =
    String.concat " "
      (CList.map_filter (fun decl ->
          let id = NamedDecl.get_id decl in
          if List.exists (NamedDecl.get_id %> Id.equal id) in_ty then None
          else Some (Id.to_string id))
        (keep_hyps env s_bo)) in
  Aux_file.record_in_aux "context_used" v

let build_constant_declaration kn env result =
  let open Cooking in
  let typ = result.cook_type in
  let check declared inferred =
    let mk_set l = List.fold_right Id.Set.add (List.map NamedDecl.get_id l) Id.Set.empty in
    let inferred_set, declared_set = mk_set inferred, mk_set declared in
    if not (Id.Set.subset inferred_set declared_set) then
      let l = Id.Set.elements (Id.Set.diff inferred_set declared_set) in
      let n = List.length l in
      let declared_vars = Pp.pr_sequence Id.print (Id.Set.elements declared_set) in
      let inferred_vars = Pp.pr_sequence Id.print (Id.Set.elements inferred_set) in
      let missing_vars  = Pp.pr_sequence Id.print (List.rev l) in
      user_err Pp.(prlist str
         ["The following section "; (String.plural n "variable"); " ";
          (String.conjugate_verb_to_be n); " used but not declared:"] ++ fnl () ++
         missing_vars ++ str "." ++ fnl () ++ fnl () ++
         str "You can either update your proof to not depend on " ++ missing_vars ++
         str ", or you can update your Proof line from" ++ fnl () ++
         str "Proof using " ++ declared_vars ++ fnl () ++
         str "to" ++ fnl () ++
         str "Proof using " ++ inferred_vars) in
  let sort evn l =
    List.filter (fun decl ->
      let id = NamedDecl.get_id decl in
      List.exists (NamedDecl.get_id %> Names.Id.equal id) l)
    (named_context env) in
  (* We try to postpone the computation of used section variables *)
  let hyps, def =
    let context_ids = List.map NamedDecl.get_id (named_context env) in
    let def = result.cook_body in
    match result.cook_context with
    | None when not (List.is_empty context_ids) -> 
        (* No declared section vars, and non-empty section context:
           we must look at the body NOW, if any *)
        let ids_typ = global_vars_set env typ in
        let ids_def = match def with
        | Undef _ -> Id.Set.empty
        | Def cs -> global_vars_set env (Mod_subst.force_constr cs)
        | OpaqueDef lc ->
            let vars =
              global_vars_set env
                (Opaqueproof.force_proof (opaque_tables env) lc) in
            (* we force so that cst are added to the env immediately after *)
            ignore(Opaqueproof.force_constraints (opaque_tables env) lc);
            if !Flags.record_aux_file then record_aux env ids_typ vars;
            vars
        in
        keep_hyps env (Id.Set.union ids_typ ids_def), def
    | None ->
        if !Flags.record_aux_file then
          record_aux env Id.Set.empty Id.Set.empty;
        [], def (* Empty section context: no need to check *)
    | Some declared ->
        (* We use the declared set and chain a check of correctness *)
        sort env declared,
        match def with
        | Undef _ as x -> x (* nothing to check *)
        | Def cs as x ->
            let ids_typ = global_vars_set env typ in
            let ids_def = global_vars_set env (Mod_subst.force_constr cs) in
            let inferred = keep_hyps env (Id.Set.union ids_typ ids_def) in
            check declared inferred;
            x
        | OpaqueDef lc -> (* In this case we can postpone the check *)
            OpaqueDef (Opaqueproof.iter_direct_opaque (fun c ->
              let ids_typ = global_vars_set env typ in
              let ids_def = global_vars_set env c in
              let inferred = keep_hyps env (Id.Set.union ids_typ ids_def) in
              check declared inferred) lc) in
  let univs = result.cook_universes in
  let tps = 
    let res = Cbytegen.compile_constant_body ~fail_on_error:false env univs def in
    Option.map Cemitcodes.from_val res
  in
  { const_hyps = hyps;
    const_body = def;
    const_type = typ;
    const_body_code = tps;
    const_universes = univs;
    const_inline_code = result.cook_inline;
    const_typing_flags = Environ.typing_flags env }

(*s Global and local constant declaration. *)

let translate_constant mb env kn ce =
  build_constant_declaration kn env
    (infer_declaration ~trust:mb env ce)

let constant_entry_of_side_effect cb u =
  let univs =
    match cb.const_universes with
    | Monomorphic_const uctx ->
      Monomorphic_const_entry uctx
    | Polymorphic_const auctx -> 
      Polymorphic_const_entry (Univ.AUContext.repr auctx)
  in
  let pt =
    match cb.const_body, u with
    | OpaqueDef _, `Opaque (b, c) -> b, c
    | Def b, `Nothing -> Mod_subst.force_constr b, Univ.ContextSet.empty
    | _ -> assert false in
  DefinitionEntry {
    const_entry_body = Future.from_val (pt, ());
    const_entry_secctx = None;
    const_entry_feedback = None;
    const_entry_type = Some cb.const_type;
    const_entry_universes = univs;
    const_entry_opaque = Declareops.is_opaque cb;
    const_entry_inline_code = cb.const_inline_code }
;;

let turn_direct (kn,cb,u,r as orig) =
  match cb.const_body, u with
  | OpaqueDef _, `Opaque (b,c) ->
      let pt = Future.from_val (b,c) in
      kn, { cb with const_body = OpaqueDef (Opaqueproof.create pt) }, u, r
   | _ -> orig
;;

type side_effect_role =
  | Subproof
  | Schema of inductive * string

type exported_side_effect = 
  Constant.t * constant_body * side_effect_role

let export_side_effects mb env c =
      let { const_entry_body = body } = c in
      let _, eff = Future.force body in
      let ce = { c with
        const_entry_body = Future.chain body
          (fun (b_ctx, _) -> b_ctx, ()) } in
      let not_exists (c,_,_,_) =
        try ignore(Environ.lookup_constant c env); false
        with Not_found -> true in 
      let aux (acc,sl) { eff = se; from_env = mb } =
        let cbl = match se with
          | SEsubproof (c,cb,b) -> [c,cb,b,Subproof]
          | SEscheme (cl,k) ->
              List.map (fun (i,c,cb,b) -> c,cb,b,Schema(i,k)) cl in
        let cbl = List.filter not_exists cbl in
        if cbl = [] then acc, sl
        else cbl :: acc, (mb,List.length cbl) :: sl in
      let seff, signatures = List.fold_left aux ([],[]) (uniq_seff_rev eff) in
      let trusted = check_signatures mb signatures in
      let push_seff env = function
        | kn, cb, `Nothing, _ ->
          begin
            let env = Environ.add_constant kn cb env in
            match cb.const_universes with
            | Monomorphic_const ctx ->
              Environ.push_context_set ~strict:true ctx env
            | Polymorphic_const _ -> env
          end
        | kn, cb, `Opaque(_, ctx), _ ->
          begin
            let env = Environ.add_constant kn cb env in
            match cb.const_universes with
            | Monomorphic_const cstctx ->
              let env = Environ.push_context_set ~strict:true cstctx env in
              Environ.push_context_set ~strict:true ctx env
            | Polymorphic_const _ -> env
          end
      in
      let rec translate_seff sl seff acc env =
        match seff with
        | [] -> List.rev acc, ce
        | cbs :: rest ->
          if Int.equal sl 0 then
           let env, cbs =
             List.fold_left (fun (env,cbs) (kn, ocb, u, r) ->
               let ce = constant_entry_of_side_effect ocb u in
               let cb = translate_constant Pure env kn ce in
               (push_seff env (kn, cb,`Nothing, Subproof),(kn,cb,r) :: cbs)) 
             (env,[]) cbs in
           translate_seff 0 rest (cbs @ acc) env
          else
           let cbs_len = List.length cbs in
           let cbs = List.map turn_direct cbs in
           let env = List.fold_left push_seff env cbs in
           let ecbs = List.map (fun (kn,cb,u,r) ->
             kn, cb, r) cbs in
           translate_seff (sl - cbs_len) rest (ecbs @ acc) env
     in
       translate_seff trusted seff [] env
;;

let translate_local_assum env t =
  let j = infer env t in
  let t = Typeops.assumption_of_judgment env j in
    t

let translate_recipe env kn r =
  (** We only hashcons the term when outside of a section, otherwise this would
      be useless. It is detected by the dirpath of the constant being empty. *)
  let (_, dir, _) = Constant.repr3 kn in
  let hcons = DirPath.is_empty dir in
  build_constant_declaration kn env (Cooking.cook_constant ~hcons r)

let translate_local_def env id centry =
  let open Cooking in
  let body = Future.from_val ((centry.secdef_body, Univ.ContextSet.empty), ()) in
  let centry = {
    const_entry_body = body;
    const_entry_secctx = centry.secdef_secctx;
    const_entry_feedback = centry.secdef_feedback;
    const_entry_type = centry.secdef_type;
    const_entry_universes = Monomorphic_const_entry Univ.ContextSet.empty;
    const_entry_opaque = false;
    const_entry_inline_code = false;
  } in
  let decl = infer_declaration ~trust:Pure env (DefinitionEntry centry) in
  let typ = decl.cook_type in
  if Option.is_empty decl.cook_context && !Flags.record_aux_file then begin
    match decl.cook_body with
    | Undef _ -> ()
    | Def _ -> ()
    | OpaqueDef lc ->
       let ids_typ = global_vars_set env typ in
       let ids_def = global_vars_set env
         (Opaqueproof.force_proof (opaque_tables env) lc) in
       record_aux env ids_typ ids_def
  end;
  let () = match decl.cook_universes with
  | Monomorphic_const ctx -> assert (Univ.ContextSet.is_empty ctx)
  | Polymorphic_const _ -> assert false
  in
  let c = match decl.cook_body with
  | Def c -> Mod_subst.force_constr c
  | OpaqueDef o ->
    let p = Opaqueproof.force_proof (Environ.opaque_tables env) o in
    let cst = Opaqueproof.force_constraints (Environ.opaque_tables env) o in
    (** Let definitions are ensured to have no extra constraints coming from
        the body by virtue of the typing of [Entries.section_def_entry]. *)
    let () = assert (Univ.ContextSet.is_empty cst) in
    p
  | Undef _ -> assert false
  in
  c, typ

(* Insertion of inductive types. *)

let translate_mind env kn mie = Indtypes.check_inductive env kn mie

let inline_entry_side_effects env ce = { ce with
  const_entry_body = Future.chain
    ce.const_entry_body (fun ((body, ctx), side_eff) ->
      let body, ctx',_ = inline_side_effects env body ctx side_eff in
      (body, ctx'), ());
}

let inline_side_effects env body side_eff =
  pi1 (inline_side_effects env body Univ.ContextSet.empty side_eff)
