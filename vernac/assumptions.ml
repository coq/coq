(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* The following definitions are used by the function
   [assumptions] which gives as an output the set of all
   axioms and sections variables on which a given term depends
   in a context (expectingly the Global context) *)

(* Initial author: Arnaud Spiwack
   Module-traversing code: Pierre Letouzey *)

open Pp
open CErrors
open Util
open Names
open Constr
open Declarations
open Mod_subst
open Printer
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration

(** For a constant c in a module sealed by an interface (M:T and
    not M<:T), [Global.lookup_constant] may return a [constant_body]
    without body. We fix this by looking in the implementation
    of the module *)

let modcache = ref (MPmap.empty : structure_body MPmap.t)

let rec search_mod_label lab = function
  | [] -> raise Not_found
  | (l, SFBmodule mb) :: _ when Label.equal l lab -> mb
  | _ :: fields -> search_mod_label lab fields

let rec search_cst_label lab = function
  | [] -> raise Not_found
  | (l, SFBconst cb) :: _ when Label.equal l lab -> cb
  | _ :: fields -> search_cst_label lab fields

let rec search_mind_label lab = function
  | [] -> raise Not_found
  | (l, SFBmind mind) :: _ when Label.equal l lab -> mind
  | _ :: fields -> search_mind_label lab fields

(* TODO: using [empty_delta_resolver] below is probably slightly incorrect. But:
    a) I don't see currently what should be used instead
    b) this shouldn't be critical for Print Assumption. At worse some
       constants will have a canonical name which is non-canonical,
       leading to failures in [Global.lookup_constant], but our own
       [lookup_constant] should work.
*)

let rec fields_of_functor f subs mp0 args = function
  | NoFunctor a -> f subs mp0 args a
  | MoreFunctor (mbid,_,e) ->
    match args with
    | [] -> assert false (* we should only encounter applied functors *)
    | mpa :: args ->
      let subs = join (map_mbid mbid mpa empty_delta_resolver (*TODO*)) subs in
      fields_of_functor f subs mp0 args e

let rec lookup_module_in_impl mp =
    match mp with
    | MPfile _ -> Global.lookup_module mp
    | MPbound _ -> Global.lookup_module mp
    | MPdot (mp',lab') ->
       if ModPath.equal mp' (Global.current_modpath ()) then
         Global.lookup_module mp
       else
         let fields = memoize_fields_of_mp mp' in
         search_mod_label lab' fields

and memoize_fields_of_mp mp =
  try MPmap.find mp !modcache
  with Not_found ->
    let l = fields_of_mp mp in
    modcache := MPmap.add mp l !modcache;
    l

and fields_of_mp mp =
  let mb = lookup_module_in_impl mp in
  let fields,inner_mp,subs = fields_of_mb empty_subst mb [] in
  let subs =
    if ModPath.equal inner_mp mp then subs
    else add_mp inner_mp mp mb.mod_delta subs
  in
  Modops.subst_structure subs fields

and fields_of_mb subs mb args = match mb.mod_expr with
  | Algebraic expr -> fields_of_expression subs mb.mod_mp args expr
  | Struct sign -> fields_of_signature subs mb.mod_mp args sign
  | Abstract|FullStruct -> fields_of_signature subs mb.mod_mp args mb.mod_type

(** The Abstract case above corresponds to [Declare Module] *)

and fields_of_signature x =
  fields_of_functor
    (fun subs mp0 args struc ->
      assert (List.is_empty args);
      (struc, mp0, subs)) x

and fields_of_expr subs mp0 args = function
  | MEident mp ->
    let mb = lookup_module_in_impl (subst_mp subs mp) in
    fields_of_mb subs mb args
  | MEapply (me1,mp2) -> fields_of_expr subs mp0 (mp2::args) me1
  | MEwith _ -> assert false (* no 'with' in [mod_expr] *)

and fields_of_expression x = fields_of_functor fields_of_expr x

let lookup_constant_in_impl cst fallback =
  try
    let mp,lab = KerName.repr (Constant.canonical cst) in
    let fields = memoize_fields_of_mp mp in
    (* A module found this way is necessarily closed, in particular
       our constant cannot be in an opened section : *)
    search_cst_label lab fields
  with Not_found ->
    (* Either:
       - The module part of the constant isn't registered yet :
         we're still in it, so the [constant_body] found earlier
         (if any) was a true axiom.
       - The label has not been found in the structure. This is an error *)
    match fallback with
      | Some cb -> cb
      | None -> anomaly (str "Print Assumption: unknown constant " ++ Constant.print cst ++ str ".")

let lookup_constant cst =
  let env = Global.env() in
  if not (Environ.mem_constant cst env)
  then lookup_constant_in_impl cst None
  else
    let cb = Environ.lookup_constant cst env in
    if Declareops.constant_has_body cb then cb
    else lookup_constant_in_impl cst (Some cb)

let lookup_mind_in_impl mind =
  try
    let mp,lab = KerName.repr (MutInd.canonical mind) in
    let fields = memoize_fields_of_mp mp in
      search_mind_label lab fields
  with Not_found ->
    anomaly (str "Print Assumption: unknown inductive " ++ MutInd.print mind ++ str ".")

let lookup_mind mind =
  let env = Global.env() in
  if Environ.mem_mind mind env then Environ.lookup_mind mind env
  else lookup_mind_in_impl mind

(** Graph traversal of an object, collecting on the way the dependencies of
    traversed objects *)

let label_of = let open GlobRef in function
  | ConstRef kn -> Constant.label kn
  | IndRef (kn,_)
  | ConstructRef ((kn,_),_) -> MutInd.label kn
  | VarRef id -> Label.of_id id

let fold_with_full_binders g f n acc c =
  let open Context.Rel.Declaration in
  match kind c with
  | Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _ | Construct _  | Int _ | Float _ -> acc
  | Cast (c,_, t) -> f n (f n acc c) t
  | Prod (na,t,c) -> f (g (LocalAssum (na,t)) n) (f n acc t) c
  | Lambda (na,t,c) -> f (g (LocalAssum (na,t)) n) (f n acc t) c
  | LetIn (na,b,t,c) -> f (g (LocalDef (na,b,t)) n) (f n (f n acc b) t) c
  | App (c,l) -> Array.fold_left (f n) (f n acc c) l
  | Proj (_,c) -> f n acc c
  | Evar (_,l) -> List.fold_left (f n) acc l
  | Case (ci, u, pms, p, iv, c, bl) ->
    let mib = lookup_mind (fst ci.ci_ind) in
    let (ci, p, iv, c, bl) = Inductive.expand_case_specif mib (ci, u, pms, p, iv, c, bl) in
    Array.fold_left (f n) (f n (fold_invert (f n) (f n acc p) iv) c) bl
  | Fix (_,(lna,tl,bl)) ->
      let n' = CArray.fold_left2_i (fun i c n t -> g (LocalAssum (n,lift i t)) c) n lna tl in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd
  | CoFix (_,(lna,tl,bl)) ->
      let n' = CArray.fold_left2_i (fun i c n t -> g (LocalAssum (n,lift i t)) c) n lna tl in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd
  | Array(_u,t,def,ty) -> f n (f n (Array.fold_left (f n) acc t) def) ty

let get_constant_body kn =
  let cb = lookup_constant kn in
  let access = Library.indirect_accessor in
  match cb.const_body with
  | Undef _ | Primitive _ -> None
  | Def c -> Some c
  | OpaqueDef o ->
    match Global.force_proof access o with
    | c, _ -> Some c
    | exception _ -> None (* missing delayed body, e.g. in vok mode *)

let rec traverse current ctx accu t =
  let open GlobRef in
  match Constr.kind t with
| Var id ->
  let body () = id |> Global.lookup_named |> NamedDecl.get_value in
  traverse_object accu body (VarRef id)
| Const (kn, _) ->
  let body () = get_constant_body kn in
  traverse_object accu body (ConstRef kn)
| Ind ((mind, _) as ind, _) ->
  traverse_inductive accu mind (IndRef ind)
| Construct (((mind, _), _) as cst, _) ->
  traverse_inductive accu mind (ConstructRef cst)
| Meta _ | Evar _ -> assert false
| Case (_, _, _, ([|_|], oty), _, c, [||]) when Vars.noccurn 1 oty ->
    (* non dependent match on an inductive with no constructors *)
    begin match Constr.kind c with
    | Const (kn, _) when not (Declareops.constant_has_body (lookup_constant kn)) ->
      let (curr, data, ax2ty) = accu in
      let obj = ConstRef kn in
      let already_in = GlobRef.Map_env.mem obj data in
      let data = if not already_in then GlobRef.Map_env.add obj None data else data in
      let ty = (current, ctx, Vars.subst1 mkProp oty) in
      let ax2ty =
        try let l = GlobRef.Map_env.find obj ax2ty in GlobRef.Map_env.add obj (ty::l) ax2ty
        with Not_found -> GlobRef.Map_env.add obj [ty] ax2ty in
      (GlobRef.Set_env.add obj curr, data, ax2ty)
    | _ ->
        fold_with_full_binders
          Context.Rel.add (traverse current) ctx accu t
    end
| _ -> fold_with_full_binders
          Context.Rel.add (traverse current) ctx accu t

and traverse_object (curr, data, ax2ty) body obj =
  let data, ax2ty =
    let already_in = GlobRef.Map_env.mem obj data in
    if already_in then data, ax2ty
    else match body () (* Beware: this can be very costly *) with
    | None ->
      GlobRef.Map_env.add obj None data, ax2ty
    | Some body ->
      let contents,data,ax2ty =
        traverse (label_of obj) Context.Rel.empty
                 (GlobRef.Set_env.empty,data,ax2ty) body in
      GlobRef.Map_env.add obj (Some contents) data, ax2ty
  in
  (GlobRef.Set_env.add obj curr, data, ax2ty)

(** Collects the references occurring in the declaration of mutual inductive
    definitions. All the constructors and names of a mutual inductive
    definition share exactly the same dependencies. Also, there is no explicit
    dependency between mutually defined inductives and constructors. *)
and traverse_inductive (curr, data, ax2ty) mind obj =
  let firstind_ref = (GlobRef.IndRef (mind, 0)) in
  let label = label_of obj in
  let data, ax2ty =
   (* Invariant : I_0 \in data iff I_i \in data iff c_ij \in data
      where I_0, I_1, ... are in the same mutual definition and c_ij
      are all their constructors. *)
   if
     (* recursive call: *) GlobRef.Set_env.mem firstind_ref curr ||
     (* already in: *) GlobRef.Map_env.mem firstind_ref data
   then data, ax2ty
   else
     (* Take into account potential recursivity of ind in itself *)
     let curr = GlobRef.Set_env.add firstind_ref GlobRef.Set_env.empty in
     let accu = (curr, data, ax2ty) in
     let mib = lookup_mind mind in
     (* Collects references of parameters *)
     let param_ctx = mib.mind_params_ctxt in
     let nparam = List.length param_ctx in
     let accu = traverse_context label Context.Rel.empty accu param_ctx in
     (* For each inductive, collects references in their arity and in the type
        of constructors*)
     let (contents, data, ax2ty) = Array.fold_left (fun accu oib ->
         let arity_wo_param =
           List.rev (List.skipn nparam (List.rev oib.mind_arity_ctxt))
         in
         let accu =
           traverse_context
             label param_ctx accu arity_wo_param
         in
         Array.fold_left (fun accu cst_typ ->
            let param_ctx, cst_typ_wo_param = Term.decompose_prod_n_assum nparam cst_typ in
            traverse label param_ctx accu cst_typ_wo_param)
          accu oib.mind_user_lc)
       accu mib.mind_packets
     in
     (* Maps all these dependencies to inductives and constructors*)
     let data =
       let contents = GlobRef.Set_env.remove firstind_ref contents in
       Array.fold_left_i (fun n data oib ->
       let ind = (mind, n) in
       let data = GlobRef.Map_env.add (GlobRef.IndRef ind) (Some contents) data in
       Array.fold_left_i (fun k data _ ->
         GlobRef.Map_env.add (GlobRef.ConstructRef (ind, k+1)) (Some contents) data
       ) data oib.mind_consnames) data mib.mind_packets
     in
     (data, ax2ty)
  in
  (GlobRef.Set_env.add obj curr, data, ax2ty)

(** Collects references in a rel_context. *)
and traverse_context current ctx accu ctxt =
  snd (Context.Rel.fold_outside (fun decl (ctx, accu) ->
    match decl with
     | Context.Rel.Declaration.LocalDef (_,c,t) ->
          let accu = traverse current ctx (traverse current ctx accu t) c in
          let ctx = Context.Rel.add decl ctx in
          ctx, accu
     | Context.Rel.Declaration.LocalAssum (_,t) ->
          let accu = traverse current ctx accu t in
          let ctx = Context.Rel.add decl ctx in
           ctx, accu) ctxt ~init:(ctx, accu))

let traverse current t =
  let () = modcache := MPmap.empty in
  traverse current Context.Rel.empty (GlobRef.Set_env.empty, GlobRef.Map_env.empty, GlobRef.Map_env.empty) t

(** Hopefully bullet-proof function to recover the type of a constant. It just
    ignores all the universe stuff. There are many issues that can arise when
    considering terms out of any valid environment, so use with caution. *)
let type_of_constant cb = cb.Declarations.const_type

let uses_uip mib =
  Array.exists (fun mip ->
      mip.mind_relevance == Sorts.Irrelevant
      && Array.length mip.mind_nf_lc = 1
      && List.length (fst mip.mind_nf_lc.(0)) = List.length mib.mind_params_ctxt)
    mib.mind_packets

let assumptions ?(add_opaque=false) ?(add_transparent=false) st gr t =
  (* Only keep the transitive dependencies *)
  let (_, graph, ax2ty) = traverse (label_of gr) t in
  let open GlobRef in
  let fold obj contents accu = match obj with
  | VarRef id ->
    let decl = Global.lookup_named id in
    if is_local_assum decl then
      let t = Context.Named.Declaration.get_type decl in
      ContextObjectMap.add (Variable id) t accu
    else accu
  | ConstRef kn ->
      let cb = lookup_constant kn in
      let accu =
        if cb.const_typing_flags.check_guarded then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (Guarded obj, l)) Constr.mkProp accu
      in
      let accu =
        if cb.const_typing_flags.check_universes then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (TypeInType obj, l)) Constr.mkProp accu
      in
    if not (Option.has_some contents) then
      let t = type_of_constant cb in
      let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
      ContextObjectMap.add (Axiom (Constant kn,l)) t accu
    else if add_opaque && (Declareops.is_opaque cb || not (TransparentState.is_transparent_constant st kn)) then
      let t = type_of_constant cb in
      ContextObjectMap.add (Opaque kn) t accu
    else if add_transparent then
      let t = type_of_constant cb in
      ContextObjectMap.add (Transparent kn) t accu
    else
      accu
  | IndRef (m,_) | ConstructRef ((m,_),_) ->
      let mind = lookup_mind m in
      let accu =
        if mind.mind_typing_flags.check_positive then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (Positive m, l)) Constr.mkProp accu
      in
      let accu =
        if mind.mind_typing_flags.check_guarded then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (Guarded obj, l)) Constr.mkProp accu
      in
      let accu =
        if mind.mind_typing_flags.check_universes then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (TypeInType obj, l)) Constr.mkProp accu
      in
      let accu =
        if not (uses_uip mind) then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (UIP m, l)) Constr.mkProp accu
      in
      accu
  in GlobRef.Map_env.fold fold graph ContextObjectMap.empty

(* Reexport a wrapper to preserve the 8.16 API *)
let traverse current t =
  let (curr, graph, ax2ty) = traverse current t in
  let map = function
  | None -> GlobRef.Set_env.empty
  | Some s -> s
  in
  let graph = GlobRef.Map_env.map map graph in
  (curr, graph, ax2ty)
