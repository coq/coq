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
open Context
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
  |NoFunctor a -> f subs mp0 args a
  |MoreFunctor (mbid,_,e) ->
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
  |Algebraic expr -> fields_of_expression subs mb.mod_mp args expr
  |Struct sign -> fields_of_signature subs mb.mod_mp args sign
  |Abstract|FullStruct -> fields_of_signature subs mb.mod_mp args mb.mod_type

(** The Abstract case above corresponds to [Declare Module] *)

and fields_of_signature x =
  fields_of_functor
    (fun subs mp0 args struc ->
      assert (List.is_empty args);
      (struc, mp0, subs)) x

and fields_of_expr subs mp0 args = function
  |MEident mp ->
    let mb = lookup_module_in_impl (subst_mp subs mp) in
    fields_of_mb subs mb args
  |MEapply (me1,mp2) -> fields_of_expr subs mp0 (mp2::args) me1
  |MEwith _ -> assert false (* no 'with' in [mod_expr] *)

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

let rec traverse current ctx accu t =
  let open GlobRef in
  match Constr.kind t with
| Var id ->
  let body () = id |> Global.lookup_named |> NamedDecl.get_value in
  traverse_object accu body (VarRef id)
| Const ((kn, _), _) ->
  let body () = Option.map pi1 (Global.body_of_constant_body Library.indirect_accessor (lookup_constant kn)) in
  traverse_object accu body (ConstRef kn)
| Ind (((mind, _) as ind, _), _) ->
  traverse_inductive accu mind (IndRef ind)
| Construct (((mind, _), _) as cst, _) ->
  traverse_inductive accu mind (ConstructRef cst)
| Meta _ | Evar _ -> assert false
| Case (_,oty,c,[||]) ->
    (* non dependent match on an inductive with no constructors *)
    begin match Constr.(kind oty, kind c) with
    | Lambda(_,_,oty), Const ((kn, _), _)
      when Vars.noccurn 1 oty &&
      not (Declareops.constant_has_body (lookup_constant kn)) ->
        let body () = Option.map pi1 (Global.body_of_constant_body Library.indirect_accessor (lookup_constant kn)) in
        traverse_object
          ~inhabits:(current,ctx,Vars.subst1 mkProp oty) accu body (ConstRef kn)
    | _ ->
        Constr.fold_with_full_binders
          Context.Rel.add (traverse current) ctx accu t
    end
| _ -> Constr.fold_with_full_binders
          Context.Rel.add (traverse current) ctx accu t

and traverse_object ?inhabits (curr, data, ax2ty) body obj =
  let data, ax2ty =
    let already_in = GlobRef.Map_env.mem obj data in
    match body () with
    | None ->
        let data =
          if not already_in then GlobRef.Map_env.add obj GlobRef.Set_env.empty data else data in
        let ax2ty =
          if Option.is_empty inhabits then ax2ty else
          let ty = Option.get inhabits in
          try let l = GlobRef.Map_env.find obj ax2ty in GlobRef.Map_env.add obj (ty::l) ax2ty
          with Not_found -> GlobRef.Map_env.add obj [ty] ax2ty in
        data, ax2ty
    | Some body ->
      if already_in then data, ax2ty else
      let contents,data,ax2ty =
        traverse (label_of obj) Context.Rel.empty
                 (GlobRef.Set_env.empty,data,ax2ty) body in
      GlobRef.Map_env.add obj contents data, ax2ty
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
   if GlobRef.Map_env.mem firstind_ref data then data, ax2ty else
     let mib = lookup_mind mind in
     (* Collects references of parameters *)
     let param_ctx = mib.mind_params_ctxt in
     let nparam = List.length param_ctx in
     let accu =
       traverse_context label Context.Rel.empty
                        (GlobRef.Set_env.empty, data, ax2ty) param_ctx
     in
     (* Build the context of all arities *)
     let arities_ctx =
       let instance =
         let open Univ in
         Instance.of_array
           (Array.init
              (AUContext.size
                 (Declareops.inductive_polymorphic_context mib))
              Level.var)
       in
       Array.fold_left (fun accu oib ->
          let pspecif = ((mib, oib), instance) in
          let ind_type = Inductive.type_of_inductive pspecif in
          let indr = oib.mind_relevance in
          let ind_name = Name oib.mind_typename in
          Context.Rel.add (Context.Rel.Declaration.LocalAssum (make_annot ind_name indr, ind_type)) accu)
          Context.Rel.empty mib.mind_packets
     in
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
            let ctx = Context.(Rel.fold_outside Context.Rel.add ~init:arities_ctx param_ctx) in
            traverse label ctx accu cst_typ_wo_param)
          accu oib.mind_user_lc)
       accu mib.mind_packets
     in
     (* Maps all these dependencies to inductives and constructors*)
     let data = Array.fold_left_i (fun n data oib ->
       let ind = (mind, n) in
       let data = GlobRef.Map_env.add (GlobRef.IndRef ind) contents data in
       Array.fold_left_i (fun k data _ ->
         GlobRef.Map_env.add (GlobRef.ConstructRef (ind, k+1)) contents data
       ) data oib.mind_consnames) data mib.mind_packets
     in
     data, ax2ty
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

let assumptions ?(add_opaque=false) ?(add_transparent=false) st gr t =
  (* Only keep the transitive dependencies *)
  let (_, graph, ax2ty) = traverse (label_of gr) t in
  let open GlobRef in
  let fold obj _ accu = match obj with
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
        if cb.const_typing_flags.check_sized then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (Sized obj, l)) Constr.mkProp accu
      in
      let accu =
        if cb.const_typing_flags.check_universes then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (TypeInType obj, l)) Constr.mkProp accu
      in
    if not (Declareops.constant_has_body cb) then
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
        if mind.mind_typing_flags.check_sized then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (Sized obj, l)) Constr.mkProp accu
      in
      let accu =
        if mind.mind_typing_flags.check_universes then accu
        else
          let l = try GlobRef.Map_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (TypeInType obj, l)) Constr.mkProp accu
      in
      accu
  in GlobRef.Map_env.fold fold graph ContextObjectMap.empty
