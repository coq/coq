(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
open Globnames
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
    let mp,dp,lab = KerName.repr (Constant.canonical cst) in
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
  try
    let cb = Global.lookup_constant cst in
    if Declareops.constant_has_body cb then cb
    else lookup_constant_in_impl cst (Some cb)
  with Not_found -> lookup_constant_in_impl cst None

let lookup_mind_in_impl mind =
  try
    let mp,dp,lab = KerName.repr (MutInd.canonical mind) in
    let fields = memoize_fields_of_mp mp in
      search_mind_label lab fields
  with Not_found ->
    anomaly (str "Print Assumption: unknown inductive " ++ MutInd.print mind ++ str ".")

let lookup_mind mind =
  try Global.lookup_mind mind
  with Not_found -> lookup_mind_in_impl mind

(** Graph traversal of an object, collecting on the way the dependencies of
    traversed objects *)

let label_of = function
  | ConstRef kn -> pi3 (Constant.repr3 kn)
  | IndRef (kn,_)
  | ConstructRef ((kn,_),_) -> pi3 (MutInd.repr3 kn)
  | VarRef id -> Label.of_id id

let fold_constr_with_full_binders g f n acc c =
  let open Context.Rel.Declaration in
  match Constr.kind c with
  | Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _ | Construct _ -> acc
  | Cast (c,_, t) -> f n (f n acc c) t
  | Prod (na,t,c) -> f (g (LocalAssum (na,t)) n) (f n acc t) c
  | Lambda (na,t,c) -> f (g (LocalAssum (na,t)) n) (f n acc t) c
  | LetIn (na,b,t,c) -> f (g (LocalDef (na,b,t)) n) (f n (f n acc b) t) c
  | App (c,l) -> Array.fold_left (f n) (f n acc c) l
  | Proj (p,c) -> f n acc c
  | Evar (_,l) -> Array.fold_left (f n) acc l
  | Case (_,p,c,bl) -> Array.fold_left (f n) (f n (f n acc p) c) bl
  | Fix (_,(lna,tl,bl)) ->
      let n' = CArray.fold_left2 (fun c n t -> g (LocalAssum (n,t)) c) n lna tl in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd
  | CoFix (_,(lna,tl,bl)) ->
      let n' = CArray.fold_left2 (fun c n t -> g (LocalAssum (n,t)) c) n lna tl in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd

let rec traverse current ctx accu t = match Constr.kind t with
| Var id ->
  let body () = id |> Global.lookup_named |> NamedDecl.get_value in
  traverse_object accu body (VarRef id)
| Const (kn, _) ->
  let body () = Option.map fst (Global.body_of_constant_body (lookup_constant kn)) in
  traverse_object accu body (ConstRef kn)
| Ind ((mind, _) as ind, _) ->
  traverse_inductive accu mind (IndRef ind)
| Construct (((mind, _), _) as cst, _) ->
  traverse_inductive accu mind (ConstructRef cst)
| Meta _ | Evar _ -> assert false
| Case (_,oty,c,[||]) ->
    (* non dependent match on an inductive with no constructors *)
    begin match Constr.(kind oty, kind c) with
    | Lambda(_,_,oty), Const (kn, _)
      when Vars.noccurn 1 oty &&
      not (Declareops.constant_has_body (lookup_constant kn)) ->
        let body () = Option.map fst (Global.body_of_constant_body (lookup_constant kn)) in
        traverse_object
          ~inhabits:(current,ctx,Vars.subst1 mkProp oty) accu body (ConstRef kn)
    | _ ->
        fold_constr_with_full_binders
          Context.Rel.add (traverse current) ctx accu t
    end
| _ -> fold_constr_with_full_binders
          Context.Rel.add (traverse current) ctx accu t

and traverse_object ?inhabits (curr, data, ax2ty) body obj =
  let data, ax2ty =
    let already_in = Refmap_env.mem obj data in
    match body () with
    | None ->
        let data =
          if not already_in then Refmap_env.add obj Refset_env.empty data else data in
        let ax2ty =
          if Option.is_empty inhabits then ax2ty else
          let ty = Option.get inhabits in
          try let l = Refmap_env.find obj ax2ty in Refmap_env.add obj (ty::l) ax2ty 
          with Not_found -> Refmap_env.add obj [ty] ax2ty in
        data, ax2ty
    | Some body ->
      if already_in then data, ax2ty else
      let contents,data,ax2ty =
        traverse (label_of obj) Context.Rel.empty
                 (Refset_env.empty,data,ax2ty) body in
      Refmap_env.add obj contents data, ax2ty
  in
  (Refset_env.add obj curr, data, ax2ty)

(** Collects the references occurring in the declaration of mutual inductive
    definitions. All the constructors and names of a mutual inductive
    definition share exactly the same dependencies. Also, there is no explicit
    dependency between mutually defined inductives and constructors. *)
and traverse_inductive (curr, data, ax2ty) mind obj =
  let firstind_ref = (IndRef (mind, 0)) in
  let label = label_of obj in
  let data, ax2ty =
   (* Invariant : I_0 \in data iff I_i \in data iff c_ij \in data
      where I_0, I_1, ... are in the same mutual definition and c_ij
      are all their constructors. *)
   if Refmap_env.mem firstind_ref data then data, ax2ty else
     let mib = lookup_mind mind in
     (* Collects references of parameters *)
     let param_ctx = mib.mind_params_ctxt in
     let nparam = List.length param_ctx in
     let accu =
       traverse_context label Context.Rel.empty
                        (Refset_env.empty, data, ax2ty) param_ctx
     in
     (* Build the context of all arities *)
     let arities_ctx =
       let global_env = Global.env () in
       Array.fold_left (fun accu oib ->
          let pspecif = Univ.in_punivs (mib, oib) in
          let ind_type = Inductive.type_of_inductive global_env pspecif in
          let ind_name = Name oib.mind_typename in
          Context.Rel.add (Context.Rel.Declaration.LocalAssum (ind_name, ind_type)) accu)
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
       let data = Refmap_env.add (IndRef ind) contents data in
       Array.fold_left_i (fun k data _ ->
         Refmap_env.add (ConstructRef (ind, k+1)) contents data
       ) data oib.mind_consnames) data mib.mind_packets
     in
     data, ax2ty
  in
  (Refset_env.add obj curr, data, ax2ty)

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
  traverse current Context.Rel.empty (Refset_env.empty, Refmap_env.empty, Refmap_env.empty) t

(** Hopefully bullet-proof function to recover the type of a constant. It just
    ignores all the universe stuff. There are many issues that can arise when
    considering terms out of any valid environment, so use with caution. *)
let type_of_constant cb = cb.Declarations.const_type

let assumptions ?(add_opaque=false) ?(add_transparent=false) st gr t =
  let (idts, knst) = st in
  (** Only keep the transitive dependencies *)
  let (_, graph, ax2ty) = traverse (label_of gr) t in
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
          let l = try Refmap_env.find obj ax2ty with Not_found -> [] in
          ContextObjectMap.add (Axiom (Guarded kn, l)) Constr.mkProp accu
      in
    if not (Declareops.constant_has_body cb) || not cb.const_typing_flags.check_universes then
      let t = type_of_constant cb in
      let l = try Refmap_env.find obj ax2ty with Not_found -> [] in
      ContextObjectMap.add (Axiom (Constant kn,l)) t accu
    else if add_opaque && (Declareops.is_opaque cb || not (Cpred.mem kn knst)) then
      let t = type_of_constant cb in
      ContextObjectMap.add (Opaque kn) t accu
    else if add_transparent then
      let t = type_of_constant cb in
      ContextObjectMap.add (Transparent kn) t accu
    else
      accu
  | IndRef (m,_) | ConstructRef ((m,_),_) ->
      let mind = lookup_mind m in
      if mind.mind_typing_flags.check_guarded then
        accu
      else
        let l = try Refmap_env.find obj ax2ty with Not_found -> [] in
        ContextObjectMap.add (Axiom (Positive m, l)) Constr.mkProp accu
  in
  Refmap_env.fold fold graph ContextObjectMap.empty
