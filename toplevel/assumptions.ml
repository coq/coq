(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* The following definitions are used by the function
   [assumptions] which gives as an output the set of all
   axioms and sections variables on which a given term depends
   in a context (expectingly the Global context) *)

(* Initial author: Arnaud Spiwack
   Module-traversing code: Pierre Letouzey *)

open Pp
open Errors
open Util
open Names
open Term
open Declarations
open Mod_subst
open Globnames
open Printer

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
      let subs = add_mbid mbid mpa empty_delta_resolver (*TODO*) subs in
      fields_of_functor f subs mp0 args e

let rec lookup_module_in_impl mp =
  try Global.lookup_module mp
  with Not_found ->
    (* The module we search might not be exported by its englobing module(s).
       We access the upper layer, and then do a manual search *)
    match mp with
      | MPfile _ | MPbound _ ->
	raise Not_found (* should have been found by [lookup_module] *)
      | MPdot (mp',lab') ->
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
    if mp_eq inner_mp mp then subs
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
    let mp,dp,lab = repr_kn (canonical_con cst) in
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
      | None -> anomaly (str "Print Assumption: unknown constant " ++ pr_con cst)

let lookup_constant cst =
  try
    let cb = Global.lookup_constant cst in
    if Declareops.constant_has_body cb then cb
    else lookup_constant_in_impl cst (Some cb)
  with Not_found -> lookup_constant_in_impl cst None

(** Graph traversal of an object, collecting on the way the dependencies of
    traversed objects *)

let label_of = function
  | ConstRef kn -> pi3 (repr_con kn)
  | IndRef (kn,_)
  | ConstructRef ((kn,_),_) -> pi3 (repr_mind kn)
  | VarRef id -> Label.of_id id

let push (r : Context.rel_declaration) (ctx : Context.rel_context) = r :: ctx

let rec traverse current ctx accu t = match kind_of_term t with
| Var id ->
  let body () = match Global.lookup_named id with (_, body, _) -> body in
  traverse_object accu body (VarRef id)
| Const (kn, _) ->
  let body () = Global.body_of_constant_body (lookup_constant kn) in
  traverse_object accu body (ConstRef kn)
| Ind (ind, _) ->
  traverse_object accu (fun () -> None) (IndRef ind)
| Construct (cst, _) ->
  traverse_object accu (fun () -> None) (ConstructRef cst)
| Meta _ | Evar _ -> assert false
| Case (_,oty,c,[||]) ->
    (* non dependent match on an inductive with no constructors *) 
    begin match Constr.(kind oty, kind c) with
    | Lambda(Anonymous,_,oty), Const (kn, _)
      when Vars.noccurn 1 oty &&
      not (Declareops.constant_has_body (lookup_constant kn)) ->
        let body () = Global.body_of_constant_body (lookup_constant kn) in
        traverse_object
          ~inhabits:(current,ctx,Vars.subst1 mkProp oty) accu body (ConstRef kn)
    | _ -> Termops.fold_constr_with_full_binders push (traverse current) ctx accu t 
    end
| _ -> Termops.fold_constr_with_full_binders push (traverse current) ctx accu t

and traverse_object ?inhabits (curr, data, ax2ty) body obj =
  let data, ax2ty =
    let already_in = Refmap.mem obj data in
    match body () with
    | None ->
        let data =
          if not already_in then Refmap.add obj Refset.empty data else data in
        let ax2ty =
          if Option.is_empty inhabits then ax2ty else
          let ty = Option.get inhabits in
          try let l = Refmap.find obj ax2ty in Refmap.add obj (ty::l) ax2ty 
          with Not_found -> Refmap.add obj [ty] ax2ty in
        data, ax2ty
    | Some body ->
      let contents,data,ax2ty =
        traverse (label_of obj) [] (Refset.empty,data,ax2ty) body in
      Refmap.add obj contents data, ax2ty
  in
  (Refset.add obj curr, data, ax2ty)

let traverse current t =
  let () = modcache := MPmap.empty in
  traverse current [] (Refset.empty, Refmap.empty, Refmap.empty) t

(** Hopefully bullet-proof function to recover the type of a constant. It just
    ignores all the universe stuff. There are many issues that can arise when
    considering terms out of any valid environment, so use with caution. *)
let type_of_constant cb = match cb.Declarations.const_type with
| Declarations.RegularArity ty -> ty
| Declarations.TemplateArity (ctx, arity) ->
  Term.mkArity (ctx, Sorts.sort_of_univ arity.Declarations.template_level)

let assumptions ?(add_opaque=false) ?(add_transparent=false) st gr t =
  let (idts, knst) = st in
  (** Only keep the transitive dependencies *)
  let (_, graph, ax2ty) = traverse (label_of gr) t in
  let fold obj _ accu = match obj with
  | VarRef id ->
    let (_, body, t) = Global.lookup_named id in
    if Option.is_empty body then ContextObjectMap.add (Variable id) t accu
    else accu
  | ConstRef kn ->
    let cb = lookup_constant kn in
    if not (Declareops.constant_has_body cb) then
      let t = type_of_constant cb in
      let l = try Refmap.find obj ax2ty with Not_found -> [] in
      ContextObjectMap.add (Axiom (kn,l)) t accu
    else if add_opaque && (Declareops.is_opaque cb || not (Cpred.mem kn knst)) then
      let t = type_of_constant cb in
      ContextObjectMap.add (Opaque kn) t accu
    else if add_transparent then
      let t = type_of_constant cb in
      ContextObjectMap.add (Transparent kn) t accu
    else
      accu
  | IndRef _ | ConstructRef _ -> accu
  in
  Refmap.fold fold graph ContextObjectMap.empty
