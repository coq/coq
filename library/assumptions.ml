(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
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

open Util
open Names
open Sign
open Univ
open Term
open Declarations
open Mod_subst

type context_object =
  | Variable of identifier (* A section variable or a Let definition *)
  | Axiom of constant      (* An axiom or a constant. *)
  | Opaque of constant     (* An opaque constant. *)

(* Defines a set of [assumption] *)
module OrderedContextObject =
struct
  type t = context_object
  let compare x y =
      match x , y with
      | Variable i1 , Variable i2 -> id_ord i1 i2
      | Axiom k1 , Axiom k2 -> Pervasives.compare k1 k2
	          (* spiwack: it would probably be cleaner
		     to provide a [kn_ord] function *)
      | Opaque k1 , Opaque k2 -> Pervasives.compare k1 k2
      | Variable _ , Axiom _ -> -1
      | Axiom _ , Variable _ -> 1
      | Opaque _ , _ -> -1
      | _, Opaque _ -> 1
end

module ContextObjectSet = Set.Make (OrderedContextObject)
module ContextObjectMap = Map.Make (OrderedContextObject)

(** For a constant c in a module sealed by an interface (M:T and
    not M<:T), [Global.lookup_constant] may return a [constant_body]
    without body. We fix this by looking in the implementation
    of the module *)

let modcache = ref (MPmap.empty : structure_body MPmap.t)

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
	match List.assoc lab' fields with
	  | SFBmodule mb -> mb
	  | _ -> assert false (* same label for a non-module ?! *)

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
    if inner_mp = mp then subs
    else add_mp inner_mp mp mb.mod_delta subs
  in
  Modops.subst_signature subs fields

and fields_of_mb subs mb args =
  let seb = match mb.mod_expr with
    | None -> mb.mod_type (* cf. Declare Module *)
    | Some seb -> seb
  in
  fields_of_seb subs mb.mod_mp seb args

(* TODO: using [empty_delta_resolver] below in [fields_of_seb]
   is probably slightly incorrect. But:
    a) I don't see currently what should be used instead
    b) this shouldn't be critical for Print Assumption. At worse some
       constants will have a canonical name which is non-canonical,
       leading to failures in [Global.lookup_constant], but our own
       [lookup_constant] should work.
*)

and fields_of_seb subs mp0 seb args = match seb with
  | SEBstruct l ->
    assert (args = []);
    l, mp0, subs
  | SEBident mp ->
    let mb = lookup_module_in_impl (subst_mp subs mp) in
    fields_of_mb subs mb args
  | SEBapply (seb1,seb2,_) ->
    (match seb2 with
      | SEBident mp2 -> fields_of_seb subs mp0 seb1 (mp2::args)
      | _ -> assert false) (* only legal application is to module names *)
  | SEBfunctor (mbid,mtb,seb) ->
    (match args with
      | [] -> assert false (* we should only encounter applied functors *)
      | mpa :: args ->
	let subs = add_mbid mbid mpa empty_delta_resolver subs in
	fields_of_seb subs mp0 seb args)
  | SEBwith _ -> assert false (* should not appear in a mod_expr
				   or mod_type field *)

let lookup_constant_in_impl cst fallback =
  try
    let mp,dp,lab = repr_kn (canonical_con cst) in
    let fields = memoize_fields_of_mp mp in
    (* A module found this way is necessarily closed, in particular
       our constant cannot be in an opened section : *)
    match List.assoc lab fields with
      | SFBconst cb -> cb
      | _ -> assert false (* label not pointing to a constant ?! *)
  with Not_found ->
    (* Either:
       - The module part of the constant isn't registered yet :
         we're still in it, so the [constant_body] found earlier
         (if any) was a true axiom.
       - The label has not been found in the structure. This is an error *)
    match fallback with
      | Some cb -> cb
      | None -> anomaly ("Print Assumption: unknown constant "^string_of_con cst)

let lookup_constant cst =
  try
    let cb = Global.lookup_constant cst in
    if cb.const_body <> None then cb
    else lookup_constant_in_impl cst (Some cb)
  with Not_found -> lookup_constant_in_impl cst None

let assumptions ?(add_opaque=false) st (* t *) =
  modcache := MPmap.empty;
  let (idts,knst) = st in
  (* Infix definition for chaining function that accumulate
     on a and a ContextObjectSet, ContextObjectMap.  *)
  let ( ** ) f1 f2 s m = let (s',m') = f1 s m in f2 s' m' in
  (* This function eases memoization, by checking if an object is already
     stored before trying and applying a function.
     If the object is there, the function is not fired (we are in a
     particular case where memoized object don't need a treatment at all).
     If the object isn't there, it is stored and the function is fired*)
  let try_and_go o f s m =
    if ContextObjectSet.mem o s then
      (s,m)
    else
      f (ContextObjectSet.add o s) m
  in
  let identity2 s m = (s,m)
  in
  (* Goes recursively into the term to see if it depends on assumptions.
    The 3 important cases are :
     - Const _ where we need to first unfold the constant and return
       the needed assumptions of its body in the environment,
     - Rel _ which means the term is a variable which has been bound
       earlier by a Lambda or a Prod (returns [] ),
     - Var _ which means that the term refers to a section variable or
       a "Let" definition, in the former it is an assumption of [t],
       in the latter is must be unfolded like a Const.
    The other cases are straightforward recursion.
    Calls to the environment are memoized, thus avoiding to explore
    the DAG of the environment as if it was a tree (can cause
    exponential behavior and prevent the algorithm from terminating
    in reasonable time). [s] is a set of [context_object], representing
    the object already visited.*)
  let rec do_constr t s acc =
    let rec iter t =
      match kind_of_term t with
	| Var id -> do_memoize_id id
	| Meta _ | Evar _ -> assert false
	| Cast (e1,_,e2) | Prod (_,e1,e2) | Lambda (_,e1,e2) ->
	  (iter e1)**(iter e2)
	| LetIn (_,e1,e2,e3) -> (iter e1)**(iter e2)**(iter e3)
	| App (e1, e_array) -> (iter e1)**(iter_array e_array)
	| Case (_,e1,e2,e_array) -> (iter e1)**(iter e2)**(iter_array e_array)
	| Fix (_,(_, e1_array, e2_array)) | CoFix (_,(_,e1_array, e2_array)) ->
          (iter_array e1_array) ** (iter_array e2_array)
	| Const kn -> do_memoize_kn kn
	| _ -> identity2 (* closed atomic types + rel *)
    and iter_array a = Array.fold_right (fun e f -> (iter e)**f) a identity2
    in iter t s acc

  and add_id id s acc =
    (* a Var can be either a variable, or a "Let" definition.*)
    match Global.lookup_named id with
    | (_,None,t) ->
        (s,ContextObjectMap.add (Variable id) t acc)
    | (_,Some bdy,_) -> do_constr bdy s acc

  and do_memoize_id id =
    try_and_go (Variable id) (add_id id)

  and add_kn kn s acc =
    let cb = lookup_constant kn in
    let do_type cst =
      let ctype =
	match cb.const_type with
	| PolymorphicArity (ctx,a) -> mkArity (ctx, Type a.poly_level)
	| NonPolymorphicType t -> t
      in
	(s,ContextObjectMap.add cst ctype acc)
    in
    let (s,acc) =
      if add_opaque && cb.const_body <> None
	&& (cb.const_opaque || not (Cpred.mem kn knst))
      then
	do_type (Opaque kn)
      else (s,acc)
    in
      match cb.const_body with
      | None -> do_type (Axiom kn)
      | Some body -> do_constr (Declarations.force body) s acc

  and do_memoize_kn kn =
    try_and_go (Axiom kn) (add_kn kn)

 in
 fun t ->
   snd (do_constr t
	  (ContextObjectSet.empty)
	  (ContextObjectMap.empty))
