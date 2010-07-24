(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Pp
open Util
open Names
open Term
open Sign
open Declarations
open Environ
open Reduction

(*s Cooking the constants. *)

type work_list = identifier array Cmap.t * identifier array Mindmap.t

let pop_dirpath p = match repr_dirpath p with
  | [] -> anomaly "dirpath_prefix: empty dirpath"
  | _::l -> make_dirpath l

let pop_mind kn =
  let (mp,dir,l) = Names.repr_mind kn in
  Names.make_mind mp (pop_dirpath dir) l

let pop_con con =
  let (mp,dir,l) = Names.repr_con con in
  Names.make_con mp (pop_dirpath dir) l

type my_global_reference =
  | ConstRef of constant
  | IndRef of inductive
  | ConstructRef of constructor

let cache = (Hashtbl.create 13 : (my_global_reference, constr) Hashtbl.t)

let clear_cooking_sharing () = Hashtbl.clear cache

let share r (cstl,knl) =
  try Hashtbl.find cache r
  with Not_found ->
  let f,l =
    match r with
    | IndRef (kn,i) ->
	mkInd (pop_mind kn,i), Mindmap.find kn knl
    | ConstructRef ((kn,i),j) ->
	mkConstruct ((pop_mind kn,i),j), Mindmap.find kn knl
    | ConstRef cst ->
	mkConst (pop_con cst), Cmap.find cst cstl in
  let c = mkApp (f, Array.map mkVar l) in
  Hashtbl.add cache r c;
  (* has raised Not_found if not in work_list *)
  c

let update_case_info ci modlist =
  try
    let ind, n =
      match kind_of_term (share (IndRef ci.ci_ind) modlist) with
      | App (f,l) -> (destInd f, Array.length l)
      | Ind ind -> ind, 0
      | _ -> assert false in
    { ci with ci_ind = ind; ci_npar = ci.ci_npar + n }
  with Not_found ->
    ci

let empty_modlist = (Cmap.empty, Mindmap.empty)

let expmod_constr modlist c =
  let rec substrec c =
    match kind_of_term c with
      | Case (ci,p,t,br) ->
	  map_constr substrec (mkCase (update_case_info ci modlist,p,t,br))

      | Ind ind ->
	  (try
	    share (IndRef ind) modlist
	   with
	    | Not_found -> map_constr substrec c)

      | Construct cstr ->
	  (try
	    share (ConstructRef cstr) modlist
	   with
	    | Not_found -> map_constr substrec c)

      | Const cst ->
	  (try
	    share (ConstRef cst) modlist
	   with
	    | Not_found -> map_constr substrec c)

  | _ -> map_constr substrec c

  in
  if modlist = empty_modlist then c
  else under_outer_cast nf_betaiota (substrec c)

let abstract_constant_type =
   List.fold_left (fun c d -> mkNamedProd_wo_LetIn d c)

let abstract_constant_body =
  List.fold_left (fun c d -> mkNamedLambda_or_LetIn d c)

type recipe = {
  d_from : constant_body;
  d_abstract : named_context;
  d_modlist : work_list }

let on_body f =
  Option.map (fun c -> Declarations.from_val (f (Declarations.force c)))

let cook_constant env r =
  let cb = r.d_from in
  let hyps = Sign.map_named_context (expmod_constr r.d_modlist) r.d_abstract in
  let body =
    on_body (fun c ->
      abstract_constant_body (expmod_constr r.d_modlist c) hyps)
      cb.const_body in
  let typ = match cb.const_type with
    | NonPolymorphicType t ->
	let typ = abstract_constant_type (expmod_constr r.d_modlist t) hyps in
	NonPolymorphicType typ
    | PolymorphicArity (ctx,s) ->
	let t = mkArity (ctx,Type s.poly_level) in
	let typ = abstract_constant_type (expmod_constr r.d_modlist t) hyps in
	let j = make_judge (force (Option.get body)) typ in
	Typeops.make_polymorphic_if_constant_for_ind env j
  in
  let boxed = Cemitcodes.is_boxed cb.const_body_code in
  (body, typ, cb.const_constraints, cb.const_opaque, boxed,false)
