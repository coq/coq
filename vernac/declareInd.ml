(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Entries

(** Declaration of inductive blocks *)
let declare_inductive_argument_scopes kn mie =
  List.iteri (fun i {mind_entry_consnames=lc} ->
    Notation.declare_ref_arguments_scope Evd.empty (GlobRef.IndRef (kn,i));
    for j=1 to List.length lc do
      Notation.declare_ref_arguments_scope Evd.empty (GlobRef.ConstructRef ((kn,i),j));
    done) mie.mind_entry_inds

type inductive_obj = {
  ind_names : (Id.t * Id.t list) list
  (* For each block, name of the type + name of constructors *)
}

let inductive_names sp kn obj =
  let (dp,_) = Libnames.repr_path sp in
  let kn = Global.mind_of_delta_kn kn in
  let names, _ =
    List.fold_left
      (fun (names, n) (typename, consnames) ->
         let ind_p = (kn,n) in
         let names, _ =
           List.fold_left
             (fun (names, p) l ->
                let sp =
                  Libnames.make_path dp l
                in
                  ((sp, GlobRef.ConstructRef (ind_p,p)) :: names, p+1))
             (names, 1) consnames in
         let sp = Libnames.make_path dp typename
         in
           ((sp, GlobRef.IndRef ind_p) :: names, n+1))
      ([], 0) obj.ind_names
  in names

let load_inductive i ((sp, kn), names) =
  let names = inductive_names sp kn names in
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Until i) sp ref ) names

let open_inductive i ((sp, kn), names) =
  let names = inductive_names sp kn names in
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Exactly i) sp ref) names

let cache_inductive ((sp, kn), names) =
  let names = inductive_names sp kn names in
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Until 1) sp ref) names

let discharge_inductive ((sp, kn), names) =
  Some names

let inInductive : inductive_obj -> Libobject.obj =
  let open Libobject in
  declare_object {(default_object "INDUCTIVE") with
    cache_function = cache_inductive;
    load_function = load_inductive;
    open_function = open_inductive;
    classify_function = (fun a -> Substitute a);
    subst_function = ident_subst_function;
    discharge_function = discharge_inductive;
  }


let cache_prim (_,(p,c)) = Recordops.register_primitive_projection p c

let load_prim _ p = cache_prim p

let subst_prim (subst,(p,c)) = Mod_subst.subst_proj_repr subst p, Mod_subst.subst_constant subst c

let discharge_prim (_,(p,c)) = Some (Lib.discharge_proj_repr p, c)

let inPrim : (Projection.Repr.t * Constant.t) -> Libobject.obj =
  let open Libobject in
  declare_object {
    (default_object "PRIMPROJS") with
    cache_function = cache_prim ;
    load_function = load_prim;
    subst_function = subst_prim;
    classify_function = (fun x -> Substitute x);
    discharge_function = discharge_prim }

let declare_primitive_projection p c = Lib.add_anonymous_leaf (inPrim (p,c))

let declare_one_projection univs (mind,_ as ind) ~proj_npars proj_arg label (term,types) =
  let name = Label.to_id label in
  let univs, u = match univs with
    | Monomorphic_entry _ ->
      (* Global constraints already defined through the inductive *)
      Monomorphic_entry Univ.ContextSet.empty, Univ.Instance.empty
    | Polymorphic_entry (nas, ctx) ->
      Polymorphic_entry (nas, ctx), Univ.UContext.instance ctx
  in
  let term = Vars.subst_instance_constr u term in
  let types = Vars.subst_instance_constr u types in
  let entry = Declare.definition_entry ~types ~univs term in
  let cst = Declare.declare_constant ~name ~kind:Decls.(IsDefinition StructureComponent) (Declare.DefinitionEntry entry) in
  let p = Projection.Repr.make ind ~proj_npars ~proj_arg label in
  declare_primitive_projection p cst

let declare_projections univs mind =
  let env = Global.env () in
  let mib = Environ.lookup_mind mind env in
  let open Declarations in
  match mib.mind_record with
  | PrimRecord info ->
    let iter_ind i (_, labs, _, _) =
      let ind = (mind, i) in
      let projs = Inductiveops.compute_projections env ind in
      CArray.iter2_i (declare_one_projection univs ind ~proj_npars:mib.mind_nparams) labs projs
    in
    let () = Array.iteri iter_ind info in
    true
  | FakeRecord -> false
  | NotRecord -> false

let feedback_axiom () = Feedback.(feedback AddedAxiom)

let is_unsafe_typing_flags () =
  let open Declarations in
  let flags = Environ.typing_flags (Global.env()) in
  not (flags.check_universes && flags.check_guarded && flags.check_positive)

(* for initial declaration *)
let declare_mind mie =
  let id = match mie.mind_entry_inds with
    | ind::_ -> ind.mind_entry_typename
    | [] -> CErrors.anomaly (Pp.str "cannot declare an empty list of inductives.") in
  let map_names mip = (mip.mind_entry_typename, mip.mind_entry_consnames) in
  let names = List.map map_names mie.mind_entry_inds in
  List.iter (fun (typ, cons) ->
      Declare.check_exists typ;
      List.iter Declare.check_exists cons) names;
  let _kn' = Global.add_mind id mie in
  let (sp,kn as oname) = Lib.add_leaf id (inInductive { ind_names = names }) in
  if is_unsafe_typing_flags() then feedback_axiom ();
  let mind = Global.mind_of_delta_kn kn in
  let isprim = declare_projections mie.mind_entry_universes mind in
  Impargs.declare_mib_implicits mind;
  declare_inductive_argument_scopes mind mie;
  oname, isprim
