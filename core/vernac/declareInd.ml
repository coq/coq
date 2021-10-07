(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

let open_inductive f i ((sp, kn), names) =
  let names = inductive_names sp kn names in
  List.iter (fun (sp, ref) ->
      if Libobject.in_filter_ref ref f then
        Nametab.push (Nametab.Exactly i) sp ref)
    names

let cache_inductive ((sp, kn), names) =
  let names = inductive_names sp kn names in
  List.iter (fun (sp, ref) -> Nametab.push (Nametab.Until 1) sp ref) names

let discharge_inductive ((sp, kn), names) =
  Some names

let objInductive : inductive_obj Libobject.Dyn.tag =
  let open Libobject in
  declare_object_full {(default_object "INDUCTIVE") with
    cache_function = cache_inductive;
    load_function = load_inductive;
    open_function = open_inductive;
    classify_function = (fun a -> Substitute a);
    subst_function = ident_subst_function;
    discharge_function = discharge_inductive;
  }

let inInductive v = Libobject.Dyn.Easy.inj v objInductive

let cache_prim (_,(p,c)) = Structures.PrimitiveProjections.register p c

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

let feedback_axiom () = Feedback.(feedback AddedAxiom)

let is_unsafe_typing_flags () =
  let open Declarations in
  let flags = Environ.typing_flags (Global.env()) in
  not (flags.check_universes && flags.check_guarded && flags.check_positive)

(* for initial declaration *)
let declare_mind ?typing_flags mie =
  let id = match mie.mind_entry_inds with
    | ind::_ -> ind.mind_entry_typename
    | [] -> CErrors.anomaly (Pp.str "cannot declare an empty list of inductives.") in
  let map_names mip = (mip.mind_entry_typename, mip.mind_entry_consnames) in
  let names = List.map map_names mie.mind_entry_inds in
  List.iter (fun (typ, cons) ->
      Declare.check_exists typ;
      List.iter Declare.check_exists cons) names;
  let _kn' = Global.add_mind ?typing_flags id mie in
  let (sp,kn as oname) = Lib.add_leaf id (inInductive { ind_names = names }) in
  if is_unsafe_typing_flags() then feedback_axiom ();
  let mind = Global.mind_of_delta_kn kn in
  let isprim = Inductive.is_primitive_record (Inductive.lookup_mind_specif (Global.env()) (mind,0)) in
  Impargs.declare_mib_implicits mind;
  declare_inductive_argument_scopes mind mie;
  oname, isprim

let is_recursive mie =
  let open Constr in
  let rec is_recursive_constructor lift typ =
    match Constr.kind typ with
    | Prod (_,arg,rest) ->
        not (EConstr.Vars.noccurn Evd.empty (* FIXME *) lift (EConstr.of_constr arg)) ||
        is_recursive_constructor (lift+1) rest
    | LetIn (na,b,t,rest) -> is_recursive_constructor (lift+1) rest
    | _ -> false
  in
  match mie.mind_entry_inds with
  | [ind] ->
      let nparams = List.length mie.mind_entry_params in
      List.exists (fun t -> is_recursive_constructor (nparams+1) t) ind.mind_entry_lc
  | _ -> false

let warn_non_primitive_record =
  CWarnings.create ~name:"non-primitive-record" ~category:"record"
    (fun indsp ->
       Pp.(hov 0 (str "The record " ++ Nametab.pr_global_env Id.Set.empty (GlobRef.IndRef indsp) ++
                  strbrk" could not be defined as a primitive record")))

let minductive_message = function
  | []  -> CErrors.user_err Pp.(str "No inductive definition.")
  | [x] -> Pp.(Id.print x ++ str " is defined")
  | l   -> Pp.(hov 0 (prlist_with_sep pr_comma Id.print l ++
                      spc () ++ str "are defined"))

type one_inductive_impls =
  Impargs.manual_implicits (* for inds *) *
  Impargs.manual_implicits list (* for constrs *)

let declare_mutual_inductive_with_eliminations ?(primitive_expected=false) ?typing_flags mie ubinders impls =
  (* spiwack: raises an error if the structure is supposed to be non-recursive,
        but isn't *)
  begin match mie.mind_entry_finite with
    | Declarations.BiFinite when is_recursive mie ->
      if Option.has_some mie.mind_entry_record then
        CErrors.user_err Pp.(str "Records declared with the keywords Record or Structure cannot be recursive. You can, however, define recursive records using the Inductive or CoInductive command.")
      else
        CErrors.user_err Pp.(str ("Types declared with the keyword Variant cannot be recursive. Recursive types are defined with the Inductive and CoInductive command."))
    | _ -> ()
  end;
  let names = List.map (fun e -> e.mind_entry_typename) mie.mind_entry_inds in
  let (_, kn), prim = declare_mind ?typing_flags mie in
  let mind = Global.mind_of_delta_kn kn in
  let is_template = match mie.mind_entry_universes with Template_ind_entry _ -> true | _ -> false in
  if primitive_expected && not prim then warn_non_primitive_record (mind,0);
  DeclareUniv.declare_univ_binders (GlobRef.IndRef (mind,0)) ubinders;
  List.iteri (fun i (indimpls, constrimpls) ->
      let ind = (mind,i) in
      let gr = GlobRef.IndRef ind in
      Impargs.maybe_declare_manual_implicits false gr indimpls;
      List.iteri
        (fun j impls ->
           Impargs.maybe_declare_manual_implicits false
             (GlobRef.ConstructRef (ind, succ j)) impls)
        constrimpls)
    impls;
  Flags.if_verbose Feedback.msg_info (minductive_message names);
  if is_template then
    List.iteri (fun i _ -> Equality.set_keep_equality (mind, i) true) mie.mind_entry_inds;
  if mie.mind_entry_private == None
  then Indschemes.declare_default_schemes mind;
  mind

module Internal =
struct
  type nonrec inductive_obj = inductive_obj
  let objInductive = objInductive
end
