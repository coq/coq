(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Entries

type indlocs = (Loc.t option * Loc.t option list) list

(** Declaration of inductive blocks *)
let declare_inductive_argument_scopes kn mie =
  List.iteri (fun i {mind_entry_consnames=lc} ->
    Notation.declare_ref_arguments_scope (GlobRef.IndRef (kn,i));
    for j=1 to List.length lc do
      Notation.declare_ref_arguments_scope (GlobRef.ConstructRef ((kn,i),j));
    done) mie.mind_entry_inds

type inductive_obj = {
  ind_names : (lident * lident list) list
  (* For each block, name of the type + name of constructors *)
}

let inductive_names sp kn obj =
  let (dp,_) = Libnames.repr_path sp in
  let kn = Global.mind_of_delta_kn kn in
  let names, _ =
    List.fold_left
      (fun (names, n) ({CAst.v=typename; loc=typeloc}, consnames) ->
         let ind_p = (kn,n) in
         let names, _ =
           List.fold_left
             (fun (names, p) {CAst.v=l; loc} ->
                let sp = Libnames.make_path dp l in
                ((loc, sp, GlobRef.ConstructRef (ind_p,p)) :: names, p+1))
             (names, 1) consnames
         in
         let sp = Libnames.make_path dp typename in
         ((typeloc, sp, GlobRef.IndRef ind_p) :: names, n+1))
      ([], 0) obj.ind_names
  in names

let load_inductive i ((sp, kn), names) =
  let names = inductive_names sp kn names in
  List.iter (fun (loc, sp, ref) ->
      Nametab.push (Nametab.Until i) sp ref;
      Option.iter (Nametab.set_cci_src_loc (TrueGlobal ref)) loc)
    names

let open_inductive i ((sp, kn), names) =
  let names = inductive_names sp kn names in
  List.iter (fun (_, sp, ref) -> Nametab.push (Nametab.Exactly i) sp ref) names

let cache_inductive o =
  (* Until 1 and Exactly 1 are equivalent so no need to open_inductive *)
  load_inductive 1 o

let discharge_inductive names =
  Some names

let objInductive : (Id.t * inductive_obj) Libobject.Dyn.tag =
  let open Libobject in
  declare_named_object_full {(default_object "INDUCTIVE") with
    cache_function = cache_inductive;
    load_function = load_inductive;
    open_function = simple_open open_inductive;
    classify_function = (fun a -> Substitute);
    subst_function = ident_subst_function;
    discharge_function = discharge_inductive;
  }

let inInductive v = Libobject.Dyn.Easy.inj v objInductive

let cache_prim (p,c) = Structures.PrimitiveProjections.register p c

let load_prim _ p = cache_prim p

let subst_prim (subst,(p,c)) = Mod_subst.subst_proj_repr subst p, Mod_subst.subst_constant subst c

let discharge_prim (p,c) = Some (Lib.discharge_proj_repr p, c)

let inPrim : (Projection.Repr.t * Constant.t) -> Libobject.obj =
  let open Libobject in
  declare_object {
    (default_object "PRIMPROJS") with
    cache_function = cache_prim ;
    load_function = load_prim;
    subst_function = subst_prim;
    classify_function = (fun x -> Substitute);
    discharge_function = discharge_prim }

let declare_primitive_projection p c = Lib.add_leaf (inPrim (p,c))

let feedback_axiom () = Feedback.(feedback AddedAxiom)

let is_unsafe_typing_flags () =
  let open Declarations in
  let flags = Environ.typing_flags (Global.env()) in
  not (flags.check_universes && flags.check_guarded && flags.check_positive)

(* for initial declaration *)
let declare_mind ?typing_flags ~indlocs mie =
  let id = match mie.mind_entry_inds with
    | ind::_ -> ind.mind_entry_typename
    | [] -> CErrors.anomaly (Pp.str "cannot declare an empty list of inductives.") in
  let indlocs = Array.of_list indlocs in
  let map_names i mip =
    let typloc, conslocs = if Array.length indlocs <= i then None, []
      else indlocs.(i)
    in
    let typloc = if Option.has_some typloc then typloc else Loc.get_current_command_loc() in
    let typ = CAst.make ?loc:typloc mip.mind_entry_typename in
    let conslocs = Array.of_list conslocs in
    let map_cons j na =
      let consloc = if Array.length conslocs <= j then None
        else conslocs.(j)
      in
      let consloc = if Option.has_some consloc then consloc else typloc in
      CAst.make ?loc:consloc na
    in
    let consl = List.mapi map_cons mip.mind_entry_consnames in
    (typ, consl)
  in
  let names = List.mapi map_names mie.mind_entry_inds in
  List.iter (fun ({CAst.v=typ}, cons) ->
      Declare.check_exists typ;
      List.iter (fun {CAst.v} -> Declare.check_exists v) cons) names;
  let mind, why_not_prim_record = Global.add_mind ?typing_flags id mie in
  let () = Lib.add_leaf (inInductive (id, { ind_names = names })) in
  if is_unsafe_typing_flags() then feedback_axiom ();
  Impargs.declare_mib_implicits mind;
  declare_inductive_argument_scopes mind mie;
  mind, why_not_prim_record

let is_recursive mie =
  let open Constr in
  let rec is_recursive_constructor lift n typ =
    match Constr.kind typ with
    | Prod (_,arg,rest) ->
        not (Vars.noccur_between lift n arg) ||
        is_recursive_constructor (lift+1) n rest
    | LetIn (na,b,t,rest) -> is_recursive_constructor (lift+1) n rest
    | _ -> false
  in
  let nind = List.length mie.mind_entry_inds in
  let nparams = List.length mie.mind_entry_params in
  List.exists (fun ind -> List.exists (fun t -> is_recursive_constructor (nparams+1) nind t) ind.mind_entry_lc) mie.mind_entry_inds

let explain_not_prim_record reason =
  let open IndTyping.NotPrimRecordReason in
  let open Pp in
  match reason with
  | MustNotBeSquashed -> strbrk "it is squashed"
  | MustHaveRelevantProj -> strbrk "it is not in SProp but all projections may be irrelevant"
  | MustHaveProj -> strbrk "it has no projections"
  | MustNotHaveAnonProj -> strbrk "it has an anonymous projection"

let warn_non_primitive_record =
  CWarnings.create ~name:"non-primitive-record" ~category:CWarnings.CoreCategories.records
    Pp.(fun (mind,why_not_prim_record) ->
        hov 0
          (str "The record " ++ Nametab.pr_global_env Id.Set.empty (GlobRef.IndRef (mind,0)) ++
           strbrk" could not be defined as a primitive record because " ++
           explain_not_prim_record why_not_prim_record ++ str "."))

let minductive_message = function
  | []  -> CErrors.user_err Pp.(str "No inductive definition.")
  | [x] -> Pp.(Id.print x ++ str " is defined")
  | l   -> Pp.(hov 0 (prlist_with_sep pr_comma Id.print l ++
                      spc () ++ str "are defined"))

type one_inductive_impls =
  Impargs.manual_implicits (* for inds *) *
  Impargs.manual_implicits list (* for constrs *)

let { Goptions.get = default_prop_dep_elim } =
  Goptions.declare_bool_option_and_ref ~key:["Dependent";"Proposition";"Eliminators"] ~value:false ()

type default_dep_elim = DefaultElim | PropButDepElim

let declare_mutual_inductive_with_eliminations ?typing_flags ?(indlocs=[]) ?default_dep_elim mie ubinders impls =
  (* spiwack: raises an error if the structure is supposed to be non-recursive,
        but isn't *)
  begin match mie.mind_entry_finite with
  | Declarations.BiFinite ->
    if is_recursive mie then
      if Option.has_some mie.mind_entry_record then
        CErrors.user_err Pp.(strbrk "Records declared with the keywords Record or Structure cannot be recursive. You can, however, define recursive records using the Inductive or CoInductive command.")
      else
        CErrors.user_err Pp.(strbrk "Types declared with the keyword Variant cannot be recursive. Recursive types are defined with the Inductive and CoInductive command.");
    if not (Int.equal (List.length mie.mind_entry_inds) 1) then
      if Option.has_some mie.mind_entry_record then
        CErrors.user_err Pp.(strbrk "Keywords Record and Structure are to define a single type at once.")
      else
        CErrors.user_err Pp.(strbrk "Keyword Variant is to define a single type at once.")
    | _ -> ()
  end;
  let names = List.map (fun e -> e.mind_entry_typename) mie.mind_entry_inds in
  let mind, why_not_prim_record = declare_mind ?typing_flags ~indlocs mie in
  why_not_prim_record |> Option.iter (fun why_not_prim_record ->
      warn_non_primitive_record (mind,why_not_prim_record));
  let () = match fst ubinders with
    | UState.Polymorphic_entry _ -> ()
    | UState.Monomorphic_entry ctx ->
      DeclareUniv.add_constraint_source (IndRef (mind,0)) ctx
  in
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
  let () = match default_dep_elim with
    | None -> ()
    | Some defaults ->
      List.iteri (fun i default ->
          let ind = (mind, i) in
          let prop_but_default_dep_elim = match default with
            | PropButDepElim -> true
            | DefaultElim ->
              default_prop_dep_elim () &&
              let _, mip = Global.lookup_inductive ind in
              Sorts.is_prop mip.mind_sort
          in
          if prop_but_default_dep_elim then
            Indrec.declare_prop_but_default_dependent_elim ind)
        defaults
  in
  Flags.if_verbose Feedback.msg_info (minductive_message names);
  let indlocs = List.map fst indlocs in
  let locmap = Ind_tables.Locmap.make mind indlocs in
  if mie.mind_entry_private == None
  then Indschemes.declare_default_schemes mind ~locmap;
  mind

module Internal =
struct
  type nonrec inductive_obj = inductive_obj
  let objInductive = objInductive
end
