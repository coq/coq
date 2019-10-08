(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Univ

module NamedDecl = Context.Named.Declaration

type section_global_entry =
| SecDefinition of Constant.t
| SecInductive of MutInd.t

type section_entry =
| SecGlobal of section_global_entry
| SecUnivs of ContextSet.t

type 'a entry_map = 'a Cmap.t * 'a Mindmap.t

type 'a section = {
  sec_context : int;
  (** Length of the named context suffix that has been introduced locally *)
  sec_poly_universes : Name.t array * UContext.t;
  (** Universes local to the section *)
  has_poly_univs : bool;
  (** Are there polymorphic universes or constraints, including in previous sections. *)
  sec_entries : section_entry list;
  (** Definitions introduced in the section *)
  sec_data : (Instance.t * AUContext.t) entry_map;
  (** Additional data synchronized with the section *)
  sec_custom : 'a;
}

(** Sections can be nested with the proviso that no monomorphic section can be
    opened inside a polymorphic one. The reverse is allowed. *)
type 'a t = 'a section list

let empty = []

let is_empty = List.is_empty

let depth = List.length

let has_poly_univs = function
  | [] -> false
  | sec :: _ -> sec.has_poly_univs

let find_emap e (cmap, imap) = match e with
| SecDefinition con -> Cmap.find con cmap
| SecInductive ind -> Mindmap.find ind imap

let add_emap e v (cmap, imap) = match e with
| SecDefinition con -> (Cmap.add con v cmap, imap)
| SecInductive ind -> (cmap, Mindmap.add ind v imap)

let on_last_section f sections = match sections with
| [] -> CErrors.user_err (Pp.str "No opened section")
| sec :: rem -> f sec :: rem

let with_last_section f sections = match sections with
| [] -> f None
| sec :: _ -> f (Some sec)

let push_local s =
  let on_sec sec = { sec with sec_context = sec.sec_context + 1 } in
  on_last_section on_sec s

let push_context (nas, ctx) s =
    let on_sec sec =
      if UContext.is_empty ctx then sec
      else
        let (snas, sctx) = sec.sec_poly_universes in
        let sec_poly_universes = (Array.append snas nas, UContext.union sctx ctx) in
        { sec with sec_poly_universes; has_poly_univs = true }
    in
    on_last_section on_sec s

let is_polymorphic_univ u s =
  let check sec =
    let (_, uctx) = sec.sec_poly_universes in
    Array.exists (fun u' -> Level.equal u u') (Instance.to_array (UContext.instance uctx))
  in
  List.exists check s

let push_constraints uctx s =
  let on_sec sec =
    if sec.has_poly_univs && Constraint.exists (fun (l,_,r) -> is_polymorphic_univ l s || is_polymorphic_univ r s) (snd uctx)
    then CErrors.user_err Pp.(str "Cannot add monomorphic constraints which refer to section polymorphic universes.");
    { sec with sec_entries = SecUnivs uctx :: sec.sec_entries }
  in
  on_last_section on_sec s

let open_section ~custom sections =
  let sec = {
    sec_context = 0;
    sec_poly_universes = ([||], UContext.empty);
    has_poly_univs = has_poly_univs sections;
    sec_entries = [];
    sec_data = (Cmap.empty, Mindmap.empty);
    sec_custom = custom;
  } in
  sec :: sections

let close_section sections =
  match sections with
  | sec :: sections ->
    sections, sec.sec_entries, sec.sec_custom
  | [] ->
    CErrors.user_err (Pp.str "No opened section.")

let make_decl_univs (nas,uctx) = abstract_universes nas uctx

let push_global ~poly e s =
  if is_empty s then s
  else if has_poly_univs s && not poly
  then CErrors.user_err
      Pp.(str "Cannot add a universe monomorphic declaration when \
               section polymorphic universes are present.")
  else
    let on_sec sec =
      { sec with
        sec_entries = SecGlobal e :: sec.sec_entries;
        sec_data = add_emap e (make_decl_univs sec.sec_poly_universes) sec.sec_data;
      }
    in
    on_last_section on_sec s

let push_constant ~poly con s = push_global ~poly (SecDefinition con) s

let push_inductive ~poly ind s = push_global ~poly (SecInductive ind) s

type abstr_info = {
  abstr_ctx : Constr.named_context;
  abstr_subst : Instance.t;
  abstr_uctx : AUContext.t;
}

let empty_segment = {
  abstr_ctx = [];
  abstr_subst = Instance.empty;
  abstr_uctx = AUContext.empty;
}

let extract_hyps sec vars used =
  (* Keep the section-local segment of variables *)
  let vars = List.firstn sec.sec_context vars in
  (* Only keep the part that is used by the declaration *)
  List.filter (fun d -> Id.Set.mem (NamedDecl.get_id d) used) vars

let section_segment_of_entry vars e hyps sections =
  (* [vars] are the named hypotheses, [hyps] the subset that is declared by the
    global *)
  let with_sec s = match s with
  | None ->
    CErrors.user_err (Pp.str "No opened section.")
  | Some sec ->
    let hyps = extract_hyps sec vars hyps in
    let inst, auctx = find_emap e sec.sec_data in
    {
      abstr_ctx = hyps;
      abstr_subst = inst;
      abstr_uctx = auctx;
    }
  in
  with_last_section with_sec sections

let segment_of_constant env con s =
  let body = Environ.lookup_constant con env in
  let vars = Environ.named_context env in
  let used = Context.Named.to_vars body.Declarations.const_hyps in
  section_segment_of_entry vars (SecDefinition con) used s

let segment_of_inductive env mind s =
  let mib = Environ.lookup_mind mind env in
  let vars = Environ.named_context env in
  let used = Context.Named.to_vars mib.Declarations.mind_hyps in
  section_segment_of_entry vars (SecInductive mind) used s

let instance_from_variable_context =
  List.rev %> List.filter NamedDecl.is_local_assum %> List.map NamedDecl.get_id %> Array.of_list

let extract_worklist info =
  let args = instance_from_variable_context info.abstr_ctx in
  info.abstr_subst, args

let replacement_context env s =
  let with_sec sec = match sec with
  | None -> CErrors.user_err (Pp.str "No opened section.")
  | Some sec ->
    let cmap, imap = sec.sec_data in
    let cmap = Cmap.mapi (fun con _ -> extract_worklist @@ segment_of_constant env con s) cmap in
    let imap = Mindmap.mapi (fun ind _ -> extract_worklist @@ segment_of_inductive env ind s) imap in
    (cmap, imap)
  in
  with_last_section with_sec s

let is_in_section env gr s =
  let with_sec sec = match sec with
  | None -> false
  | Some sec ->
    let open GlobRef in
    match gr with
    | VarRef id ->
      let vars = List.firstn sec.sec_context (Environ.named_context env) in
      List.exists (fun decl -> Id.equal id (NamedDecl.get_id decl)) vars
    | ConstRef con ->
      Cmap.mem con (fst sec.sec_data)
    | IndRef (ind, _) | ConstructRef ((ind, _), _) ->
      Mindmap.mem ind (snd sec.sec_data)
  in
  with_last_section with_sec s
