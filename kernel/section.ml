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

type _ section_kind =
| SecMono : [ `mono ] section_kind
| SecPoly : [ `poly ] section_kind

type _ section_universes =
| SecMonoUniv : [ `mono ] section_universes
| SecPolyUniv : Name.t array * UContext.t -> [ `poly ] section_universes

type section_entry =
| SecDefinition of Constant.t
| SecInductive of MutInd.t

type 'a entry_map = 'a Cmap.t * 'a Mindmap.t

type 'a section = {
  sec_context : int;
  (** Length of the named context suffix that has been introduced locally *)
  sec_universes : 'a section_universes;
  (** Universes local to the section *)
  sec_entries : section_entry list;
  (** Definitions introduced in the section *)
  sec_data : 'a section_universes entry_map;
}

(** Sections can be nested with the proviso that no monomorphic section can be
    opened inside a polymorphic one. The reverse is allowed. *)
type t = {
  sec_poly : [ `poly ] section list;
  sec_mono : [ `mono ] section list;
}

let empty = {
  sec_poly = [];
  sec_mono = [];
}

let is_empty s =
  List.is_empty s.sec_poly && List.is_empty s.sec_mono

let is_polymorphic s =
  not (List.is_empty s.sec_poly)

let find_emap e (cmap, imap) = match e with
| SecDefinition con -> Cmap.find con cmap
| SecInductive ind -> Mindmap.find ind imap

let add_emap e v (cmap, imap) = match e with
| SecDefinition con -> (Cmap.add con v cmap, imap)
| SecInductive ind -> (cmap, Mindmap.add ind v imap)

type on_sec = { on_sec : 'a. 'a section_kind -> 'a section -> 'a section }

let on_last_section f { sec_poly; sec_mono } = match sec_poly, sec_mono with
| [], [] -> CErrors.user_err (Pp.str "No opened section")
| sec :: rem, _ ->
  let sec_poly = f.on_sec SecPoly sec :: rem in
  { sec_mono; sec_poly }
| [], sec :: rem ->
  let sec_mono = f.on_sec SecMono sec :: rem in
  { sec_mono; sec_poly }

type 'r with_sec = { with_sec : 'a. ('a section_kind * 'a section) option -> 'r }

let with_last_section f { sec_poly; sec_mono } = match sec_poly, sec_mono with
| [], [] -> f.with_sec None
| sec :: _, _ -> f.with_sec (Some (SecPoly, sec))
| [], sec :: _ -> f.with_sec (Some (SecMono, sec))

let push_local s =
  let on_sec _ sec = { sec with sec_context = sec.sec_context + 1 } in
  on_last_section { on_sec } s

let push_context (nas, ctx) s =
  let on_sec (type a) (kind : a section_kind) (sec : a section) : a section = match kind with
  | SecMono ->
    CErrors.anomaly (Pp.str "Adding polymorphic constraints to monomorphic section")
  | SecPoly ->
    let SecPolyUniv (snas, sctx) = sec.sec_universes in
    let sec_universes = SecPolyUniv (Array.append snas nas, UContext.union sctx ctx) in
    { sec with sec_universes }
  in
  on_last_section { on_sec } s

let open_section ~poly sections =
  if poly then
    let sec = {
      sec_context = 0;
      sec_universes = SecPolyUniv ([||], Univ.UContext.empty);
      sec_entries = [];
      sec_data = (Cmap.empty, Mindmap.empty);
    } in
    { sections with sec_poly = sec :: sections.sec_poly }
  else if List.is_empty sections.sec_poly then
    let sec = {
      sec_context = 0;
      sec_universes = SecMonoUniv;
      sec_entries = [];
      sec_data = (Cmap.empty, Mindmap.empty);
    } in
    { sections with sec_mono = sec :: sections.sec_mono }
  else
    CErrors.user_err (Pp.str "Cannot open a monomorphic section inside a polymorphic one")

let close_section sections =
  (* TODO: implement me correctly when discharging in kernel *)
  match sections.sec_poly, sections.sec_mono with
  | _sec :: psecs, _ ->
    let sections = { sections with sec_poly = psecs } in
    sections
  | [], _sec :: msecs ->
    let sections = { sections with sec_mono = msecs } in
    sections
  | [], [] ->
    CErrors.user_err (Pp.str "No opened section.")

let same_poly (type a) ~poly (knd : a section_kind) = match knd with
| SecPoly -> poly
| SecMono -> not poly

let push_global ~poly e s =
  if is_empty s then s
  else
    let on_sec knd sec =
      if same_poly ~poly knd then { sec with
        sec_entries = e :: sec.sec_entries;
        sec_data = add_emap e sec.sec_universes sec.sec_data;
      } else
        CErrors.user_err (Pp.str "Cannot mix universe polymorphic and \
          monomorphic declarations in sections.")
    in
    on_last_section { on_sec } s

let push_constant ~poly con s = push_global ~poly (SecDefinition con) s

let push_inductive ~poly ind s = push_global ~poly (SecInductive ind) s

type abstr_info = {
  abstr_ctx : Constr.named_context;
  abstr_subst : Univ.Instance.t;
  abstr_uctx : Univ.AUContext.t;
}

let empty_segment = {
  abstr_ctx = [];
  abstr_subst = Instance.empty;
  abstr_uctx = AUContext.empty;
}

let extract_hyps sec vars hyps =
  (* FIXME: this code is fishy. It is supposed to check that declared section
     variables are an ordered subset of the ambient ones, but it doesn't check
     e.g. uniqueness of naming nor convertibility of the section data. *)
  let rec aux ids hyps = match ids, hyps with
  | id :: ids, decl :: hyps when Names.Id.equal id (NamedDecl.get_id decl) ->
    decl :: aux ids hyps
  | _ :: ids, hyps ->
    aux ids hyps
  | [], _ -> []
  in
  let ids = List.map NamedDecl.get_id @@ List.firstn sec.sec_context vars in
  aux ids hyps

let section_segment_of_entry vars e hyps sections =
  (* [vars] are the named hypotheses, [hyps] the subset that is declared by the
    global *)
  let with_sec (type a) (s : (a section_kind * a section) option) = match s with
  | None ->
    CErrors.user_err (Pp.str "No opened section.")
  | Some (knd, sec) ->
    let hyps = extract_hyps sec vars hyps in
    let inst, auctx = match knd, find_emap e sec.sec_data with
    | SecMono, SecMonoUniv ->
      Instance.empty, AUContext.empty
    | SecPoly, SecPolyUniv (nas, ctx) ->
      Univ.abstract_universes nas ctx
    in
    {
      abstr_ctx = hyps;
      abstr_subst = inst;
      abstr_uctx = auctx;
    }
  in
  with_last_section { with_sec } sections

let segment_of_constant env con s =
  let body = Environ.lookup_constant con env in
  let vars = Environ.named_context env in
  section_segment_of_entry vars (SecDefinition con) body.Declarations.const_hyps s

let segment_of_inductive env mind s =
  let mib = Environ.lookup_mind mind env in
  let vars = Environ.named_context env in
  section_segment_of_entry vars (SecInductive mind) mib.Declarations.mind_hyps s

let instance_from_variable_context =
  List.rev %> List.filter NamedDecl.is_local_assum %> List.map NamedDecl.get_id %> Array.of_list

let extract_worklist info =
  let args = instance_from_variable_context info.abstr_ctx in
  info.abstr_subst, args

let replacement_context env s =
  let with_sec sec = match sec with
  | None -> CErrors.user_err (Pp.str "No opened section.")
  | Some (_, sec) ->
    let cmap, imap = sec.sec_data in
    let cmap = Cmap.mapi (fun con _ -> extract_worklist @@ segment_of_constant env con s) cmap in
    let imap = Mindmap.mapi (fun ind _ -> extract_worklist @@ segment_of_inductive env ind s) imap in
    (cmap, imap)
  in
  with_last_section { with_sec } s

let is_in_section env gr s =
  let with_sec sec = match sec with
  | None -> false
  | Some (_, sec) ->
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
  with_last_section { with_sec } s

let is_polymorphic_univ u s =
  let check sec =
    let SecPolyUniv (_, uctx) = sec.sec_universes in
    Array.mem u (Instance.to_array (UContext.instance uctx))
  in
  List.exists check s.sec_poly
