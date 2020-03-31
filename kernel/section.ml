(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Univ

module NamedDecl = Context.Named.Declaration

type section_entry =
| SecDefinition of Constant.t
| SecInductive of MutInd.t

type 'a entry_map = 'a Cmap.t * 'a Mindmap.t

type 'a t = {
  prev : 'a t option;
  (** Section surrounding the current one *)
  context : int;
  (** Length of the named context suffix that has been introduced locally *)
  mono_universes : ContextSet.t;
  poly_universes : Name.t array * UContext.t;
  (** Universes local to the section *)
  all_poly_univs : Univ.Level.t array;
  (** All polymorphic universes, including from previous sections. *)
  has_poly_univs : bool;
  (** Are there polymorphic universes or constraints, including in previous sections. *)
  entries : section_entry list;
  (** Definitions introduced in the section *)
  data : (Instance.t * AUContext.t) entry_map;
  (** Additional data synchronized with the section *)
  custom : 'a;
}

let rec depth sec = 1 + match sec.prev with None -> 0 | Some prev -> depth prev

let has_poly_univs sec = sec.has_poly_univs

let all_poly_univs sec = sec.all_poly_univs

let map_custom f sec = {sec with custom = f sec.custom}

let find_emap e (cmap, imap) = match e with
| SecDefinition con -> Cmap.find con cmap
| SecInductive ind -> Mindmap.find ind imap

let add_emap e v (cmap, imap) = match e with
| SecDefinition con -> (Cmap.add con v cmap, imap)
| SecInductive ind -> (cmap, Mindmap.add ind v imap)

let push_local sec =
  { sec with context = sec.context + 1 }

let push_context (nas, ctx) sec =
  if UContext.is_empty ctx then sec
  else
    let (snas, sctx) = sec.poly_universes in
    let poly_universes = (Array.append snas nas, UContext.union sctx ctx) in
    let all_poly_univs =
      Array.append sec.all_poly_univs (Instance.to_array @@ UContext.instance ctx)
    in
    { sec with poly_universes; all_poly_univs; has_poly_univs = true }

let rec is_polymorphic_univ u sec =
  let (_, uctx) = sec.poly_universes in
  let here = Array.exists (fun u' -> Level.equal u u') (Instance.to_array (UContext.instance uctx)) in
  here || Option.cata (is_polymorphic_univ u) false sec.prev

let push_constraints uctx sec =
  if sec.has_poly_univs &&
     Constraint.exists
       (fun (l,_,r) -> is_polymorphic_univ l sec || is_polymorphic_univ r sec)
       (snd uctx)
  then CErrors.user_err
      Pp.(str "Cannot add monomorphic constraints which refer to section polymorphic universes.");
  let uctx' = sec.mono_universes in
  let mono_universes =  (ContextSet.union uctx uctx') in
  { sec with mono_universes }

let open_section ~custom prev =
  {
    prev;
    context = 0;
    mono_universes = ContextSet.empty;
    poly_universes = ([||], UContext.empty);
    all_poly_univs = Option.cata (fun sec -> sec.all_poly_univs) [| |] prev;
    has_poly_univs = Option.cata has_poly_univs false prev;
    entries = [];
    data = (Cmap.empty, Mindmap.empty);
    custom = custom;
  }

let close_section sec =
  sec.prev, sec.entries, sec.mono_universes, sec.custom

let make_decl_univs (nas,uctx) = abstract_universes nas uctx

let push_global ~poly e sec =
  if has_poly_univs sec && not poly
  then CErrors.user_err
      Pp.(str "Cannot add a universe monomorphic declaration when \
               section polymorphic universes are present.")
  else
    { sec with
      entries = e :: sec.entries;
      data = add_emap e (make_decl_univs sec.poly_universes) sec.data;
    }

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
  let vars = List.firstn sec.context vars in
  (* Only keep the part that is used by the declaration *)
  List.filter (fun d -> Id.Set.mem (NamedDecl.get_id d) used) vars

let section_segment_of_entry vars e hyps sec =
  (* [vars] are the named hypotheses, [hyps] the subset that is declared by the
     global *)
  let hyps = extract_hyps sec vars hyps in
  let inst, auctx = find_emap e sec.data in
  {
    abstr_ctx = hyps;
    abstr_subst = inst;
    abstr_uctx = auctx;
  }

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

let replacement_context env sec =
  let cmap, imap = sec.data in
  let cmap = Cmap.mapi (fun con _ -> extract_worklist @@ segment_of_constant env con sec) cmap in
  let imap = Mindmap.mapi (fun ind _ -> extract_worklist @@ segment_of_inductive env ind sec) imap in
  (cmap, imap)

let is_in_section env gr sec =
  let open GlobRef in
  match gr with
  | VarRef id ->
    let vars = List.firstn sec.context (Environ.named_context env) in
    List.exists (fun decl -> Id.equal id (NamedDecl.get_id decl)) vars
  | ConstRef con ->
    Cmap.mem con (fst sec.data)
  | IndRef (ind, _) | ConstructRef ((ind, _), _) ->
    Mindmap.mem ind (snd sec.data)
