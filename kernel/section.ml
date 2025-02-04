(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
open UVars
open Cooking

module NamedDecl = Context.Named.Declaration

type section_entry =
| SecDefinition of Constant.t
| SecInductive of MutInd.t

type 'a t = {
  prev : 'a t option;
  (** Section surrounding the current one *)
  entries : section_entry list;
  (** Global declarations introduced in the section *)
  context : Constr.named_context;
  (** Declarations local to the section, intended to be interleaved
      with global declarations *)
  mono_universes : ContextSet.t;
  (** Global universes introduced in the section *)
  poly_universes : UContext.t;
  (** Universes local to the section *)
  all_poly_univs : Instance.t;
  (** All polymorphic universes, including from previous sections. *)
  has_poly_univs : bool;
  (** Are there polymorphic universes or constraints, including in previous sections. *)
  expand_info_map : expand_info;
  (** Tells how to re-instantiate global declarations when they are
      generalized *)
  cooking_info_map : cooking_info entry_map;
  custom : 'a;
}

let rec depth sec = 1 + match sec.prev with None -> 0 | Some prev -> depth prev

let has_poly_univs sec = sec.has_poly_univs

let all_poly_univs sec = sec.all_poly_univs

let map_custom f sec = {sec with custom = f sec.custom}

let add_emap e v (cmap, imap) = match e with
| SecDefinition con -> (Cmap_env.add con v cmap, imap)
| SecInductive ind -> (cmap, Mindmap_env.add ind v imap)

let push_local_universe_context ctx sec =
  if UContext.is_empty ctx then sec
  else
    let sctx = sec.poly_universes in
    let poly_universes = UContext.union sctx ctx in
    let all_poly_univs = Instance.append sec.all_poly_univs (UContext.instance ctx) in
    { sec with poly_universes; all_poly_univs; has_poly_univs = true }

let is_polymorphic_univ u sec =
  let _, us = Instance.to_array sec.all_poly_univs in
  Array.exists (fun u' -> Level.equal u u') us

let push_constraints uctx sec =
  if sec.has_poly_univs &&
     Constraints.exists
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
    context = [];
    mono_universes = ContextSet.empty;
    poly_universes = UContext.empty;
    all_poly_univs = Option.cata (fun sec -> sec.all_poly_univs) Instance.empty prev;
    has_poly_univs = Option.cata has_poly_univs false prev;
    entries = [];
    expand_info_map = (Cmap_env.empty, Mindmap_env.empty);
    cooking_info_map = (Cmap_env.empty, Mindmap_env.empty);
    custom = custom;
  }

let close_section sec =
  sec.prev, sec.entries, sec.mono_universes, sec.custom

let push_local d sec =
  { sec with context = d :: sec.context }

let extract_hyps vars used =
  (* Only keep the part that is used by the declaration *)
  List.filter (fun d -> Id.Set.mem (NamedDecl.get_id d) used) vars

let segment_of_entry env e uctx sec =
  let hyps = match e with
  | SecDefinition con -> (Environ.lookup_constant con env).Declarations.const_hyps
  | SecInductive mind -> (Environ.lookup_mind mind env).Declarations.mind_hyps
  in
  let hyps = Context.Named.to_vars hyps in
  (* [sec.context] are the named hypotheses, [hyps] the subset that is
     declared by the global *)
  let ctx = extract_hyps sec.context hyps in
  (* Add recursive calls: projections are recursively referring to the
     mind they belong to *)
  let recursive = match e with
  | SecDefinition _ -> None
  | SecInductive ind -> Some ind
  in
  Cooking.make_cooking_info ~recursive sec.expand_info_map ctx uctx

let push_global env ~poly e sec =
  if has_poly_univs sec && not poly
  then CErrors.user_err
      Pp.(str "Cannot add a universe monomorphic declaration when \
               section polymorphic universes are present.")
  else
    let cooking_info, abstr_inst_info = segment_of_entry env e sec.poly_universes sec in
    let cooking_info_map = add_emap e cooking_info sec.cooking_info_map in
    let expand_info_map = add_emap e abstr_inst_info sec.expand_info_map in
    { sec with entries = e :: sec.entries; expand_info_map; cooking_info_map }

let segment_of_constant con sec = Cmap_env.find con (fst sec.cooking_info_map)
let segment_of_inductive con sec = Mindmap_env.find con (snd sec.cooking_info_map)

let is_in_section _env gr sec =
  let open GlobRef in
  match gr with
  | VarRef id ->
    let vars = sec.context in
    List.exists (fun decl -> Id.equal id (NamedDecl.get_id decl)) vars
  | ConstRef con ->
    Cmap_env.mem con (fst sec.expand_info_map)
  | IndRef (ind, _) | ConstructRef ((ind, _), _) ->
    Mindmap_env.mem ind (snd sec.expand_info_map)
