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
  mono_universes : Univ.ContextSet.t;
  (** Global universes introduced in the section *)
  poly_universes : UContext.t;
  (** Universes local to the section *)
  all_poly_univs : UContext.t list;
  (** All polymorphic universe contexts, including from previous sections. *)
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

let poly_universes sec = sec.poly_universes

let all_poly_univs sec = sec.all_poly_univs

let section_qvar_count sec =
  CList.fold_left (fun c uctx -> c +
    (fst @@ UVars.LevelInstance.length @@ UVars.UContext.instance uctx)) 0 (all_poly_univs sec)

let map_custom f sec = {sec with custom = f sec.custom}

let add_emap e v (cmap, imap) = match e with
| SecDefinition con -> (Cmap.add con v cmap, imap)
| SecInductive ind -> (cmap, Mindmap.add ind v imap)

let push_local_universe_context ctx sec =
  if UContext.is_empty ctx then sec
  else
    let sctx = sec.poly_universes in
    let poly_universes = UContext.union sctx ctx in
    let all_poly_univs = match sec.all_poly_univs with
      | [] -> assert false
      | hd :: tl ->
        UContext.union hd ctx :: tl
    in
    { sec with poly_universes; all_poly_univs; has_poly_univs = true }

let is_polymorphic_univ u sec =
  let test uctx =
    let _, us = LevelInstance.to_array @@ UContext.instance uctx in
    Array.exists (fun u' -> Level.equal u u') us
  in List.exists test sec.all_poly_univs

let push_level_constraints uctx sec =
  if sec.has_poly_univs &&
     UnivConstraints.exists
       (fun (l,_,r) ->
        Universe.exists (fun (l, _) -> is_polymorphic_univ l sec) l ||
        Universe.exists (fun (l, _) -> is_polymorphic_univ l sec) r)
       (snd uctx)
  then CErrors.user_err
      Pp.(str "Cannot add monomorphic constraints which refer to section polymorphic universes.");
  let uctx' = sec.mono_universes in
  let mono_universes = Univ.ContextSet.union uctx uctx' in
  { sec with mono_universes }

let open_section ~custom prev =
  {
    prev;
    context = [];
    mono_universes = Univ.ContextSet.empty;
    poly_universes = UContext.empty;
    all_poly_univs = UContext.empty :: Option.cata (fun sec -> sec.all_poly_univs) [] prev;
    has_poly_univs = Option.cata has_poly_univs false prev;
    entries = [];
    expand_info_map = (Cmap.empty, Mindmap.empty);
    cooking_info_map = (Cmap.empty, Mindmap.empty);
    custom = custom;
  }

let close_section sec =
  sec.prev, sec.entries, sec.mono_universes, sec.custom

let push_local d sec =
  { sec with context = d :: sec.context }

let extract_hyps vars used =
  (* Only keep the part that is used by the declaration *)
  List.filter (fun d -> Id.Set.mem (NamedDecl.get_id d) used) vars

(* let mentions univ univs = Univ.Universe.exists (fun (l, _) -> Level.Set.mem l univs) univ *)

(* [restrict_uctx uctx hyps] Restrict the context quantification to universes in [hyps],
  and filters out constraints not mentionning [hyps]. *)
(* let restrict_uctx uctx hyps =
  let _qvars, lvars = LevelInstance.levels hyps in
  let uinst, cstrs = UContext.instance uctx, UContext.constraints uctx in
  let names = UContext.names uctx in
  let qs, us = LevelInstance.to_array uinst in
  let names', us' = List.filter2 (fun _ i -> Univ.Level.Set.mem i lvars) (Array.to_list names.univs) (Array.to_list us) in
  let names = { quals = names.quals; univs = Array.of_list names' } in
  let levels = LevelInstance.of_array (qs, Array.of_list us') in
  let qcstrs, ucstrs = cstrs in
  let ucstrs = Univ.UnivConstraints.filter (fun (l, _, r) -> mentions l lvars || mentions r lvars) ucstrs in
  Feedback.msg_debug Pp.(str"restricting section context from " ++ LevelInstance.pr Sorts.raw_printer uinst ++ str " to " ++
    LevelInstance.pr Sorts.raw_printer levels ++ str "hyps = " ++ LevelInstance.pr Sorts.raw_printer hyps);
  UContext.make names (levels, (qcstrs, ucstrs)) *)

let segment_of_entry env e sec =
  let hyps, univ_hyps =
    let open Declarations in
    match e with
    | SecDefinition con ->
      let cb = Environ.lookup_constant con env in
      cb.const_hyps, cb.const_univ_ctx
    | SecInductive mind ->
      let mib = Environ.lookup_mind mind env in
      mib.mind_hyps, mib.mind_univ_ctx
  in
  let hyps = Context.Named.to_vars hyps in
  (* [sec.context] are the named hypotheses, [hyps] the subset that is
     declared by the global *)
  let ctx = extract_hyps sec.context hyps in
  let uctx = match univ_hyps with hd :: _ -> hd | [] -> UContext.empty in
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
    let cooking_info, abstr_inst_info = segment_of_entry env e sec in
    let cooking_info_map = add_emap e cooking_info sec.cooking_info_map in
    let expand_info_map = add_emap e abstr_inst_info sec.expand_info_map in
    { sec with entries = e :: sec.entries; expand_info_map; cooking_info_map }

let segment_of_constant con sec = Cmap.find con (fst sec.cooking_info_map)
let segment_of_inductive con sec = Mindmap.find con (snd sec.cooking_info_map)

let is_in_section _env gr sec =
  let open GlobRef in
  match gr with
  | VarRef id ->
    let vars = sec.context in
    List.exists (fun decl -> Id.equal id (NamedDecl.get_id decl)) vars
  | ConstRef con ->
    Cmap.mem con (fst sec.expand_info_map)
  | IndRef (ind, _) | ConstructRef ((ind, _), _) ->
    Mindmap.mem ind (snd sec.expand_info_map)
