(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declare

type locality = Discharge | Global of Declare.import_status

(* Hooks naturally belong here as they apply to both definitions and lemmas *)
module Hook = struct
  module S = struct
    type t =
      { uctx : UState.t
      (** [ustate]: universe constraints obtained when the term was closed *)
      ; obls : (Names.Id.t * Constr.t) list
      (** [(n1,t1),...(nm,tm)]: association list between obligation
          name and the corresponding defined term (might be a constant,
          but also an arbitrary term in the Expand case of obligations) *)
      ; scope : locality
      (**  [locality]: Locality of the original declaration *)
      ; dref : Names.GlobRef.t
      (** [ref]: identifier of the original declaration *)
      }
  end

  type t = (S.t -> unit) CEphemeron.key

  let make hook = CEphemeron.create hook

  let call ?hook x = Option.iter (fun hook -> CEphemeron.get hook x) hook

end

(* Locality stuff *)
let declare_entry ~name ~scope ~kind ?hook ?(obls=[]) ~impargs ~uctx entry =
  let should_suggest = entry.Declare.proof_entry_opaque &&
                       Option.is_empty entry.Declare.proof_entry_secctx in
  let ubind = UState.universe_binders uctx in
  let dref = match scope with
  | Discharge ->
    let () = declare_variable ~name ~kind (SectionLocalDef entry) in
    if should_suggest then Proof_using.suggest_variable (Global.env ()) name;
    Names.GlobRef.VarRef name
  | Global local ->
    let kn = declare_constant ~name ~local ~kind (DefinitionEntry entry) in
    let gr = Names.GlobRef.ConstRef kn in
    if should_suggest then Proof_using.suggest_constant (Global.env ()) kn;
    let () = DeclareUniv.declare_univ_binders gr ubind in
    gr
  in
  let () = Impargs.maybe_declare_manual_implicits false dref impargs in
  let () = definition_message name in
  Option.iter (fun hook -> Hook.call ~hook { Hook.S.uctx; obls; scope; dref }) hook;
  dref

let mutual_make_bodies ~fixitems ~rec_declaration ~possible_indexes =
  match possible_indexes with
  | Some possible_indexes ->
    let env = Global.env() in
    let indexes = Pretyping.search_guard env possible_indexes rec_declaration in
    let vars = Vars.universes_of_constr (Constr.mkFix ((indexes,0),rec_declaration)) in
    let fixdecls = CList.map_i (fun i _ -> Constr.mkFix ((indexes,i),rec_declaration)) 0 fixitems in
    vars, fixdecls, Some indexes
  | None ->
    let fixdecls = CList.map_i (fun i _ -> Constr.mkCoFix (i,rec_declaration)) 0 fixitems in
    let vars = Vars.universes_of_constr (List.hd fixdecls) in
    vars, fixdecls, None

module Recthm = struct
  type t =
    { name : Names.Id.t
    (** Name of theorem *)
    ; typ : Constr.t
    (** Type of theorem  *)
    ; args : Names.Name.t list
    (** Names to pre-introduce  *)
    ; impargs : Impargs.manual_implicits
    (** Explicitily declared implicit arguments  *)
    }
end

let declare_mutually_recursive ~opaque ~scope ~kind ~poly ~uctx ~udecl ~ntns ~rec_declaration ~possible_indexes ?(restrict_ucontext=true) fixitems =
  let vars, fixdecls, indexes =
    mutual_make_bodies ~fixitems ~rec_declaration ~possible_indexes in
  let uctx, univs =
    (* XXX: Obligations don't do this, this seems like a bug? *)
    if restrict_ucontext
    then
      let uctx = UState.restrict uctx vars in
      let univs = UState.check_univ_decl ~poly uctx udecl in
      uctx, univs
    else
      let univs = UState.univ_entry ~poly uctx in
      uctx, univs
  in
  let csts = CList.map2
      (fun Recthm.{ name; typ; impargs } body ->
         let entry = Declare.definition_entry ~opaque ~types:typ ~univs body in
         declare_entry ~name ~scope ~kind ~impargs ~uctx entry)
      fixitems fixdecls
  in
  let isfix = Option.has_some possible_indexes in
  let fixnames = List.map (fun { Recthm.name } -> name) fixitems in
  Declare.recursive_message isfix indexes fixnames;
  List.iter (Metasyntax.add_notation_interpretation (Global.env())) ntns;
  csts

let warn_let_as_axiom =
  CWarnings.create ~name:"let-as-axiom" ~category:"vernacular"
    Pp.(fun id -> strbrk "Let definition" ++ spc () ++ Names.Id.print id ++
                  spc () ++ strbrk "declared as an axiom.")

let declare_assumption ~name ~scope ~hook ~impargs ~uctx pe =
  let local = match scope with
    | Discharge -> warn_let_as_axiom name; Declare.ImportNeedQualified
    | Global local -> local
  in
  let kind = Decls.(IsAssumption Conjectural) in
  let decl = Declare.ParameterEntry pe in
  let kn = Declare.declare_constant ~name ~local ~kind decl in
  let dref = Names.GlobRef.ConstRef kn in
  let () = Impargs.maybe_declare_manual_implicits false dref impargs in
  let () = Declare.assumption_message name in
  let () = DeclareUniv.declare_univ_binders dref (UState.universe_binders uctx) in
  let () = Hook.(call ?hook { S.uctx; obls = []; scope; dref}) in
  dref

let declare_assumption ?fix_exn ~name ~scope ~hook ~impargs ~uctx pe =
  try declare_assumption ~name ~scope ~hook ~impargs ~uctx pe
  with exn ->
    let exn = Exninfo.capture exn in
    let exn = Option.cata (fun fix -> fix exn) exn fix_exn in
    Exninfo.iraise exn

(* Preparing proof entries *)

let prepare_definition ?opaque ?inline ?fix_exn ~poly ~udecl ~types ~body sigma =
  let env = Global.env () in
  Pretyping.check_evars_are_solved ~program_mode:false env sigma;
  let sigma, (body, types) = Evarutil.finalize ~abort_on_undefined_evars:true
      sigma (fun nf -> nf body, Option.map nf types)
  in
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  let entry = definition_entry ?fix_exn ?opaque ?inline ?types ~univs body in
  let uctx = Evd.evar_universe_context sigma in
  entry, uctx

let declare_definition ~name ~scope ~kind ~opaque ~impargs ~udecl ?hook
    ?obls ~poly ?inline ~types ~body ?fix_exn sigma =
  let entry, uctx = prepare_definition ?fix_exn ~opaque ~poly ~udecl ~types ~body ?inline sigma in
  declare_entry ~name ~scope ~kind ~impargs ?obls ?hook ~uctx entry

let prepare_obligation ?opaque ?inline ~name ~poly ~udecl ~types ~body sigma =
  let sigma, (body, types) = Evarutil.finalize ~abort_on_undefined_evars:false
      sigma (fun nf -> nf body, Option.map nf types)
  in
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  let ce = definition_entry ?opaque ?inline ?types ~univs body in
  let env = Global.env () in
  let (c,ctx), sideff = Future.force ce.Declare.proof_entry_body in
  assert(Safe_typing.is_empty_private_constants sideff.Evd.seff_private);
  assert(Univ.ContextSet.is_empty ctx);
  RetrieveObl.check_evars env sigma;
  let c = EConstr.of_constr c in
  let typ = match ce.Declare.proof_entry_type with
    | Some t -> EConstr.of_constr t
    | None -> Retyping.get_type_of env sigma c
  in
  let obls, _, c, cty = RetrieveObl.retrieve_obligations env name sigma 0 c typ in
  let uctx = Evd.evar_universe_context sigma in
  c, cty, uctx, obls

let prepare_parameter ~poly ~udecl ~types sigma =
  let env = Global.env () in
  Pretyping.check_evars_are_solved ~program_mode:false env sigma;
  let sigma, typ = Evarutil.finalize ~abort_on_undefined_evars:true
      sigma (fun nf -> nf types)
  in
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  sigma, (None(*proof using*), (typ, univs), None(*inline*))
