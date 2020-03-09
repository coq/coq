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
open Impargs

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
let declare_definition ~name ~scope ~kind ?hook_data ~ubind ~impargs ce =
  let should_suggest = ce.Declare.proof_entry_opaque &&
                       Option.is_empty ce.Declare.proof_entry_secctx in
  let dref = match scope with
  | Discharge ->
    let () = declare_variable ~name ~kind (SectionLocalDef ce) in
    if should_suggest then Proof_using.suggest_variable (Global.env ()) name;
    Names.GlobRef.VarRef name
  | Global local ->
    let kn = declare_constant ~name ~local ~kind (DefinitionEntry ce) in
    let gr = Names.GlobRef.ConstRef kn in
    if should_suggest then Proof_using.suggest_constant (Global.env ()) kn;
    let () = DeclareUniv.declare_univ_binders gr ubind in
    gr
  in
  let () = maybe_declare_manual_implicits false dref impargs in
  let () = definition_message name in
  begin
    match hook_data with
    | None -> ()
    | Some (hook, uctx, obls) ->
      Hook.call ~hook { Hook.S.uctx; obls; scope; dref }
  end;
  dref

let declare_definition ~name ~scope ~kind ?hook_data ~ubind ~impargs ce =
  let fix_exn = Declare.Internal.get_fix_exn ce in
  try declare_definition ~name ~scope ~kind ?hook_data ~ubind ~impargs ce
  with exn ->
    let exn = Exninfo.capture exn in
    Exninfo.iraise (fix_exn exn)

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
  let ubind, univs =
    (* XXX: Obligations don't do this, this seems like a bug? *)
    if restrict_ucontext
    then
      let evd = Evd.from_ctx uctx in
      let evd = Evd.restrict_universe_context evd vars in
      let univs = Evd.check_univ_decl ~poly evd udecl in
      Evd.universe_binders evd, univs
    else
      let univs = UState.univ_entry ~poly uctx in
      UnivNames.empty_binders, univs
  in
  let csts = CList.map2
      (fun Recthm.{ name; typ; impargs } body ->
         let ce = Declare.definition_entry ~opaque ~types:typ ~univs body in
         declare_definition ~name ~scope ~kind ~ubind ~impargs ce)
      fixitems fixdecls
  in
  let isfix = Option.is_empty possible_indexes in
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

let check_definition_evars ~allow_evars sigma =
  let env = Global.env () in
  if not allow_evars then Pretyping.check_evars_are_solved ~program_mode:false env sigma

let prepare_definition ~allow_evars ?opaque ?inline ~poly ~udecl ~types ~body sigma =
  check_definition_evars ~allow_evars sigma;
  let sigma, (body, types) = Evarutil.finalize ~abort_on_undefined_evars:(not allow_evars)
      sigma (fun nf -> nf body, Option.map nf types)
  in
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  sigma, definition_entry ?opaque ?inline ?types ~univs body

let prepare_parameter ~allow_evars ~poly ~udecl ~types sigma =
  check_definition_evars ~allow_evars sigma;
  let sigma, typ = Evarutil.finalize ~abort_on_undefined_evars:(not allow_evars)
      sigma (fun nf -> nf types)
  in
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  sigma, (None(*proof using*), (typ, univs), None(*inline*))
