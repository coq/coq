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

  let call ?hook ?fix_exn x =
    try Option.iter (fun hook -> CEphemeron.get hook x) hook
    with e when CErrors.noncritical e ->
      let e = Exninfo.capture e in
      let e = Option.cata (fun fix -> fix e) e fix_exn in
      Exninfo.iraise e
end

(* Locality stuff *)
let declare_definition ~name ~scope ~kind ?hook_data ~ubind ~impargs ce =
  let fix_exn = Declare.Internal.get_fix_exn ce in
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
      Hook.call ~fix_exn ~hook { Hook.S.uctx; obls; scope; dref }
  end;
  dref

let declare_mutually_recursive ~cofix ~indexes ~opaque ~univs ~scope ~kind ~ubind fixnames fixdecls fixtypes fiximps =
  let csts = CList.map4
      (fun name body types impargs ->
         let ce = Declare.definition_entry ~opaque ~types ~univs body in
         declare_definition ~name ~scope ~kind ~ubind ~impargs ce)
      fixnames fixdecls fixtypes fiximps
  in
  Declare.recursive_message (not cofix) indexes fixnames;
  csts

let warn_let_as_axiom =
  CWarnings.create ~name:"let-as-axiom" ~category:"vernacular"
    Pp.(fun id -> strbrk "Let definition" ++ spc () ++ Names.Id.print id ++
                  spc () ++ strbrk "declared as an axiom.")

let declare_assumption ?fix_exn ~name ~scope ~hook ~impargs ~uctx pe =
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
  let () = Hook.(call ?fix_exn ?hook { S.uctx; obls = []; scope; dref}) in
  dref

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
