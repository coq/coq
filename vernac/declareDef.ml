(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Decl_kinds
open Declare
open Globnames
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
      let e = CErrors.push e in
      let e = Option.cata (fun fix -> fix e) e fix_exn in
      Util.iraise e
end

(* Locality stuff *)
let declare_definition ~name ~scope ~kind ?hook_data udecl ce imps =
  let fix_exn = Future.fix_exn_of ce.Proof_global.proof_entry_body in
  let gr = match scope with
  | Discharge ->
      let _ = declare_variable name (Lib.cwd(), SectionLocalDef ce, IsDefinition kind) in
      VarRef name
  | Global local ->
      let kn = declare_constant name ~local (DefinitionEntry ce, IsDefinition kind) in
      let gr = ConstRef kn in
      let () = Declare.declare_univ_binders gr udecl in
      gr
  in
  let () = maybe_declare_manual_implicits false gr imps in
  let () = definition_message name in
  begin
    match hook_data with
    | None -> ()
    | Some (hook, uctx, obls) ->
      Hook.call ~fix_exn ~hook { Hook.S.uctx; obls; scope; dref = gr }
  end;
  gr

let declare_fix ?(opaque = false) ?hook_data ~name ~scope ~kind udecl univs ((def,_),eff) t imps =
  let ce = definition_entry ~opaque ~types:t ~univs ~eff def in
  declare_definition ~name ~scope ~kind ?hook_data udecl ce imps

let check_definition_evars ~allow_evars sigma =
  let env = Global.env () in
  if not allow_evars then Pretyping.check_evars_are_solved ~program_mode:false env sigma

let prepare_definition ~allow_evars ?opaque ?inline ~poly sigma udecl ~types ~body =
  check_definition_evars ~allow_evars sigma;
  let sigma, (body, types) = Evarutil.finalize ~abort_on_undefined_evars:(not allow_evars)
      sigma (fun nf -> nf body, Option.map nf types)
  in
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  sigma, definition_entry ?opaque ?inline ?types ~univs body

let prepare_parameter ~allow_evars ~poly sigma udecl typ =
  check_definition_evars ~allow_evars sigma;
  let sigma, typ = Evarutil.finalize ~abort_on_undefined_evars:(not allow_evars)
      sigma (fun nf -> nf typ)
  in
  let univs = Evd.check_univ_decl ~poly sigma udecl in
  sigma, (None(*proof using*), (typ, univs), None(*inline*))
