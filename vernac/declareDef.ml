(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Decl_kinds
open Declare
open Entries
open Globnames
open Impargs

(* Hooks naturally belong here as they apply to both definitions and lemmas *)
module Hook = struct
  module S = struct
    type t = UState.t
      -> (Names.Id.t * Constr.t) list
      -> Decl_kinds.locality
      -> Names.GlobRef.t
      -> unit
  end

  type t = S.t CEphemeron.key

  let make hook = CEphemeron.create hook

  let call ?hook ?fix_exn uctx trans l c =
    try Option.iter (fun hook -> CEphemeron.get hook uctx trans l c) hook
    with e when CErrors.noncritical e ->
      let e = CErrors.push e in
      let e = Option.cata (fun fix -> fix e) e fix_exn in
      Util.iraise e
end

(* Locality stuff *)
let declare_definition ident (local, p, k) ?hook_data ce pl imps =
  let fix_exn = Future.fix_exn_of ce.const_entry_body in
  let gr = match local with
  | Discharge ->
      let _ = declare_variable ident (Lib.cwd(), SectionLocalDef ce, IsDefinition k) in
      VarRef ident
  | Global local ->
      let kn = declare_constant ident ~local (DefinitionEntry ce, IsDefinition k) in
      let gr = ConstRef kn in
      let () = Declare.declare_univ_binders gr pl in
      gr
  in
  let () = maybe_declare_manual_implicits false gr imps in
  let () = definition_message ident in
  begin
    match hook_data with
    | None -> ()
    | Some (hook, uctx, extra_defs) ->
      Hook.call ~fix_exn ~hook uctx extra_defs local gr
  end;
  gr

let declare_fix ?(opaque = false) ?hook_data (_,poly,_ as kind) pl univs f ((def,_),eff) t imps =
  let ce = definition_entry ~opaque ~types:t ~univs ~eff def in
  declare_definition f kind ?hook_data ce pl imps

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
