(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Decl_kinds
open Declare
open Entries
open Globnames
open Impargs

let warn_definition_not_visible =
  CWarnings.create ~name:"definition-not-visible" ~category:"implicits"
    Pp.(fun ident ->
        strbrk "Section definition " ++
        Names.Id.print ident ++ strbrk " is not visible from current goals")

let warn_local_declaration =
  CWarnings.create ~name:"local-declaration" ~category:"scope"
    Pp.(fun (id,kind) ->
        Names.Id.print id ++ strbrk " is declared as a local " ++ str kind)

let get_locality id ~kind = function
| Discharge ->
  (** If a Let is defined outside a section, then we consider it as a local definition *)
   warn_local_declaration (id,kind);
  true
| Local -> true
| Global -> false

let declare_global_definition ident ce local k pl imps =
  let local = get_locality ident ~kind:"definition" local in
  let kn = declare_constant ident ~local (DefinitionEntry ce, IsDefinition k) in
  let gr = ConstRef kn in
  let () = maybe_declare_manual_implicits false gr imps in
  let () = Universes.register_universe_binders gr pl in
  let () = definition_message ident in
  gr

let declare_definition ident (local, p, k) ce pl imps hook =
  let fix_exn = Future.fix_exn_of ce.const_entry_body in
  let r = match local with
  | Discharge when Lib.sections_are_opened () ->
    let c = SectionLocalDef ce in
    let _ = declare_variable ident (Lib.cwd(), c, IsDefinition k) in
    let () = definition_message ident in
    let gr = VarRef ident in
    let () = maybe_declare_manual_implicits false gr imps in
    let () = if Proof_global.there_are_pending_proofs () then
	       warn_definition_not_visible ident
    in
    gr
  | Discharge | Local | Global ->
    declare_global_definition ident ce local k pl imps in
  Lemmas.call_hook fix_exn hook local r

let declare_fix ?(opaque = false) (_,poly,_ as kind) pl ctx f ((def,_),eff) t imps =
  let ce = definition_entry ~opaque ~types:t ~poly ~univs:ctx ~eff def in
  declare_definition f kind ce pl imps (Lemmas.mk_hook (fun _ r -> r))

