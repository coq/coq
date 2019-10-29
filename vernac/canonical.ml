(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Names
open Libobject
open Recordops

let open_canonical_structure i (_, o) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  if Int.equal i 1 then register_canonical_structure env sigma ~warn:false o

let cache_canonical_structure (_, o) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  register_canonical_structure ~warn:true env sigma o

let discharge_canonical_structure (_,x) = Some x

let inCanonStruc : Constant.t * inductive -> obj =
  declare_object {(default_object "CANONICAL-STRUCTURE") with
                  open_function = open_canonical_structure;
                  cache_function = cache_canonical_structure;
                  subst_function = (fun (subst,c) -> subst_canonical_structure subst c);
                  classify_function = (fun x -> Substitute x);
                  discharge_function = discharge_canonical_structure }

let add_canonical_structure x = Lib.add_anonymous_leaf (inCanonStruc x)

let declare_definition ~poly ~scope seed ind env sigma body =
  let name = Namegen.next_global_ident_away seed (Termops.vars_of_env env) in
  let sigma, ce =
    DeclareDef.prepare_definition
      ~allow_evars:false ~opaque:false ~poly ~types:None ~body sigma UState.default_univ_decl in
  let scope = DeclareDef.(Global Declare.ImportNeedQualified) in
  let kind = Decls.IsDefinition Decls.Definition in
  let ub = Evd.universe_binders sigma in
  match DeclareDef.declare_definition ~name ~scope ~kind ub ce [] with
  | GlobRef.ConstRef c -> c
  | _ -> assert false

let declare_canonical_structure ~poly ~scope ref =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  match check_and_decompose_canonical_structure env sigma ref with
  | SingleNamedCanonicalInstance (c,i) ->
      add_canonical_structure (c,i)
  | MultipleAnonymousCanonicalInstances (label,sigma,cslist) ->
      cslist |> List.iter (fun (body,ind) ->
        let name = declare_definition ~poly ~scope label ind env sigma body in
        add_canonical_structure (name,ind))
