(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


(* Poor's man DECLARE PLUGIN *)
let __coq_plugin_name = "int63_syntax_plugin"
let () = Mltop.add_known_module __coq_plugin_name

(* digit-based syntax for int63 *)

open Names
open Libnames

(*** Constants for locating int63 constructors ***)

let q_int63 = qualid_of_string "Coq.Numbers.Cyclic.Int63.Int63.int"
let q_id_int63 = qualid_of_string "Coq.Numbers.Cyclic.Int63.Int63.id_int"

let make_dir l = DirPath.make (List.rev_map Id.of_string l)
let make_path dir id = Libnames.make_path (make_dir dir) (Id.of_string id)

(* int63 stuff *)
let int63_module = ["Coq"; "Numbers"; "Cyclic"; "Int63"; "Int63"]
let int63_path = make_path int63_module "int"
let int63_scope = "int63_scope"

let at_declare_ml_module f x =
  Mltop.declare_cache_obj (fun () -> f x) __coq_plugin_name

(* Actually declares the interpreter for int63 *)

let _ =
  let open Notation in
  at_declare_ml_module
    (fun () ->
       let id_int63 = Nametab.locate q_id_int63 in
       let o = { to_kind = Int63, Direct;
                 to_ty = id_int63;
                 of_kind = Int63, Direct;
                 of_ty = id_int63;
                 ty_name = q_int63;
                 warning = Nop } in
       enable_prim_token_interpretation
         { pt_local = false;
           pt_scope = int63_scope;
           pt_interp_info = NumeralNotation o;
           pt_required = (int63_path, int63_module);
           pt_refs = [];
           pt_in_match = false })
    ()
