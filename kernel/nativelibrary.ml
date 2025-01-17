(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Declarations
open Mod_declarations
open Mod_subst
open Modops
open Nativecode

(** This file implements separate compilation for libraries in the native
compiler *)

let rec translate_mod mp env mod_expr acc =
  match mod_expr with
  | NoFunctor struc ->
      let env' = add_structure mp struc (empty_delta_resolver mp) env in
      List.fold_left (translate_field mp env') acc struc
  | MoreFunctor _ -> acc

and translate_field mp env acc (l,x) =
  match x with
  | SFBconst cb ->
     let con = Constant.make2 mp l in
     (debug_native_compiler (fun () ->
        let msg = Printf.sprintf "Compiling constant %s..." (Constant.to_string con) in
        Pp.str msg));
     compile_constant_field env con acc cb
  | SFBmind mb ->
     (debug_native_compiler (fun () ->
        let id = mb.mind_packets.(0).mind_typename in
        let msg = Printf.sprintf "Compiling inductive %s..." (Id.to_string id) in
        Pp.str msg));
     compile_mind_field mp l acc mb
  | SFBrules rrb ->
     (debug_native_compiler (fun () ->
        let msg = Printf.sprintf "Not Compiling rules %s..." (Label.to_string l) in
        Pp.str msg));
     compile_rewrite_rules env l acc rrb
  | SFBmodule md ->
     let mp = MPdot (mp, l) in
     (debug_native_compiler (fun () ->
        let msg =
          Printf.sprintf "Compiling module %s..." (ModPath.to_string mp)
        in
        Pp.str msg));
     translate_mod mp env (mod_type md) acc
  | SFBmodtype mdtyp ->
     let mp = MPdot (mp, l) in
     (debug_native_compiler (fun () ->
        let msg =
          Printf.sprintf "Compiling module type %s..." (ModPath.to_string mp)
        in
        Pp.str msg));
     translate_mod mp env (mod_type mdtyp) acc

let dump_library mp env mod_expr =
  debug_native_compiler (fun () -> Pp.str "Compiling library...");
  match mod_expr with
  | NoFunctor struc ->
      let env = add_structure mp struc (empty_delta_resolver mp) env in
      let t0 = Sys.time () in
      clear_global_tbl ();
      clear_symbols ();
      let mlcode =
        List.fold_left (translate_field mp env) [] struc
      in
      let t1 = Sys.time () in
      let time_info = Format.sprintf "Time spent generating this code: %.5fs" (t1-.t0) in
      let mlcode = add_header_comment (List.rev mlcode) time_info in
      mlcode, get_symbols ()
  | _ -> assert false
