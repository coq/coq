(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Declarations
open Mod_subst
open Modops
open Nativecode

(** This file implements separate compilation for libraries in the native
compiler *)

let rec translate_mod prefix mp env mod_expr acc =
  match mod_expr with
  | NoFunctor struc ->
      let env' = add_structure mp struc empty_delta_resolver env in
      List.fold_left (translate_field prefix mp env') acc struc
  | MoreFunctor _ -> acc

and translate_field prefix mp env acc (l,x) =
  match x with
  | SFBconst cb ->
     let con = Constant.make3 mp DirPath.empty l in
     (if !Flags.debug then
        let msg = Printf.sprintf "Compiling constant %s..." (Constant.to_string con) in
	Feedback.msg_debug (Pp.str msg));
     compile_constant_field env prefix con acc cb
  | SFBmind mb ->
     (if !Flags.debug then
	let id = mb.mind_packets.(0).mind_typename in
	let msg = Printf.sprintf "Compiling inductive %s..." (Id.to_string id) in
	Feedback.msg_debug (Pp.str msg));
     compile_mind_field mp l acc mb
  | SFBmodule md ->
     let mp = md.mod_mp in
     (if !Flags.debug then
	let msg =
	  Printf.sprintf "Compiling module %s..." (ModPath.to_string mp)
	in
	Feedback.msg_debug (Pp.str msg));
     translate_mod prefix mp env md.mod_type acc
  | SFBmodtype mdtyp ->
     let mp = mdtyp.mod_mp in
     (if !Flags.debug then
	let msg =
	  Printf.sprintf "Compiling module type %s..." (ModPath.to_string mp)
	in
	Feedback.msg_debug (Pp.str msg));
     translate_mod prefix mp env mdtyp.mod_type acc

let dump_library mp dp env mod_expr =
  if !Flags.debug then Feedback.msg_debug (Pp.str "Compiling library...");
  match mod_expr with
  | NoFunctor struc ->
      let env = add_structure mp struc empty_delta_resolver env in
      let prefix = mod_uid_of_dirpath dp ^ "." in
      let t0 = Sys.time () in
      clear_global_tbl ();
      clear_symbols ();
      let mlcode =
        List.fold_left (translate_field prefix mp env) [] struc
      in
      let t1 = Sys.time () in
      let time_info = Format.sprintf "Time spent generating this code: %.5fs" (t1-.t0) in
      let mlcode = add_header_comment (List.rev mlcode) time_info in
      mlcode, get_symbols ()
  | _ -> assert false
