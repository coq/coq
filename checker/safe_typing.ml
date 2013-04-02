(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Declarations
open Environ

(************************************************************************)
(*
 * Global environment
 *)

let genv = ref empty_env
let get_env () = !genv

let set_engagement c =
  genv := set_engagement c !genv

(* full_add_module adds module with universes and constraints *)
let full_add_module dp mb digest =
  let env = !genv in
  let env = add_constraints mb.mod_constraints env in
  let env = Modops.add_module mb env in
  genv := add_digest env dp digest

(* Check that the engagement expected by a library matches the initial one *)
let check_engagement env c =
  match engagement env, c with
    | Some ImpredicativeSet, Some ImpredicativeSet -> ()
    | _, None -> ()
    | _, Some ImpredicativeSet ->
        error "Needs option -impredicative-set"

(* Libraries = Compiled modules *)

let report_clash f caller dir =
  let msg =
    str "compiled library " ++ str(DirPath.to_string caller) ++
    spc() ++ str "makes inconsistent assumptions over library" ++ spc() ++
    str(DirPath.to_string dir) ++ fnl() in
  f msg


let check_imports f caller env needed =
  let check (dp,stamp) =
    try
      let actual_stamp = lookup_digest env dp in
      if stamp <> actual_stamp then report_clash f caller dp
    with Not_found ->
      error ("Reference to unknown module " ^ (DirPath.to_string dp))
  in
  Array.iter check needed

type nativecode_symb_array

type compiled_library =
    DirPath.t *
    module_body *
    (DirPath.t * Digest.t) array *
    engagement option *
    nativecode_symb_array

open Validate
let val_deps = val_array (val_tuple ~name:"dep"[|val_dp;no_val|])
let val_vo = val_tuple ~name:"vo"
  [|val_dp;val_module;val_deps;val_opt val_eng; no_val|]

(* This function should append a certificate to the .vo file.
   The digest must be part of the certicate to rule out attackers
   that could change the .vo file between the time it was read and
   the time the stamp is written.
   For the moment, .vo are not signed. *)
let stamp_library file digest = ()

(* When the module is checked, digests do not need to match, but a
   warning is issued in case of mismatch *)
let import file (dp,mb,depends,engmt,_ as vo) table digest =
  Validate.apply !Flags.debug val_vo vo;
  Validate.apply !Flags.debug (val_array Term.val_constr) table;
  Flags.if_verbose ppnl (str "*** vo structure validated ***"); pp_flush ();
  let env = !genv in
  check_imports msg_warning dp env depends;
  check_engagement env engmt;
  Mod_checking.check_module (add_constraints mb.mod_constraints env) mb.mod_mp mb;
  stamp_library file digest;
  (* We drop proofs once checked *)
(*  let mb = lighten_module mb in*)
  full_add_module dp mb digest

(* When the module is admitted, digests *must* match *)
let unsafe_import file (dp,mb,depends,engmt,_ as vo) digest =
  if !Flags.debug then ignore vo; (*Validate.apply !Flags.debug val_vo vo;*)
  let env = !genv in
  check_imports (errorlabstrm"unsafe_import") dp env depends;
  check_engagement env engmt;
  (* We drop proofs once checked *)
(*  let mb = lighten_module mb in*)
  full_add_module dp mb digest
