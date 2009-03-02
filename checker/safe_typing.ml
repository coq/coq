(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: safe_typing.ml 10275 2007-10-30 11:01:24Z barras $ *)

open Pp
open Util
open Names
open Declarations
open Environ
open Mod_checking

(************************************************************************)
(*
 * Global environment
 *)

let genv = ref empty_env
let reset () = genv := empty_env
let get_env () = !genv

let set_engagement c =
  genv := set_engagement c !genv

(* full_add_module adds module with universes and constraints *)
let full_add_module dp mb digest =
  let env = !genv in
  let mp = MPfile dp in
  let env = add_constraints mb.mod_constraints env in
  let env = Modops.add_module mp mb env in
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
    str "compiled library " ++ str(string_of_dirpath caller) ++
    spc() ++ str "makes inconsistent assumptions over library" ++ spc() ++
    str(string_of_dirpath dir) ++ fnl() in
  f msg


let check_imports f caller env needed =
  let check (dp,stamp) =
    try
      let actual_stamp = lookup_digest env dp in
      if stamp <> actual_stamp then report_clash f caller dp
    with Not_found -> 
      error ("Reference to unknown module " ^ (string_of_dirpath dp))
  in
  List.iter check needed



(* Remove the body of opaque constants in modules *)
(* also remove mod_expr ? *)
let rec lighten_module mb =
  { mb with
    mod_expr = Option.map lighten_modexpr mb.mod_expr;
    mod_type = Option.map lighten_modexpr mb.mod_type }

and lighten_struct struc = 
  let lighten_body (l,body) = (l,match body with
    | SFBconst ({const_opaque=true} as x) -> SFBconst {x with const_body=None}
    | (SFBconst _ | SFBmind _ | SFBalias _) as x -> x
    | SFBmodule m -> SFBmodule (lighten_module m)
    | SFBmodtype m -> SFBmodtype 
	({m with 
	    typ_expr = lighten_modexpr m.typ_expr}))
  in
    List.map lighten_body struc

and lighten_modexpr = function
  | SEBfunctor (mbid,mty,mexpr) ->
      SEBfunctor (mbid, 
		    ({mty with 
			typ_expr = lighten_modexpr mty.typ_expr}),
		  lighten_modexpr mexpr)
  | SEBident mp as x -> x
  | SEBstruct (msid, struc) ->
      SEBstruct (msid, lighten_struct struc)
  | SEBapply (mexpr,marg,u) ->
      SEBapply (lighten_modexpr mexpr,lighten_modexpr marg,u)
  | SEBwith (seb,wdcl) ->
      SEBwith (lighten_modexpr seb,wdcl) 
 
let lighten_library (dp,mb,depends,s) = (dp,lighten_module mb,depends,s)


type compiled_library = 
    dir_path *
    module_body *
    (dir_path * Digest.t) list *
    engagement option
 
open Validate
let val_deps = val_list (val_tuple"dep"[|val_dp;no_val|])
let val_vo = val_tuple "vo" [|val_dp;val_module;val_deps;val_opt val_eng|]

(* This function should append a certificate to the .vo file.
   The digest must be part of the certicate to rule out attackers
   that could change the .vo file between the time it was read and
   the time the stamp is written.
   For the moment, .vo are not signed. *)
let stamp_library file digest = ()

(* When the module is checked, digests do not need to match, but a
   warning is issued in case of mismatch *)
let import file (dp,mb,depends,engmt as vo) digest = 
  Validate.apply !Flags.debug val_vo vo;
  Flags.if_verbose msgnl (str "*** vo structure validated ***");
  let env = !genv in
  check_imports msg_warning dp env depends;
  check_engagement env engmt;
  check_module (add_constraints mb.mod_constraints env) mb;
  stamp_library file digest;
  (* We drop proofs once checked *)
(*  let mb = lighten_module mb in*)
  full_add_module dp mb digest

(* When the module is admitted, digests *must* match *)
let unsafe_import file (dp,mb,depends,engmt) digest = 
  let env = !genv in
  check_imports (errorlabstrm"unsafe_import") dp env depends;
  check_engagement env engmt;
  (* We drop proofs once checked *)
(*  let mb = lighten_module mb in*)
  full_add_module dp mb digest
