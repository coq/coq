(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
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


type compiled_library =
    dir_path *
    module_body *
    (dir_path * Digest.t) list *
    engagement option

 (* Store the body of modules' opaque constants inside a table.  

    This module is used during the serialization and deserialization
    of vo files. 

    By adding an indirection to the opaque constant definitions, we
    gain the ability not to load them. As these constant definitions
    are usually big terms, we save a deserialization time as well as
    some memory space. *)
module LightenLibrary : sig
  type table 
  type lightened_compiled_library 
  val load : load_proof:bool -> (unit -> table) 
    -> lightened_compiled_library -> compiled_library
end = struct

  (* The table is implemented as an array of [constr_substituted].
     Thus, its keys are integers which can be easily embedded inside
     [constr_substituted]. This way the [compiled_library] type does
     not have to be changed. *)
  type table = constr_substituted array

  (* To avoid any future misuse of the lightened library that could 
     interpret encoded keys as real [constr_substituted], we hide 
     these kind of values behind an abstract datatype. *)
  type lightened_compiled_library = compiled_library

  (* Map a [compiled_library] to another one by just updating 
     the opaque term [t] to [on_opaque_const_body t]. *)
  let traverse_library on_opaque_const_body =
    let rec traverse_module mb =
      match mb.mod_expr with 
	  None -> 
	    { mb with
		mod_expr = None;
		mod_type = traverse_modexpr mb.mod_type;
	    }
	| Some impl when impl == mb.mod_type-> 
	    let mtb =  traverse_modexpr mb.mod_type in 
	      { mb with
		  mod_expr = Some mtb;
		  mod_type = mtb;
	      }    
	| Some impl -> 
	    { mb with
		mod_expr = Option.map traverse_modexpr mb.mod_expr;
		mod_type = traverse_modexpr mb.mod_type;
	    }    
    and traverse_struct struc =
      let traverse_body (l,body) = (l,match body with
	| SFBconst ({const_opaque=true} as x) -> 
	  SFBconst {x with const_body = on_opaque_const_body x.const_body }
	| (SFBconst _ | SFBmind _ ) as x -> 
	  x
	| SFBmodule m -> 
	  SFBmodule (traverse_module m)
	| SFBmodtype m -> 
	  SFBmodtype ({m with typ_expr = traverse_modexpr m.typ_expr}))
      in
      List.map traverse_body struc
	
    and traverse_modexpr = function
      | SEBfunctor (mbid,mty,mexpr) ->
	SEBfunctor (mbid,
		    ({mty with
		      typ_expr = traverse_modexpr mty.typ_expr}),
		    traverse_modexpr mexpr)
      | SEBident mp as x -> x
      | SEBstruct (struc) ->
	SEBstruct  (traverse_struct struc)
      | SEBapply (mexpr,marg,u) ->
	SEBapply (traverse_modexpr mexpr,traverse_modexpr marg,u)
      | SEBwith (seb,wdcl) ->
	SEBwith (traverse_modexpr seb,wdcl)
    in
    fun (dp,mb,depends,s) -> (dp,traverse_module mb,depends,s) 

  (* Loading is also a traversing that decodes the embedded keys that
     are inside the [lightened_library]. If the [load_proof] flag is
     set, we lookup inside the table to graft the
     [constr_substituted]. Otherwise, we set the [const_body] field
     to [None]. 
  *)
  let load ~load_proof (get_table : unit -> table) lightened_library = 
    let decode_key : constr_substituted option -> constr_substituted option = 
      if load_proof then 
	let table = get_table () in
	function Some cterm -> 
	  Some (table.(
	    try 
	      match Declarations.force_constr cterm with
		| Term.Rel key -> key
		| _ -> assert false
	    with _ -> assert false
	  ))
	  | _ -> None
      else 
	fun _ -> None
    in
    traverse_library decode_key lightened_library

end

open Validate
let val_deps = val_list (val_tuple ~name:"dep"[|val_dp;no_val|])
let val_vo = val_tuple ~name:"vo" [|val_dp;val_module;val_deps;val_opt val_eng|]

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
  Mod_checking.check_module (add_constraints mb.mod_constraints env) mb.mod_mp mb;
  stamp_library file digest;
  (* We drop proofs once checked *)
(*  let mb = lighten_module mb in*)
  full_add_module dp mb digest

(* When the module is admitted, digests *must* match *)
let unsafe_import file (dp,mb,depends,engmt as vo) digest =
  if !Flags.debug then ignore vo; (*Validate.apply !Flags.debug val_vo vo;*)
  let env = !genv in
  check_imports (errorlabstrm"unsafe_import") dp env depends;
  check_engagement env engmt;
  (* We drop proofs once checked *)
(*  let mb = lighten_module mb in*)
  full_add_module dp mb digest
