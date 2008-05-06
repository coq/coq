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

(*
let type_modpath env mp = 
  strengthen env (lookup_module mp env).mod_type mp

let rec check_spec_body env mp lab = function
  | SPBconst cb ->
      let kn = mp, empty_dirpath, lab in
      check_constant_declaration env kn cb
  | SPBmind mib ->
      let kn = mp, empty_dirpath, lab in
      Indtypes.check_inductive env kn mib
  | SPBmodule msb ->
      check_mod_spec env msb;
      Modops.add_module (MPdot(mp,lab)) (module_body_of_type msb.msb_modtype)
        (add_modtype_constraints env msb.msb_modtype)
  | SPBmodtype mty ->
      let kn = mp, empty_dirpath, lab in
      check_modtype env mty;
      add_modtype kn mty (add_modtype_constraints env mty)

and check_mod_spec env msb =
  let env' = add_constraints msb.msb_constraints env in
  check_modtype env' msb.msb_modtype;

(*  Subtyping.check_equal env' msb.msb_modtype (MTBident *)
  (* TODO: check equiv *)
  env'

(* !!!: modtype needs mp (the name it will be given) because
   submodule should be added without reference to self *)
and check_modtype env = function
  | MTBident kn ->
      (try let _ = lookup_modtype kn env in ()
      with Not_found -> failwith ("unbound module type "(*^string_of_kn kn*)))
  | MTBfunsig (mbid,marg,mbody) ->
      check_modtype env marg;
      let env' = 
	add_module (MPbound mbid) (module_body_of_type marg)
          (add_modtype_constraints env marg) in
      check_modtype env' mbody
  | MTBsig (msid,sign) ->
      let _ =
        List.fold_left (fun env (lab,mb) ->
          check_spec_body env (MPself msid) lab mb) env sign in
      ()


let elem_spec_of_body (lab,e) =
  lab,
  match e with
      SEBconst cb -> SPBconst cb
    | SEBmind mind -> SPBmind mind
    | SEBmodule msb -> SPBmodule (module_spec_of_body msb)
    | SEBmodtype mtb -> SPBmodtype mtb

let rec check_module env mb =
  let env' = add_module_constraints env mb in
  (* mod_type *)
  check_modtype env' mb.mod_type;
  (* mod_expr *)
  let msig =
    match mb.mod_expr with
        Some mex ->
          let msig = infer_mod_expr env' mex in
          Subtyping.check_subtypes env' msig mb.mod_type;
          msig
      | None -> mb.mod_type in
  (* mod_user_type *)
  (match mb.mod_user_type with
      Some usig -> Subtyping.check_subtypes env' msig usig
    | None -> ());
  (* mod_equiv *)
  (match mb.mod_equiv with
      Some mid ->
        if mb.mod_expr <> Some(MEBident mid) then
          failwith "incorrect module alias"
    | None -> ());

and infer_mod_expr env = function
    MEBident mp -> type_modpath env mp
  | MEBstruct(msid,msb) ->
      let mp = MPself msid in
      let _ =
        List.fold_left (fun env (lab,mb) ->
          struct_elem_body env mp lab mb) env msb in
      MTBsig(msid,List.map elem_spec_of_body msb)
  | MEBfunctor (arg_id, arg, body) ->
      check_modtype env arg;
      let env' = add_module (MPbound arg_id) (module_body_of_type arg) env in
      let body_ty = infer_mod_expr env' body in
      MTBfunsig (arg_id, arg, body_ty)
  | MEBapply (fexpr,MEBident mp,_) ->
      let ftb = infer_mod_expr env fexpr in
      let ftb = scrape_modtype env ftb in
      let farg_id, farg_b, fbody_b = destr_functor ftb in
      let mtb = type_modpath env mp in
      Subtyping.check_subtypes env mtb farg_b;
      subst_modtype (map_mbid farg_id mp) fbody_b
  | MEBapply _ ->
      failwith "functor argument must be a module variable"

and struct_elem_body env mp lab = function
  | SEBconst cb ->
      let kn = mp, empty_dirpath, lab in
      check_constant_declaration env kn cb
  | SEBmind mib ->
      let kn = mp, empty_dirpath, lab in
      Indtypes.check_inductive env kn mib
  | SEBmodule msb ->
      check_module env msb;
(*msgnl(str"MODULE OK: "++prkn(make_kn mp empty_dirpath lab)++fnl());*)
      Modops.add_module (MPdot(mp,lab)) msb 
        (add_module_constraints env msb)
  | SEBmodtype mty ->
      check_modtype env mty;
      add_modtype (mp, empty_dirpath, lab) mty
        (add_modtype_constraints env mty)
*)

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
  let env = add_module_constraints env mb in
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
 
(* This function should append a certificate to the .vo file.
   The digest must be part of the certicate to rule out attackers
   that could change the .vo file between the time it was read and
   the time the stamp is written.
   For the moment, .vo are not signed. *)
let stamp_library file digest = ()

(* When the module is checked, digests do not need to match, but a
   warning is issued in case of mismatch *)
let import file (dp,mb,depends,engmt as vo) digest = 
  Validate.val_vo (Obj.repr vo);
  Flags.if_verbose msgnl (str "*** vo structure validated ***");
  let env = !genv in
  check_imports msg_warning dp env depends;
  check_engagement env engmt;
  check_module env mb;
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
