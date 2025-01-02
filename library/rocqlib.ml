(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names

let make_dir l = DirPath.make (List.rev_map Id.of_string l)

(************************************************************************)
(* Rocq reference API                                                   *)
(************************************************************************)
let rocq = Libnames.rocq_init_string (* "Corelib" *)

let init_dir = [ rocq; "Init"]

let jmeq_module_name = ["Stdlib";"Logic";"JMeq"]

let table : GlobRef.t CString.Map.t ref =
  Summary.ref ~name:"rocqlib_registered" CString.Map.empty

let get_lib_refs () =
  CString.Map.bindings !table

let has_ref s = CString.Map.mem s !table

let check_ref s gr =
  match CString.Map.find s !table with
  | r -> GlobRef.UserOrd.equal r gr
  | exception Not_found -> false

let check_ind_ref s ind = check_ref s (GlobRef.IndRef ind)

exception NotFoundRef of string

let () = CErrors.register_handler (function
    | NotFoundRef s -> Some Pp.(str "not found in table: " ++ str s)
    | _ -> None)

let lib_ref s =
  try CString.Map.find s !table
  with Not_found -> raise (NotFoundRef s)

let lib_ref_opt s = CString.Map.find_opt s !table

let add_ref s c =
  table := CString.Map.add s c !table

let cache_ref (s,c) =
  add_ref s c

let (inRocqlibRef : Libobject.locality * (string * GlobRef.t) -> Libobject.obj) =
  let open Libobject in
  declare_object @@ object_with_locality "COQLIBREF"
    ~cache:cache_ref
    ~subst:(Some ident_subst_function)
    ~discharge:(fun x -> x)

(** Replaces a binding ! *)
let register_ref local s c =
  Lib.add_leaf @@ inRocqlibRef (local,(s,c))

(************************************************************************)
(* Generic functions to find Rocq objects *)

(* For tactics/commands requiring vernacular libraries *)

let check_required_library d =
  let dir = make_dir d in
  try
    let _ : Mod_declarations.module_body = Global.lookup_module (ModPath.MPfile dir) in
    ()
  with Not_found ->
    let in_current_dir = match Lib.current_mp () with
      | MPfile dp -> DirPath.equal dir dp
      | _ -> false
    in
    if not in_current_dir then
      CErrors.user_err Pp.(str "Library " ++ DirPath.print dir
        ++ str " has to be required first.")

(************************************************************************)
(* Specific Rocq objects                                                *)
(************************************************************************)

let logic_module_name = init_dir@["Logic"]

let datatypes_module_name = init_dir@["Datatypes"]

(** Identity *)

(* Sigma data *)
type rocq_sigma_data = {
  proj1 : GlobRef.t;
  proj2 : GlobRef.t;
  elim  : GlobRef.t;
  intro : GlobRef.t;
  typ   : GlobRef.t }

let build_sigma_gen str =
  { typ   = lib_ref ("core." ^ str ^ ".type");
    elim  = lib_ref ("core." ^ str ^ ".rect");
    intro = lib_ref ("core." ^ str ^ ".intro");
    proj1 = lib_ref ("core." ^ str ^ ".proj1");
    proj2 = lib_ref ("core." ^ str ^ ".proj2");
  }

let build_prod       () = build_sigma_gen "prod"
let build_sigma      () = build_sigma_gen "sig"
let build_sigma_type () = build_sigma_gen "sigT"

(* Equalities *)
type rocq_eq_data = {
  eq   : GlobRef.t;
  ind  : GlobRef.t;
  refl : GlobRef.t;
  sym  : GlobRef.t;
  trans: GlobRef.t;
  congr: GlobRef.t }

(* Leibniz equality on Type *)

let build_eqdata_gen str = {
  eq    = lib_ref ("core." ^ str ^ ".type");
  ind   = lib_ref ("core." ^ str ^ ".ind");
  refl  = lib_ref ("core." ^ str ^ ".refl");
  sym   = lib_ref ("core." ^ str ^ ".sym");
  trans = lib_ref ("core." ^ str ^ ".trans");
  congr = lib_ref ("core." ^ str ^ ".congr");
  }

let build_rocq_eq_data       () = build_eqdata_gen "eq"
let build_rocq_jmeq_data     () = build_eqdata_gen "JMeq"
let build_rocq_identity_data () = build_eqdata_gen "identity"
