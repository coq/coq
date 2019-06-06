(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Pp
open Names
open Libnames
open Globnames

let make_dir l = DirPath.make (List.rev_map Id.of_string l)

(************************************************************************)
(* Coq reference API                                                    *)
(************************************************************************)
let coq = Libnames.coq_string (* "Coq" *)

let init_dir = [ coq; "Init"]

let jmeq_module_name       = [coq;"Logic";"JMeq"]
let jmeq_library_path = make_dir jmeq_module_name
let jmeq_module = MPfile jmeq_library_path

let find_reference locstr dir s =
  let dp = make_dir dir in
  let sp = Libnames.make_path dp (Id.of_string s) in
  Nametab.global_of_path sp

let coq_reference locstr dir s = find_reference locstr (coq::dir) s

let table : GlobRef.t CString.Map.t ref =
  let name = "coqlib_registered" in
  Summary.ref ~name CString.Map.empty

let get_lib_refs () =
  CString.Map.bindings !table

let has_ref s = CString.Map.mem s !table

let check_ind_ref s ind =
  match CString.Map.find s !table with
  | IndRef r -> eq_ind r ind
  | _ -> false
  | exception Not_found -> false

let lib_ref s =
  try CString.Map.find s !table
  with Not_found ->
    user_err Pp.(str "not found in table: " ++ str s)

let add_ref s c =
  table := CString.Map.add s c !table

let cache_ref (_,(s,c)) =
  add_ref s c

let (inCoqlibRef : string * GlobRef.t -> Libobject.obj) =
  let open Libobject in
  declare_object { (default_object "COQLIBREF") with
    cache_function = cache_ref;
    load_function = (fun _ x -> cache_ref x);
    classify_function = (fun o -> Substitute o);
    subst_function = ident_subst_function;
    discharge_function = fun (_, sc) -> Some sc }

(** Replaces a binding ! *)
let register_ref s c =
  Lib.add_anonymous_leaf @@ inCoqlibRef (s,c)

(************************************************************************)
(* Generic functions to find Coq objects *)

let has_suffix_in_dirs dirs ref =
  let dir = dirpath (Nametab.path_of_global ref) in
  List.exists (fun d -> is_dirpath_prefix_of d dir) dirs

let gen_reference_in_modules locstr dirs s =
  let dirs = List.map make_dir dirs in
  let qualid = qualid_of_string s in
  let all = Nametab.locate_all qualid in
  let all = List.sort_uniquize GlobRef.Ordered_env.compare all in
  let these = List.filter (has_suffix_in_dirs dirs) all in
  match these with
    | [x] -> x
    | [] ->
	anomaly ~label:locstr (str "cannot find " ++ str s ++
	str " in module" ++ str (if List.length dirs > 1 then "s " else " ") ++
        prlist_with_sep pr_comma DirPath.print dirs ++ str ".")
    | l ->
      anomaly ~label:locstr
	(str "ambiguous name " ++ str s ++ str " can represent " ++
	   prlist_with_sep pr_comma
	   (fun x -> Libnames.pr_path (Nametab.path_of_global x)) l ++
	   str " in module" ++ str (if List.length dirs > 1 then "s " else " ") ++
           prlist_with_sep pr_comma DirPath.print dirs ++ str ".")

(* For tactics/commands requiring vernacular libraries *)

let check_required_library d =
  let dir = make_dir d in
  if Library.library_is_loaded dir then ()
  else
    let in_current_dir = match Lib.current_mp () with
      | MPfile dp -> DirPath.equal dir dp
      | _ -> false
    in
    if not in_current_dir then
      user_err ~hdr:"Coqlib.check_required_library"
        (str "Library " ++ DirPath.print dir ++ str " has to be required first.")

(************************************************************************)
(* Specific Coq objects                                                 *)
(************************************************************************)

let arith_dir = [coq;"Arith"]
let arith_modules = [arith_dir]

let numbers_dir = [coq;"Numbers"]
let parith_dir = [coq;"PArith"]
let narith_dir = [coq;"NArith"]
let zarith_dir = [coq;"ZArith"]

let zarith_base_modules = [numbers_dir;parith_dir;narith_dir;zarith_dir]

let init_modules = [
  init_dir@["Datatypes"];
  init_dir@["Logic"];
  init_dir@["Specif"];
  init_dir@["Logic_Type"];
  init_dir@["Nat"];
  init_dir@["Peano"];
  init_dir@["Wf"]
]

let logic_module_name = init_dir@["Logic"]
let logic_module = MPfile (make_dir logic_module_name)

let logic_type_module_name = init_dir@["Logic_Type"]
let logic_type_module = make_dir logic_type_module_name

let datatypes_module_name = init_dir@["Datatypes"]
let datatypes_module = MPfile (make_dir datatypes_module_name)

(** Identity *)

let id = Constant.make2 datatypes_module @@ Label.make "idProp"
let type_of_id = Constant.make2 datatypes_module @@ Label.make "IDProp"

(** Natural numbers *)
let nat_kn = MutInd.make2 datatypes_module @@ Label.make "nat"
let nat_path = Libnames.make_path (make_dir datatypes_module_name) (Id.of_string "nat")

let glob_nat = IndRef (nat_kn,0)

let path_of_O = ((nat_kn,0),1)
let path_of_S = ((nat_kn,0),2)
let glob_O = ConstructRef path_of_O
let glob_S = ConstructRef path_of_S

(** Booleans *)
let bool_kn = MutInd.make2 datatypes_module @@ Label.make "bool"

let glob_bool = IndRef (bool_kn,0)

let path_of_true = ((bool_kn,0),1)
let path_of_false = ((bool_kn,0),2)
let glob_true  = ConstructRef path_of_true
let glob_false  = ConstructRef path_of_false

(** Equality *)
let eq_kn = MutInd.make2 logic_module @@ Label.make "eq"
let glob_eq = IndRef (eq_kn,0)

let identity_kn = MutInd.make2 datatypes_module @@ Label.make "identity"
let glob_identity = IndRef (identity_kn,0)

let jmeq_kn = MutInd.make2 jmeq_module @@ Label.make "JMeq"
let glob_jmeq = IndRef (jmeq_kn,0)

(* Sigma data *)
type coq_sigma_data = {
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

(* Booleans *)

type coq_bool_data  = {
  andb : GlobRef.t;
  andb_prop : GlobRef.t;
  andb_true_intro : GlobRef.t}

let build_bool_type () =
  { andb = lib_ref "core.bool.andb";
    andb_prop = lib_ref "core.bool.andb_prop";
    andb_true_intro = lib_ref "core.bool.andb_true_intro"; }

(* Equalities *)
type coq_eq_data = {
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

let build_coq_eq_data       () = build_eqdata_gen "eq"
let build_coq_jmeq_data     () = build_eqdata_gen "JMeq"
let build_coq_identity_data () = build_eqdata_gen "identity"

(* Inversion data... *)

(* Data needed for discriminate and injection *)
type coq_inversion_data = {
  inv_eq   : GlobRef.t; (* : forall params, t -> Prop *)
  inv_ind  : GlobRef.t; (* : forall params P y, eq params y -> P y *)
  inv_congr: GlobRef.t  (* : forall params B (f:t->B) y, eq params y -> f c=f y *)
}

let build_coq_inversion_gen l str =
  List.iter check_required_library l; {
    inv_eq    = lib_ref ("core." ^ str ^ ".type");
    inv_ind   = lib_ref ("core." ^ str ^ ".ind");
    inv_congr = lib_ref ("core." ^ str ^ ".congr_canonical");
  }

let build_coq_inversion_eq_data () =
  build_coq_inversion_gen [logic_module_name] "eq"

let build_coq_inversion_eq_true_data () =
  build_coq_inversion_gen [logic_module_name] "True"

let build_coq_inversion_identity_data () =
  build_coq_inversion_gen [logic_module_name] "identity"

(* This needs a special case *)
let build_coq_inversion_jmeq_data () = {
  inv_eq    = lib_ref "core.JMeq.hom";
  inv_ind   = lib_ref "core.JMeq.ind";
  inv_congr = lib_ref "core.JMeq.congr_canonical";
}

(* Specif *)
let build_coq_sumbool () = lib_ref "core.sumbool.type"

let build_coq_eq () = lib_ref "core.eq.type"
let build_coq_eq_refl () = lib_ref "core.eq.refl"
let build_coq_eq_sym () = lib_ref "core.eq.sym"
let build_coq_f_equal2 () = lib_ref "core.eq.congr2"

(* Runtime part *)
let build_coq_True ()  = lib_ref "core.True.type"
let build_coq_I ()     = lib_ref "core.True.I"
let build_coq_identity () = lib_ref "core.identity.type"

let build_coq_eq_true () = lib_ref "core.eq_true.type"
let build_coq_jmeq () = lib_ref "core.JMeq.type"

let build_coq_prod ()   = lib_ref "core.prod.type"
let build_coq_pair ()  = lib_ref "core.prod.intro"

let build_coq_False () = lib_ref "core.False.type"
let build_coq_not ()   = lib_ref "core.not.type"
let build_coq_and ()   = lib_ref "core.and.type"
let build_coq_conj ()  = lib_ref "core.and.conj"
let build_coq_or ()    = lib_ref "core.or.type"
let build_coq_ex ()    = lib_ref "core.ex.type"
let build_coq_sig () = lib_ref "core.sig.type"
let build_coq_existT () = lib_ref "core.sigT.existT"
let build_coq_iff ()   = lib_ref "core.iff.type"

let build_coq_iff_left_proj ()  = lib_ref "core.iff.proj1"
let build_coq_iff_right_proj () = lib_ref "core.iff.proj2"

(* The following is less readable but does not depend on parsing *)
let coq_eq_ref      = Lazy.from_fun build_coq_eq
let coq_identity_ref = Lazy.from_fun build_coq_identity
let coq_jmeq_ref     = Lazy.from_fun build_coq_jmeq
let coq_eq_true_ref = Lazy.from_fun build_coq_eq_true
let coq_existS_ref  = Lazy.from_fun build_coq_existT
let coq_existT_ref  = Lazy.from_fun build_coq_existT
let coq_exist_ref  = Lazy.from_fun build_coq_ex
let coq_not_ref     = Lazy.from_fun build_coq_not
let coq_False_ref   = Lazy.from_fun build_coq_False
let coq_sumbool_ref = Lazy.from_fun build_coq_sumbool
let coq_sig_ref = Lazy.from_fun build_coq_sig
let coq_or_ref     = Lazy.from_fun build_coq_or
let coq_iff_ref    = Lazy.from_fun build_coq_iff

(** Deprecated functions that search by library name. *)
let build_sigma_set () = anomaly (Pp.str "Use build_sigma_type.")
