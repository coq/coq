(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util
open Pp
open Names
open Term
open Libnames
open Globnames
open Nametab
open Smartlocate

let coq = Nameops.coq_string (* "Coq" *)

(************************************************************************)
(* Generic functions to find Coq objects *)

type message = string

let make_dir l = DirPath.make (List.rev_map Id.of_string l)

let find_reference locstr dir s =
  let sp = Libnames.make_path (make_dir dir) (Id.of_string s) in
  try global_of_extended_global (Nametab.extended_global_of_path sp)
  with Not_found ->
    anomaly ~label:locstr (str "cannot find " ++ Libnames.pr_path sp)

let coq_reference locstr dir s = find_reference locstr (coq::dir) s
let coq_constant locstr dir s = constr_of_global (coq_reference locstr dir s)

let gen_reference = coq_reference
let gen_constant = coq_constant

let has_suffix_in_dirs dirs ref =
  let dir = dirpath (path_of_global ref) in
  List.exists (fun d -> is_dirpath_prefix_of d dir) dirs

let global_of_extended q =
  try Some (global_of_extended_global q) with Not_found -> None

let gen_constant_in_modules locstr dirs s =
  let dirs = List.map make_dir dirs in
  let qualid = qualid_of_string s in
  let all = Nametab.locate_extended_all qualid in
  let all = List.map_filter global_of_extended all in
  let all = List.sort_uniquize RefOrdered_env.compare all in
  let these = List.filter (has_suffix_in_dirs dirs) all in
  match these with
    | [x] -> constr_of_global x
    | [] ->
	anomaly ~label:locstr (str ("cannot find "^s^
	" in module"^(if List.length dirs > 1 then "s " else " ")) ++
	prlist_with_sep pr_comma pr_dirpath dirs)
    | l ->
      anomaly ~label:locstr
	(str ("ambiguous name "^s^" can represent ") ++
	   prlist_with_sep pr_comma
	   (fun x -> Libnames.pr_path (Nametab.path_of_global x)) l ++
	   str (" in module"^(if List.length dirs > 1 then "s " else " ")) ++
	   prlist_with_sep pr_comma pr_dirpath dirs)


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
(* Loading silently ...
    let m, prefix = List.sep_last d' in
    read_library
     (Loc.ghost,make_qualid (DirPath.make (List.rev prefix)) m)
*)
(* or failing ...*)
      error ("Library "^(DirPath.to_string dir)^" has to be required first.")

(************************************************************************)
(* Specific Coq objects *)

let init_reference dir s =
  let d = "Init"::dir in
  check_required_library (coq::d); gen_reference "Coqlib" d s

let init_constant dir s =
  let d = "Init"::dir in
  check_required_library (coq::d); gen_constant "Coqlib" d s

let logic_constant dir s =
  let d = "Logic"::dir in
  check_required_library (coq::d); gen_constant "Coqlib" d s

let arith_dir = [coq;"Arith"]
let arith_modules = [arith_dir]

let numbers_dir = [coq;"Numbers"]
let parith_dir = [coq;"PArith"]
let narith_dir = [coq;"NArith"]
let zarith_dir = [coq;"ZArith"]

let zarith_base_modules = [numbers_dir;parith_dir;narith_dir;zarith_dir]

let init_dir = [coq;"Init"]
let init_modules = [
  init_dir@["Datatypes"];
  init_dir@["Logic"];
  init_dir@["Specif"];
  init_dir@["Logic_Type"];
  init_dir@["Peano"];
  init_dir@["Wf"]
]

let prelude_module_name = init_dir@["Prelude"]
let prelude_module = make_dir prelude_module_name

let logic_module_name = init_dir@["Logic"]
let logic_module = make_dir logic_module_name

let logic_type_module_name = init_dir@["Logic_Type"]
let logic_type_module = make_dir logic_type_module_name

let datatypes_module_name = init_dir@["Datatypes"]
let datatypes_module = make_dir datatypes_module_name

let arith_module_name = arith_dir@["Arith"]
let arith_module = make_dir arith_module_name

let jmeq_module_name = [coq;"Logic";"JMeq"]
let jmeq_module = make_dir jmeq_module_name

(* TODO: temporary hack. Works only if the module isn't an alias *)
let make_ind dir id = Globnames.encode_mind dir (Id.of_string id)
let make_con dir id = Globnames.encode_con dir (Id.of_string id)

(** Identity *)

let id = make_con datatypes_module "id"
let type_of_id = make_con datatypes_module "ID"

let _ = Termops.set_impossible_default_clause (mkConst id,mkConst type_of_id)

(** Natural numbers *)
let nat_kn = make_ind datatypes_module "nat"
let nat_path = Libnames.make_path datatypes_module (Id.of_string "nat")

let glob_nat = IndRef (nat_kn,0)

let path_of_O = ((nat_kn,0),1)
let path_of_S = ((nat_kn,0),2)
let glob_O = ConstructRef path_of_O
let glob_S = ConstructRef path_of_S

(** Booleans *)
let bool_kn = make_ind datatypes_module "bool"

let glob_bool = IndRef (bool_kn,0)

let path_of_true = ((bool_kn,0),1)
let path_of_false = ((bool_kn,0),2)
let glob_true  = ConstructRef path_of_true
let glob_false  = ConstructRef path_of_false

(** Equality *)
let eq_kn = make_ind logic_module "eq"
let glob_eq = IndRef (eq_kn,0)

let identity_kn = make_ind datatypes_module "identity"
let glob_identity = IndRef (identity_kn,0)

let jmeq_kn = make_ind jmeq_module "JMeq"
let glob_jmeq = IndRef (jmeq_kn,0)

type coq_sigma_data = {
  proj1 : constr;
  proj2 : constr;
  elim  : constr;
  intro : constr;
  typ   : constr }

type coq_bool_data  = {
  andb : constr;
  andb_prop : constr;
  andb_true_intro : constr}

let build_bool_type () =
  { andb =  init_constant ["Datatypes"] "andb";
    andb_prop =  init_constant ["Datatypes"] "andb_prop";
    andb_true_intro =  init_constant ["Datatypes"] "andb_true_intro" }

let build_sigma_set () = anomaly (Pp.str "Use build_sigma_type")

let build_sigma_type () =
  { proj1 = init_constant ["Specif"] "projT1";
    proj2 = init_constant ["Specif"] "projT2";
    elim = init_constant ["Specif"] "sigT_rect";
    intro = init_constant ["Specif"] "existT";
    typ = init_constant ["Specif"] "sigT" }

let build_sigma () =
  { proj1 = init_constant ["Specif"] "proj1_sig";
    proj2 = init_constant ["Specif"] "proj2_sig";
    elim = init_constant ["Specif"] "sig_rect";
    intro = init_constant ["Specif"] "exist";
    typ = init_constant ["Specif"] "sig" }

let build_prod () =
  { proj1 = init_constant ["Datatypes"] "fst";
    proj2 = init_constant ["Datatypes"] "snd";
    elim = init_constant ["Datatypes"] "prod_rec";
    intro = init_constant ["Datatypes"] "pair";
    typ = init_constant ["Datatypes"] "prod" }

(* Equalities *)
type coq_eq_data = {
  eq   : constr;
  ind  : constr;
  refl : constr;
  sym  : constr;
  trans: constr;
  congr: constr }

(* Data needed for discriminate and injection *)
type coq_inversion_data = {
  inv_eq   : constr; (* : forall params, t -> Prop *)
  inv_ind  : constr; (* : forall params P y, eq params y -> P y *)
  inv_congr: constr  (* : forall params B (f:t->B) y, eq params y -> f c=f y *)
}

let lazy_init_constant dir id = lazy (init_constant dir id)
let lazy_logic_constant dir id = lazy (logic_constant dir id)

(* Leibniz equality on Type *)

let coq_eq_eq = lazy_init_constant ["Logic"] "eq"
let coq_eq_refl = lazy_init_constant ["Logic"] "eq_refl"
let coq_eq_ind = lazy_init_constant ["Logic"] "eq_ind"
let coq_eq_congr = lazy_init_constant ["Logic"] "f_equal"
let coq_eq_sym  = lazy_init_constant ["Logic"] "eq_sym"
let coq_eq_trans  = lazy_init_constant ["Logic"] "eq_trans"
let coq_f_equal2 = lazy_init_constant ["Logic"] "f_equal2"
let coq_eq_congr_canonical =
  lazy_init_constant ["Logic"] "f_equal_canonical_form"

let build_coq_eq_data () =
  let _ = check_required_library logic_module_name in {
  eq = Lazy.force coq_eq_eq;
  ind = Lazy.force coq_eq_ind;
  refl = Lazy.force coq_eq_refl;
  sym = Lazy.force coq_eq_sym;
  trans = Lazy.force coq_eq_trans;
  congr = Lazy.force coq_eq_congr }

let build_coq_eq () = Lazy.force coq_eq_eq
let build_coq_eq_refl () = Lazy.force coq_eq_refl
let build_coq_eq_sym () = Lazy.force coq_eq_sym
let build_coq_f_equal2 () = Lazy.force coq_f_equal2

let build_coq_inversion_eq_data () =
  let _ = check_required_library logic_module_name in {
  inv_eq = Lazy.force coq_eq_eq;
  inv_ind = Lazy.force coq_eq_ind;
  inv_congr = Lazy.force coq_eq_congr_canonical }

(* Heterogenous equality on Type *)

let coq_jmeq_eq = lazy_logic_constant ["JMeq"] "JMeq"
let coq_jmeq_refl = lazy_logic_constant ["JMeq"] "JMeq_refl"
let coq_jmeq_ind = lazy_logic_constant ["JMeq"] "JMeq_ind"
let coq_jmeq_sym  = lazy_logic_constant ["JMeq"] "JMeq_sym"
let coq_jmeq_congr  = lazy_logic_constant ["JMeq"] "JMeq_congr"
let coq_jmeq_trans  = lazy_logic_constant ["JMeq"] "JMeq_trans"
let coq_jmeq_congr_canonical =
  lazy_logic_constant ["JMeq"] "JMeq_congr_canonical_form"

let build_coq_jmeq_data () =
  let _ = check_required_library jmeq_module_name in {
  eq = Lazy.force coq_jmeq_eq;
  ind = Lazy.force coq_jmeq_ind;
  refl = Lazy.force coq_jmeq_refl;
  sym = Lazy.force coq_jmeq_sym;
  trans = Lazy.force coq_jmeq_trans;
  congr = Lazy.force coq_jmeq_congr }

let join_jmeq_types eq =
  mkLambda(Name (Id.of_string "A"),Termops.new_Type(),
  mkLambda(Name (Id.of_string "x"),mkRel 1,
  mkApp (eq,[|mkRel 2;mkRel 1;mkRel 2|])))

let build_coq_inversion_jmeq_data () =
  let _ = check_required_library logic_module_name in {
  inv_eq = join_jmeq_types (Lazy.force coq_jmeq_eq);
  inv_ind = Lazy.force coq_jmeq_ind;
  inv_congr = Lazy.force coq_jmeq_congr_canonical }

(* Specif *)
let coq_sumbool  = lazy_init_constant ["Specif"] "sumbool"

let build_coq_sumbool () = Lazy.force coq_sumbool

(* Equality on Type as a Type *)
let coq_identity_eq = lazy_init_constant ["Datatypes"] "identity"
let coq_identity_refl = lazy_init_constant ["Datatypes"] "identity_refl"
let coq_identity_ind = lazy_init_constant ["Datatypes"] "identity_ind"
let coq_identity_congr = lazy_init_constant ["Logic_Type"] "identity_congr"
let coq_identity_sym = lazy_init_constant ["Logic_Type"] "identity_sym"
let coq_identity_trans = lazy_init_constant ["Logic_Type"] "identity_trans"
let coq_identity_congr_canonical = lazy_init_constant ["Logic_Type"] "identity_congr_canonical_form"

let build_coq_identity_data () =
  let _ = check_required_library datatypes_module_name in {
  eq = Lazy.force coq_identity_eq;
  ind = Lazy.force coq_identity_ind;
  refl = Lazy.force coq_identity_refl;
  sym = Lazy.force coq_identity_sym;
  trans = Lazy.force coq_identity_trans;
  congr = Lazy.force coq_identity_congr }

let build_coq_inversion_identity_data () =
  let _ = check_required_library datatypes_module_name in
  let _ = check_required_library logic_type_module_name in {
  inv_eq = Lazy.force coq_identity_eq;
  inv_ind = Lazy.force coq_identity_ind;
  inv_congr = Lazy.force coq_identity_congr_canonical }

(* Equality to true *)
let coq_eq_true_eq = lazy_init_constant ["Datatypes"] "eq_true"
let coq_eq_true_ind = lazy_init_constant ["Datatypes"] "eq_true_ind"
let coq_eq_true_congr = lazy_init_constant ["Logic"] "eq_true_congr"

let build_coq_inversion_eq_true_data () =
  let _ = check_required_library datatypes_module_name in
  let _ = check_required_library logic_module_name in {
  inv_eq = Lazy.force coq_eq_true_eq;
  inv_ind = Lazy.force coq_eq_true_ind;
  inv_congr = Lazy.force coq_eq_true_congr }

(* The False proposition *)
let coq_False  = lazy_init_constant ["Logic"] "False"
let coq_proof_admitted = lazy_init_constant ["Logic"] "proof_admitted"

(* The True proposition and its unique proof *)
let coq_True   = lazy_init_constant ["Logic"] "True"
let coq_I      = lazy_init_constant ["Logic"] "I"

(* Connectives *)
let coq_not = lazy_init_constant ["Logic"] "not"
let coq_and = lazy_init_constant ["Logic"] "and"
let coq_conj = lazy_init_constant ["Logic"] "conj"
let coq_or = lazy_init_constant ["Logic"] "or"
let coq_ex = lazy_init_constant ["Logic"] "ex"
let coq_iff = lazy_init_constant ["Logic"] "iff"

let coq_iff_left_proj  = lazy_init_constant ["Logic"] "proj1"
let coq_iff_right_proj = lazy_init_constant ["Logic"] "proj2"

(* Runtime part *)
let build_coq_True ()  = Lazy.force coq_True
let build_coq_I ()     = Lazy.force coq_I

let build_coq_False () = Lazy.force coq_False
let build_coq_proof_admitted () = Lazy.force coq_proof_admitted
let build_coq_not ()   = Lazy.force coq_not
let build_coq_and ()   = Lazy.force coq_and
let build_coq_conj ()  = Lazy.force coq_conj
let build_coq_or ()    = Lazy.force coq_or
let build_coq_ex ()    = Lazy.force coq_ex
let build_coq_iff ()   = Lazy.force coq_iff

let build_coq_iff_left_proj ()  = Lazy.force coq_iff_left_proj
let build_coq_iff_right_proj () = Lazy.force coq_iff_right_proj


(* The following is less readable but does not depend on parsing *)
let coq_eq_ref      = lazy (init_reference ["Logic"] "eq")
let coq_identity_ref = lazy (init_reference ["Datatypes"] "identity")
let coq_jmeq_ref     = lazy (gen_reference "Coqlib" ["Logic";"JMeq"] "JMeq")
let coq_eq_true_ref = lazy (gen_reference "Coqlib" ["Init";"Datatypes"] "eq_true")
let coq_existS_ref  = lazy (anomaly (Pp.str "use coq_existT_ref"))
let coq_existT_ref  = lazy (init_reference ["Specif"] "existT")
let coq_exist_ref  = lazy (init_reference ["Specif"] "exist")
let coq_not_ref     = lazy (init_reference ["Logic"] "not")
let coq_False_ref   = lazy (init_reference ["Logic"] "False")
let coq_sumbool_ref = lazy (init_reference ["Specif"] "sumbool")
let coq_sig_ref = lazy (init_reference ["Specif"] "sig")
let coq_or_ref     = lazy (init_reference ["Logic"] "or")
let coq_iff_ref    = lazy (init_reference ["Logic"] "iff")

