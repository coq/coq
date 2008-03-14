(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Pp
open Names
open Term
open Libnames
open Pattern
open Nametab

(************************************************************************)
(* Generic functions to find Coq objects *)

type message = string

let make_dir l = make_dirpath (List.map id_of_string (List.rev l))

let find_reference locstr dir s =
  let sp = Libnames.make_path (make_dir dir) (id_of_string s) in
  try
    Nametab.absolute_reference sp
  with Not_found ->
    anomaly (locstr^": cannot find "^(string_of_path sp))

let coq_reference locstr dir s = find_reference locstr ("Coq"::dir) s
let coq_constant locstr dir s = constr_of_global (coq_reference locstr dir s)

let gen_reference = coq_reference
let gen_constant = coq_constant

let has_suffix_in_dirs dirs ref =
  let dir = dirpath (sp_of_global ref) in
  List.exists (fun d -> is_dirpath_prefix_of d dir) dirs

let gen_constant_in_modules locstr dirs s =
  let dirs = List.map make_dir dirs in
  let id = id_of_string s in
  let all = Nametab.locate_all (make_short_qualid id) in
  let these = List.filter (has_suffix_in_dirs dirs) all in
  match these with
    | [x] -> constr_of_global x
    | [] ->
	anomalylabstrm "" (str (locstr^": cannot find "^s^
	" in module"^(if List.length dirs > 1 then "s " else " ")) ++
	prlist_with_sep pr_coma pr_dirpath dirs)
    | l ->
	anomalylabstrm "" 
	(str (locstr^": found more than once object of name "^s^
	" in module"^(if List.length dirs > 1 then "s " else " ")) ++
	prlist_with_sep pr_coma pr_dirpath dirs)


(* For tactics/commands requiring vernacular libraries *)

let check_required_library d =
  let d' = List.map id_of_string d in
  let dir = make_dirpath (List.rev d') in
  if not (Library.library_is_loaded dir) then
(* Loading silently ...
    let m, prefix = list_sep_last d' in
    read_library 
     (dummy_loc,make_qualid (make_dirpath (List.rev prefix)) m)
*)
(* or failing ...*)
    error ("Library "^(list_last d)^" has to be required first")

(************************************************************************)
(* Specific Coq objects *)

let init_reference dir s = gen_reference "Coqlib" ("Init"::dir) s

let init_constant dir s = gen_constant "Coqlib" ("Init"::dir) s  

let arith_dir = ["Coq";"Arith"]
let arith_modules = [arith_dir]

let narith_dir = ["Coq";"NArith"]

let zarith_dir = ["Coq";"ZArith"]
let zarith_base_modules = [narith_dir;zarith_dir]

let init_dir = ["Coq";"Init"]
let init_modules = [
  init_dir@["Datatypes"];
  init_dir@["Logic"];
  init_dir@["Specif"];
  init_dir@["Logic_Type"];
  init_dir@["Peano"];
  init_dir@["Wf"]
]
  
let coq_id = id_of_string "Coq"
let init_id = id_of_string "Init"
let arith_id = id_of_string "Arith"
let datatypes_id = id_of_string "Datatypes"

let logic_module = make_dir ["Coq";"Init";"Logic"]
let logic_type_module = make_dir ["Coq";"Init";"Logic_Type"]
let datatypes_module = make_dir ["Coq";"Init";"Datatypes"]
let arith_module = make_dir ["Coq";"Arith";"Arith"]

(* TODO: temporary hack *)
let make_kn dir id = Libnames.encode_kn dir id

(** Natural numbers *)
let nat_kn = make_kn datatypes_module (id_of_string "nat")
let nat_path = Libnames.make_path datatypes_module (id_of_string "nat")

let glob_nat = IndRef (nat_kn,0)

let path_of_O = ((nat_kn,0),1)
let path_of_S = ((nat_kn,0),2)
let glob_O = ConstructRef path_of_O
let glob_S = ConstructRef path_of_S

(** Booleans *)
let bool_kn = make_kn datatypes_module (id_of_string "bool")

let glob_bool = IndRef (bool_kn,0)

let path_of_true = ((bool_kn,0),1)
let path_of_false = ((bool_kn,0),2)
let glob_true  = ConstructRef path_of_true
let glob_false  = ConstructRef path_of_false

(** Equality *)
let eq_kn = make_kn logic_module (id_of_string "eq")

let glob_eq = IndRef (eq_kn,0)

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

type 'a delayed = unit -> 'a

let build_bool_type () = 
  { andb =  init_constant ["Datatypes"] "andb";
    andb_prop =  init_constant ["Datatypes"] "andb_prop";
    andb_true_intro =  init_constant ["Datatypes"] "andb_true_intro" }


let build_sigma_set () = anomaly "Use build_sigma_type"

let build_sigma_type () =
  { proj1 = init_constant ["Specif"] "projT1";
    proj2 = init_constant ["Specif"] "projT2";
    elim = init_constant ["Specif"] "sigT_rec";
    intro = init_constant ["Specif"] "existT";
    typ = init_constant ["Specif"] "sigT" }

let build_prod () =
  { proj1 = init_constant ["Datatypes"] "fst";
    proj2 = init_constant ["Datatypes"] "snd";
    elim = init_constant ["Datatypes"] "prod_rec";
    intro = init_constant ["Datatypes"] "pair";
    typ = init_constant ["Datatypes"] "prod" }

(* Equalities *)
type coq_leibniz_eq_data = {
  eq   : constr;
  refl : constr;
  ind  : constr;
  rrec : constr option;
  rect : constr option;
  congr: constr;
  sym  : constr }

let lazy_init_constant dir id = lazy (init_constant dir id)

(* Equality on Set *)
let coq_eq_eq = lazy_init_constant ["Logic"] "eq"
let coq_eq_refl = lazy_init_constant ["Logic"] "refl_equal"
let coq_eq_ind = lazy_init_constant ["Logic"] "eq_ind"
let coq_eq_rec = lazy_init_constant ["Logic"] "eq_rec"
let coq_eq_rect = lazy_init_constant ["Logic"] "eq_rect"
let coq_eq_congr = lazy_init_constant ["Logic"] "f_equal"
let coq_eq_sym  = lazy_init_constant ["Logic"] "sym_eq"
let coq_f_equal2 = lazy_init_constant ["Logic"] "f_equal2"

let build_coq_eq_data () = {
  eq = Lazy.force coq_eq_eq;
  refl = Lazy.force coq_eq_refl;
  ind = Lazy.force coq_eq_ind;
  rrec = Some (Lazy.force coq_eq_rec);
  rect = Some (Lazy.force coq_eq_rect);
  congr = Lazy.force coq_eq_congr;
  sym = Lazy.force coq_eq_sym }

let build_coq_eq () = Lazy.force coq_eq_eq
let build_coq_sym_eq () = Lazy.force coq_eq_sym
let build_coq_f_equal2 () = Lazy.force coq_f_equal2

(* Specif *)
let coq_sumbool  = lazy_init_constant ["Specif"] "sumbool"

let build_coq_sumbool () = Lazy.force coq_sumbool

(* Equality on Type as a Type *)
let coq_identity_eq = lazy_init_constant ["Datatypes"] "identity"
let coq_identity_refl = lazy_init_constant ["Datatypes"] "refl_identity"
let coq_identity_ind = lazy_init_constant ["Datatypes"] "identity_ind"
let coq_identity_rec = lazy_init_constant ["Datatypes"] "identity_rec"
let coq_identity_rect = lazy_init_constant ["Datatypes"] "identity_rect"
let coq_identity_congr = lazy_init_constant ["Logic_Type"] "congr_id"
let coq_identity_sym = lazy_init_constant ["Logic_Type"] "sym_id"

let build_coq_identity_data () = {
  eq = Lazy.force coq_identity_eq;
  refl = Lazy.force coq_identity_refl;
  ind = Lazy.force coq_identity_ind;
  rrec = Some (Lazy.force coq_identity_rec);
  rect = Some (Lazy.force coq_identity_rect);
  congr = Lazy.force coq_identity_congr;
  sym = Lazy.force coq_identity_sym }

(* The False proposition *)
let coq_False  = lazy_init_constant ["Logic"] "False"

(* The True proposition and its unique proof *)
let coq_True   = lazy_init_constant ["Logic"] "True"
let coq_I      = lazy_init_constant ["Logic"] "I"

(* Connectives *)
let coq_not = lazy_init_constant ["Logic"] "not"
let coq_and = lazy_init_constant ["Logic"] "and"
let coq_conj = lazy_init_constant ["Logic"] "conj"
let coq_or = lazy_init_constant ["Logic"] "or"
let coq_ex = lazy_init_constant ["Logic"] "ex"

(* Runtime part *)
let build_coq_True ()  = Lazy.force coq_True
let build_coq_I ()     = Lazy.force coq_I

let build_coq_False () = Lazy.force coq_False
let build_coq_not ()   = Lazy.force coq_not
let build_coq_and ()   = Lazy.force coq_and
let build_coq_conj ()  = Lazy.force coq_conj
let build_coq_or ()   = Lazy.force coq_or
let build_coq_ex ()   = Lazy.force coq_ex

(* The following is less readable but does not depend on parsing *)
let coq_eq_ref      = lazy (init_reference ["Logic"] "eq")
let coq_identity_ref     = lazy (init_reference ["Datatypes"] "identity")
let coq_existS_ref  = lazy (anomaly "use coq_existT_ref")
let coq_existT_ref  = lazy (init_reference ["Specif"] "existT")
let coq_not_ref     = lazy (init_reference ["Logic"] "not")
let coq_False_ref   = lazy (init_reference ["Logic"] "False")
let coq_sumbool_ref = lazy (init_reference ["Specif"] "sumbool")
let coq_sig_ref = lazy (init_reference ["Specif"] "sig")
let coq_or_ref     = lazy (init_reference ["Logic"] "or")

