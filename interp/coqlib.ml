(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
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

(************************************************************************)
(* New API *)
let make_dir l = DirPath.make (List.rev_map Id.of_string l)

let find_reference locstr dir s =
  let sp = Libnames.make_path (make_dir dir) (Id.of_string s) in
  try global_of_extended_global (Nametab.extended_global_of_path sp)
  with Not_found ->
    Format.eprintf "uy marcion %s %s\n%!" locstr s;
    Printexc.print_backtrace stderr;
    anomaly ~label:locstr (str "cannot find " ++ Libnames.pr_path sp)

let table : (string * string list * string) array =
  [| "core.False.type", ["Coq"; "Init"; "Logic"], "False"

   ; "core.True.type",  ["Coq"; "Init"; "Logic"], "True"

   ; "core.True.I",     ["Coq"; "Init"; "Logic"], "I"

   ; "core.not.type",   ["Coq"; "Init"; "Logic"], "not"
   ; "core.or.type",    ["Coq"; "Init"; "Logic"], "or"
   ; "core.and.type",   ["Coq"; "Init"; "Logic"], "and"

   ; "core.iff.type",   ["Coq"; "Init"; "Logic"], "iff"
   ; "core.iff.proj1",  ["Coq"; "Init"; "Logic"], "proj1"
   ; "core.iff.proj2",  ["Coq"; "Init"; "Logic"], "proj2"

   ; "core.ex.type",    ["Coq"; "Init"; "Specif"], "exist"

   ; "core.eq.type",    ["Coq"; "Init"; "Logic"], "eq"
   ; "core.eq.refl",    ["Coq"; "Init"; "Logic"], "eq_refl"
   ; "core.eq.ind",     ["Coq"; "Init"; "Logic"], "eq_ind"
   ; "core.eq.sym",     ["Coq"; "Init"; "Logic"], "eq_sym"
   ; "core.eq.congr",   ["Coq"; "Init"; "Logic"], "f_equal"
   ; "core.eq.trans",   ["Coq"; "Init"; "Logic"], "eq_trans"

   ; "core.id.type",    ["Coq"; "Init"; "Datatypes"],  "identity"
   ; "core.id.refl",    ["Coq"; "Init"; "Datatypes"],  "identity_refl"
   ; "core.id.ind",     ["Coq"; "Init"; "Datatypes"],  "identity_ind"
   ; "core.id.sym",     ["Coq"; "Init"; "Logic_Type"], "identity_sym"
   ; "core.id.congr",   ["Coq"; "Init"; "Logic_Type"], "identity_congr"
   ; "core.id.trans",   ["Coq"; "Init"; "Logic_Type"], "identity_trans"

   ; "core.prod.type",   ["Coq"; "Init"; "Datatypes"], "prod"
   ; "core.prod.rect",   ["Coq"; "Init"; "Datatypes"], "prod_rec"
   ; "core.prod.intro",  ["Coq"; "Init"; "Datatypes"], "pair"
   ; "core.prod.proj1",  ["Coq"; "Init"; "Datatypes"], "fst"
   ; "core.prod.proj2",  ["Coq"; "Init"; "Datatypes"], "snd"

   ; "core.sig.type",    ["Coq"; "Init"; "Specif"], "sig"
   ; "core.sig.rect",    ["Coq"; "Init"; "Specif"], "sig_rec"
   ; "core.sig.intro",   ["Coq"; "Init"; "Specif"], "exist"
   ; "core.sig.proj1",   ["Coq"; "Init"; "Specif"], "proj1_sig"
   ; "core.sig.proj2",   ["Coq"; "Init"; "Specif"], "proj2_sig"

   ; "core.sigT.type",   ["Coq"; "Init"; "Specif"], "sigT"
   ; "core.sigT.rect",   ["Coq"; "Init"; "Specif"], "sigT_rect"
   ; "core.sigT.intro",  ["Coq"; "Init"; "Specif"], "existT"
   ; "core.sigT.proj1",  ["Coq"; "Init"; "Specif"], "projT1"
   ; "core.sigT.proj2",  ["Coq"; "Init"; "Specif"], "projT2"

   ; "core.sumbool.type", ["Coq"; "Init"; "Specif"], "sumbool"

   ; "core.jmeq.type",   ["Coq"; "Logic"; "JMeq"], "JMeq"
   ; "core.jmeq.refl",   ["Coq"; "Logic"; "JMeq"], "JMeq_refl"
   ; "core.jmeq.ind",    ["Coq"; "Logic"; "JMeq"], "JMeq_ind"
   ; "core.jmeq.sym",    ["Coq"; "Logic"; "JMeq"], "JMeq_sym"
   ; "core.jmeq.congr",  ["Coq"; "Logic"; "JMeq"], "JMeq_congr"
   ; "core.jmeq.trans",  ["Coq"; "Logic"; "JMeq"], "JMeq_trans"


   ; "core.bool.type",   ["Coq"; "Init"; "Datatypes"], "bool"
   ; "core.bool.true",   ["Coq"; "Init"; "Datatypes"], "true"
   ; "core.bool.false",  ["Coq"; "Init"; "Datatypes"], "false"
   ; "core.bool.andb",      ["Coq"; "Init"; "Datatypes"], "andb"
   ; "core.bool.andb_prop", ["Coq"; "Init"; "Datatypes"], "andb_prop"
   ; "core.bool.andb_true_intro", ["Coq"; "Init"; "Datatypes"], "andb_true_intro"

  |]

let core_table : (string, global_reference Lazy.t) Hashtbl.t =
  let ht = Hashtbl.create (2 * Array.length table) in
  Array.iter (fun (b, path, s) -> Hashtbl.add ht b @@ lazy (find_reference "table" path s)) table;
  ht

(** Can throw Not_found *)
let get_ref    s =
  (* Format.eprintf "get_ref_log: %s\n%!" s; *)
  Lazy.force (Hashtbl.find core_table s)

let get_constr s =
  (* Format.eprintf "get_constr_log: %s\n%!" s; *)
  Universes.constr_of_global (Lazy.force (Hashtbl.find core_table s))

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

let has_suffix_in_dirs dirs ref =
  let dir = dirpath (path_of_global ref) in
  List.exists (fun d -> is_dirpath_prefix_of d dir) dirs

let global_of_extended q =
  try Some (global_of_extended_global q) with Not_found -> None

let gen_reference_in_modules locstr dirs s =
  let dirs = List.map make_dir dirs in
  let qualid = qualid_of_string s in
  let all = Nametab.locate_extended_all qualid in
  let all = List.map_filter global_of_extended all in
  let all = List.sort_uniquize RefOrdered_env.compare all in
  let these = List.filter (has_suffix_in_dirs dirs) all in
  match these with
    | [x] -> x
    | [] ->
	anomaly ~label:locstr (str "cannot find " ++ str s ++
	str " in module" ++ str (if List.length dirs > 1 then "s " else " ") ++
	prlist_with_sep pr_comma pr_dirpath dirs)
    | l ->
      anomaly ~label:locstr
	(str "ambiguous name " ++ str s ++ str " can represent " ++
	   prlist_with_sep pr_comma
	   (fun x -> Libnames.pr_path (Nametab.path_of_global x)) l ++
	   str " in module" ++ str (if List.length dirs > 1 then "s " else " ") ++
	   prlist_with_sep pr_comma pr_dirpath dirs)

let gen_constant_in_modules locstr dirs s =
  Universes.constr_of_global (gen_reference_in_modules locstr dirs s)

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
      (Printexc.print_backtrace stderr;
      errorlabstrm "Coqlib.check_required_library"
        (str "Library " ++ str (DirPath.to_string dir) ++ str " has to be required first."))

(************************************************************************)
(* Specific Coq objects *)

let coq_constant locstr dir s = Universes.constr_of_global (coq_reference locstr dir s)

let init_reference dir s =
  let d = "Init"::dir in
  check_required_library (coq::d); coq_reference "Coqlib" d s

let init_constant dir s =
  let d = "Init"::dir in
  check_required_library (coq::d); coq_constant "Coqlib" d s

let logic_reference dir s =
  let d = "Logic"::dir in
  check_required_library ("Coq"::d); coq_reference "Coqlib" d s

let arith_dir     = [coq;"Arith"]
let arith_modules = [arith_dir]

let numbers_dir = [coq; "Numbers"]
let parith_dir  = [coq; "PArith"]
let narith_dir  = [coq; "NArith"]
let zarith_dir  = [coq; "ZArith"]

let zarith_base_modules = [numbers_dir;parith_dir;narith_dir;zarith_dir]

let init_dir = [coq;"Init"]
let init_modules = [
  init_dir@["Datatypes"];
  init_dir@["Logic"];
  init_dir@["Specif"];
  init_dir@["Logic_Type"];
  init_dir@["Nat"];
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

let jmeq_module_name = [coq;"Logic";"JMeq"]
let jmeq_module = make_dir jmeq_module_name

(* TODO: temporary hack. Works only if the module isn't an alias *)
let make_ind dir id = Globnames.encode_mind dir (Id.of_string id)
let make_con dir id = Globnames.encode_con dir (Id.of_string id)

(** Identity *)

let id = make_con datatypes_module "idProp"
let type_of_id = make_con datatypes_module "IDProp"

let _ = Termops.set_impossible_default_clause 
  (fun () -> 
    let c, ctx = Universes.fresh_global_instance (Global.env()) (ConstRef id) in
    let (_, u) = destConst c in
      (c,mkConstU (type_of_id,u)), ctx)

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
let eq_kn   = make_ind logic_module "eq"
let glob_eq = IndRef (eq_kn,0)

let identity_kn   = make_ind datatypes_module "identity"
let glob_identity = IndRef (identity_kn,0)

let jmeq_kn   = make_ind jmeq_module "JMeq"
let glob_jmeq = IndRef (jmeq_kn,0)

(* Sigma data *)
type coq_sigma_data = {
  proj1 : global_reference;
  proj2 : global_reference;
  elim  : global_reference;
  intro : global_reference;
  typ   : global_reference }

let build_sigma_gen str =
  { typ   = get_ref ("core." ^ str ^ ".type");
    elim  = get_ref ("core." ^ str ^ ".rect");
    intro = get_ref ("core." ^ str ^ ".intro");
    proj1 = get_ref ("core." ^ str ^ ".proj1");
    proj2 = get_ref ("core." ^ str ^ ".proj2");
  }

let build_prod       () = build_sigma_gen "prod"
let build_sigma      () = build_sigma_gen "sig"
let build_sigma_type () = build_sigma_gen "sigT"

(* Equalities *)
type coq_eq_data = {
  eq   : global_reference;
  ind  : global_reference;
  refl : global_reference;
  sym  : global_reference;
  trans: global_reference;
  congr: global_reference }

let lazy_init_reference  dir id = lazy (init_reference dir id)
let lazy_logic_reference dir id = lazy (logic_reference dir id)

(* Leibniz equality on Type *)

let build_eqdata_gen lib str =
  let _ = check_required_library lib in {
  eq    = get_ref ("core." ^ str ^ ".type");
  ind   = get_ref ("core." ^ str ^ ".ind");
  refl  = get_ref ("core." ^ str ^ ".refl");
  sym   = get_ref ("core." ^ str ^ ".sym");
  trans = get_ref ("core." ^ str ^ ".trans");
  congr = get_ref ("core." ^ str ^ ".congr");
  }

let build_coq_eq_data       () = build_eqdata_gen logic_module_name "eq"
let build_coq_jmeq_data     () = build_eqdata_gen jmeq_module_name "jmeq"
let build_coq_identity_data () = build_eqdata_gen datatypes_module_name "id"

(* Inversion data... *)

(* Data needed for discriminate and injection *)
type coq_inversion_data = {
  inv_eq   : global_reference; (* : forall params, t -> Prop *)
  inv_ind  : global_reference; (* : forall params P y, eq params y -> P y *)
  inv_congr: global_reference  (* : forall params B (f:t->B) y, eq params y -> f c=f y *)
}

let coq_eq_congr_canonical =
  lazy_init_reference ["Logic"] "f_equal_canonical_form"

let build_coq_inversion_eq_data () =
  let _     = check_required_library logic_module_name in {
  inv_eq    = get_ref "core.eq.type";
  inv_ind   = get_ref "core.eq.ind";
  inv_congr = Lazy.force coq_eq_congr_canonical }

let coq_jmeq_hom   = lazy_logic_reference ["JMeq"] "JMeq_hom"
let coq_jmeq_congr_canonical =
  lazy_logic_reference ["JMeq"] "JMeq_congr_canonical_form"

let build_coq_inversion_jmeq_data () =
  let _ = check_required_library logic_module_name in {
  inv_eq    = Lazy.force coq_jmeq_hom;
  inv_ind   = get_ref "core.jmeq.ind";
  inv_congr = Lazy.force coq_jmeq_congr_canonical }

let coq_identity_congr_canonical = lazy_init_reference ["Logic_Type"] "identity_congr_canonical_form"

let build_coq_inversion_identity_data () =
  let _     = check_required_library datatypes_module_name in
  let _     = check_required_library logic_type_module_name in {
  inv_eq    = get_ref "core.id.type";
  inv_ind   = get_ref "core.id.ind";
  inv_congr = Lazy.force coq_identity_congr_canonical }

(* Equality to true *)
let coq_eq_true_eq    = lazy_init_reference ["Datatypes"] "eq_true"
let coq_eq_true_ind   = lazy_init_reference ["Datatypes"] "eq_true_ind"
let coq_eq_true_congr = lazy_init_reference ["Logic"]     "eq_true_congr"

let build_coq_inversion_eq_true_data () =
  let _ = check_required_library datatypes_module_name in
  let _ = check_required_library logic_module_name in {
  inv_eq    = Lazy.force coq_eq_true_eq;
  inv_ind   = Lazy.force coq_eq_true_ind;
  inv_congr = Lazy.force coq_eq_true_congr }
