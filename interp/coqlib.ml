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

(************************************************************************)
(* New API *)
let make_dir l = DirPath.make (List.rev_map Id.of_string l)

let find_reference locstr dir s =
  let sp = Libnames.make_path (make_dir dir) (Id.of_string s) in
  try Nametab.global_of_path sp
  with Not_found ->
    (* Format.eprintf "ref not found %s %s\n%!" locstr s; *)
    (* Printexc.print_backtrace stderr; *)
    anomaly ~label:locstr (str "cannot find " ++ Libnames.pr_path sp)

let ssr = true

let coq = Nameops.coq_string (* "Coq" *)
let init_dir = if ssr
  then [ "mathcomp"; "ssreflect" ]
  else [coq; "Init"]

let lib_prelude, lib_logic, lib_data, lib_type, lib_specif = if ssr
  then "init", "init", "init", "init", "init"
  else "Prelude", "Logic", "Datatypes", "Logic_Type", "Specif"

let prelude_module_name    = init_dir@[lib_prelude]
let prelude_module         = make_dir prelude_module_name

let logic_module_name      = init_dir@[lib_logic]
let logic_module           = make_dir logic_module_name

let logic_type_module_name = init_dir@[lib_type]
let logic_type_module      = make_dir logic_type_module_name

let datatypes_module_name  = init_dir@[lib_data]
let datatypes_module       = make_dir datatypes_module_name

let specif_module_name     = init_dir@[lib_specif]

let jmeq_module_name       = [coq;"Logic";"JMeq"]
let jmeq_module            = make_dir jmeq_module_name

let std_table : (string * string list * string) array =
  let logic_lib = logic_module_name      in
  let data_lib  = datatypes_module_name  in
  let type_lib  = logic_type_module_name in
  let spec_lib  = specif_module_name     in
  let jmeq_lib  = jmeq_module_name       in
  [| "core.False.type", logic_lib, "False"

   ; "core.True.type",  logic_lib, "True"
   ; "core.True.I",     logic_lib, "I"

   ; "core.not.type",   logic_lib, "not"

   ; "core.or.type",    logic_lib, "or"
   ; "core.or.ind",     logic_lib, "or_ind"

   ; "core.and.type",   logic_lib, "and"
   ; "core.and.ind",    logic_lib, "and_ind"

   ; "core.iff.type",   logic_lib, "iff"
   ; "core.iff.proj1",  logic_lib, "proj1"
   ; "core.iff.proj2",  logic_lib, "proj2"

   ; "core.ex.type",    logic_lib, "ex"
   ; "core.ex.ind",     logic_lib, "ex_ind"
   ; "core.ex.intro",   logic_lib, "ex_intro"

   ; "core.eq.type",    logic_lib, "eq"
   ; "core.eq.refl",    logic_lib, "eq_refl"
   ; "core.eq.ind",     logic_lib, "eq_ind"
   ; "core.eq.rect",    logic_lib, "eq_rect"
   ; "core.eq.sym",     logic_lib, "eq_sym"
   ; "core.eq.congr",   logic_lib, "f_equal"
   ; "core.eq.trans",   logic_lib, "eq_trans"
   (* Is not there? *)
   ; "core.eq.congr_canonical", logic_lib, "f_equal_canonical_form"

   ; "core.id.type",    data_lib, "identity"
   ; "core.id.refl",    data_lib, "identity_refl"
   ; "core.id.ind",     data_lib, "identity_ind"
   ; "core.id.sym",     type_lib, "identity_sym"
   ; "core.id.congr",   type_lib, "identity_congr"
   ; "core.id.trans",   type_lib, "identity_trans"
   (* Also doesn't seem there *)
   ; "core.id.congr_canonical",   ["Coq"; "Init"; "Logic_Type"], "identity_congr_canonical_form"

   ; "core.prod.type",   data_lib, "prod"
   ; "core.prod.rect",   data_lib, "prod_rect"
   ; "core.prod.intro",  data_lib, "pair"
   ; "core.prod.proj1",  data_lib, "fst"
   ; "core.prod.proj2",  data_lib, "snd"

   ; "core.sig.type",    spec_lib, "sig"
   ; "core.sig.rect",    spec_lib, "sig_rec"
   ; "core.sig.intro",   spec_lib, "exist"
   ; "core.sig.proj1",   spec_lib, "proj1_sig"
   ; "core.sig.proj2",   spec_lib, "proj2_sig"

   ; "core.sigT.type",   spec_lib, "sigT"
   ; "core.sigT.rect",   spec_lib, "sigT_rect"
   ; "core.sigT.intro",  spec_lib, "existT"
   ; "core.sigT.proj1",  spec_lib, "projT1"
   ; "core.sigT.proj2",  spec_lib, "projT2"

   ; "core.sumbool.type", spec_lib, "sumbool"

   ; "core.jmeq.type",   jmeq_lib, "JMeq"
   ; "core.jmeq.refl",   jmeq_lib, "JMeq_refl"
   ; "core.jmeq.ind",    jmeq_lib, "JMeq_ind"
   ; "core.jmeq.sym",    jmeq_lib, "JMeq_sym"
   ; "core.jmeq.congr",  jmeq_lib, "JMeq_congr"
   ; "core.jmeq.trans",  jmeq_lib, "JMeq_trans"
   ; "core.jmeq.hom",    jmeq_lib, "JMeq_hom"
   ; "core.jmeq.congr_canonical", jmeq_lib, "JMeq_congr_canonical_form"

   ; "core.bool.type",            data_lib, "bool"
   ; "core.bool.true",            data_lib, "true"
   ; "core.bool.false",           data_lib, "false"
   ; "core.bool.andb",            data_lib, "andb"
   ; "core.bool.andb_prop",       data_lib, "andb_prop"
   ; "core.bool.andb_true_intro", data_lib, "andb_true_intro"
   ; "core.bool.orb",             data_lib, "orb"
   ; "core.bool.xorb",            data_lib, "xorb"
   ; "core.bool.negb",            data_lib, "negb"

   ; "core.eq_true.type",         data_lib, "eq_true"
   ; "core.eq_true.ind",          data_lib, "eq_true_ind"
   (* Not in the lib *)
   ; "core.eq_true.congr",  logic_lib,     "eq_true_congr"

   ; "core.list.type",   data_lib, "list"
   ; "core.list.nil",    data_lib, "nil"
   ; "core.list.cons",   data_lib, "cons"

  |]

let table = std_table

let table : (string, global_reference Lazy.t) Hashtbl.t =
  let ht = Hashtbl.create (2 * Array.length table) in
  Array.iter (fun (b, path, s) -> Hashtbl.add ht b @@ lazy (find_reference "table" path s)) table;
  ht

(** Can throw Not_found *)
let get_ref    s =
  (* Format.eprintf "get_ref %s \n%!" s; *)
  try Lazy.force (Hashtbl.find table s)
  with | Not_found ->
    Format.eprintf "not found in table: %s %!" s; raise Not_found

let get_constr s = Universes.constr_of_global (get_ref s)

(** Replaces a binding ! *)
let add_ref  s c =
  (* Format.eprintf "add_ref_log: %s\n%!" s; *)
  Hashtbl.add table s (Lazy.from_val c)

(************************************************************************)
(* Generic functions to find Coq objects *)

type message = string

let has_suffix_in_dirs dirs ref =
  let dir = dirpath (path_of_global ref) in
  List.exists (fun d -> is_dirpath_prefix_of d dir) dirs

let global_of_extended q =
  try Some (Nametab.global_of_path q) with Not_found -> None

let gen_reference_in_modules locstr dirs s =
  let dirs = List.map make_dir dirs   in
  let qualid = qualid_of_string s     in
  let all = Nametab.locate_all qualid in
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

let arith_dir     = [ coq ; "Arith"   ]
let arith_modules = [ arith_dir       ]
let numbers_dir   = [ coq ; "Numbers" ]
let parith_dir    = [ coq ; "PArith"  ]
let narith_dir    = [ coq ; "NArith"  ]
let zarith_dir    = [ coq ; "ZArith"  ]

let zarith_base_modules =
  [ numbers_dir
  ; parith_dir
  ; narith_dir
  ; zarith_dir
  ]

let init_modules = [
  init_dir @ [ "Datatypes"  ];
  init_dir @ [ "Logic"      ];
  init_dir @ [ "Specif"     ];
  init_dir @ [ "Logic_Type" ];
  init_dir @ [ "Nat"        ];
  init_dir @ [ "Peano"      ];
  init_dir @ [ "Wf"         ]
]

let coq_reference locstr dir s = find_reference locstr (coq::dir) s

(* TODO: temporary hack. Works only if the module isn't an alias *)
let make_ind dir id = Globnames.encode_mind dir (Id.of_string id)
let make_con dir id = Globnames.encode_con dir  (Id.of_string id)

(** Identity *)

let id         = make_con datatypes_module "idProp"
let type_of_id = make_con datatypes_module "IDProp"

let _ = Termops.set_impossible_default_clause
  (fun () ->
    let c, ctx = Universes.fresh_global_instance (Global.env()) (ConstRef id) in
    let (_, u) = destConst c in
      (c,mkConstU (type_of_id, u)), ctx)

(** Natural numbers *)
let nat_kn   = make_ind datatypes_module "nat"
let nat_path = Libnames.make_path datatypes_module (Id.of_string "nat")

let glob_nat = IndRef (nat_kn,0)

let path_of_O = ((nat_kn,0),1)
let path_of_S = ((nat_kn,0),2)
let glob_O    = ConstructRef path_of_O
let glob_S    = ConstructRef path_of_S

(** Equality *)
let eq_kn         = make_ind logic_module "eq"
let glob_eq       = IndRef (eq_kn,0)

let identity_kn   = make_ind datatypes_module "identity"
let glob_identity = IndRef (identity_kn,0)

let jmeq_kn       = make_ind jmeq_module "JMeq"
let glob_jmeq     = IndRef (jmeq_kn,0)

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
let build_coq_jmeq_data     () = build_eqdata_gen jmeq_module_name  "jmeq"
let build_coq_identity_data () = build_eqdata_gen datatypes_module_name "id"

(* Inversion data... *)

(* Data needed for discriminate and injection *)
type coq_inversion_data = {
  inv_eq   : global_reference; (* : forall params, t -> Prop *)
  inv_ind  : global_reference; (* : forall params P y, eq params y -> P y *)
  inv_congr: global_reference  (* : forall params B (f:t->B) y, eq params y -> f c=f y *)
}

let build_coq_inversion_gen l str =
  List.iter check_required_library l; {
    inv_eq    = get_ref ("core." ^ str ^ ".type");
    inv_ind   = get_ref ("core." ^ str ^ ".ind");
    inv_congr = get_ref ("core." ^ str ^ ".congr_canonical");
  }

let build_coq_inversion_eq_data () =
  build_coq_inversion_gen [logic_module_name] "eq"

let build_coq_inversion_identity_data () =
  build_coq_inversion_gen [datatypes_module_name; logic_type_module_name] "id"

let build_coq_inversion_eq_true_data () =
  build_coq_inversion_gen [datatypes_module_name; logic_module_name] "eq_true"

let build_coq_inversion_jmeq_data () =
  let _ = check_required_library logic_module_name in {
  inv_eq    = get_ref "core.jmeq.hom";
  inv_ind   = get_ref "core.jmeq.ind";
  inv_congr = get_ref "core.jmeq.congr_canonical"; }

