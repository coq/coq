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

let make_dir l = make_dirpath (List.map id_of_string (List.rev l))

let gen_reference locstr dir s =
  let dir = make_dir ("Coq"::dir) in
  let id = Constrextern.id_of_v7_string s in
  let sp = Libnames.make_path dir id in
  try
    Nametab.absolute_reference sp
  with Not_found ->
    anomaly (locstr^": cannot find "^(string_of_path sp))
    
let gen_constant locstr dir s = 
  constr_of_reference (gen_reference locstr dir s)

let list_try_find f = 
  let rec try_find_f = function
    | [] -> raise Not_found
    | h::t -> try f h with Not_found -> try_find_f t
  in 
  try_find_f

let has_suffix_in_dirs dirs ref =
  let dir = dirpath (sp_of_global ref) in
  List.exists (fun d -> is_dirpath_prefix_of d dir) dirs

let gen_constant_in_modules locstr dirs s =
  let dirs = List.map make_dir dirs in
  let id = Constrextern.id_of_v7_string s in
  let all = Nametab.locate_all (make_short_qualid id) in
  let these = List.filter (has_suffix_in_dirs dirs) all in
  match these with
    | [x] -> constr_of_reference x
    | [] ->
	anomalylabstrm "" (str (locstr^": cannot find "^s^
	" in module"^(if List.length dirs > 1 then "s " else " ")) ++
	prlist_with_sep pr_coma pr_dirpath dirs)
    | l ->
	anomalylabstrm "" 
	(str (locstr^": found more than once object of name "^s^
	" in module"^(if List.length dirs > 1 then "s " else " ")) ++
	prlist_with_sep pr_coma pr_dirpath dirs)

let init_reference dir s=gen_reference "Coqlib" ("Init"::dir) s

let init_constant dir s=gen_constant "Coqlib" ("Init"::dir) s  

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
let make_path dir id = Libnames.encode_kn dir id

let nat_path = make_path datatypes_module (id_of_string "nat")

let glob_nat = IndRef (nat_path,0)

let path_of_O = ((nat_path,0),1)
let path_of_S = ((nat_path,0),2)
let glob_O = ConstructRef path_of_O
let glob_S = ConstructRef path_of_S

let eq_path = make_path logic_module (id_of_string "eq")
let eqT_path = make_path logic_module (id_of_string "eq")

let glob_eq = IndRef (eq_path,0)
let glob_eqT = IndRef (eqT_path,0)

type coq_sigma_data = {
  proj1 : constr;
  proj2 : constr;
  elim  : constr;
  intro : constr;
  typ   : constr }

type 'a delayed = unit -> 'a

let build_sigma_set () =
  { proj1 = init_constant ["Specif"] "projS1";
    proj2 = init_constant ["Specif"] "projS2";
    elim = init_constant ["Specif"] "sigS_rec";
    intro = init_constant ["Specif"] "existS";
    typ = init_constant ["Specif"] "sigS" }

let build_sigma_type () =
  { proj1 = init_constant ["Specif"] "projT1";
    proj2 = init_constant ["Specif"] "projT2";
    elim = init_constant ["Specif"] "sigT_rec";
    intro = init_constant ["Specif"] "existT";
    typ = init_constant ["Specif"] "sigT" }

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
  sym  = Lazy.force coq_eq_sym }

let build_coq_eq () = Lazy.force coq_eq_eq
let build_coq_f_equal2 () = Lazy.force coq_f_equal2

(* Specif *)
let coq_sumbool  = lazy_init_constant ["Specif"] "sumbool"

let build_coq_sumbool () = Lazy.force coq_sumbool

(* Equality on Type *)

let coq_eqT_eq = lazy_init_constant ["Logic"] "eq"
let coq_eqT_refl = lazy_init_constant ["Logic"] "refl_equal"
let coq_eqT_ind = lazy_init_constant ["Logic"] "eq_ind"
let coq_eqT_congr =lazy_init_constant ["Logic"] "f_equal"
let coq_eqT_sym  = lazy_init_constant ["Logic"] "sym_eq"

let build_coq_eqT_data () = {
  eq = Lazy.force coq_eqT_eq;
  refl = Lazy.force coq_eqT_refl;
  ind = Lazy.force coq_eqT_ind;
  rrec = None;
  rect = None;
  congr = Lazy.force coq_eqT_congr;
  sym  = Lazy.force coq_eqT_sym }

let build_coq_eqT () = Lazy.force coq_eqT_eq
let build_coq_sym_eqT () = Lazy.force coq_eqT_sym

(* Equality on Type as a Type *)
let coq_idT_eq = lazy_init_constant ["Datatypes"] "identity"
let coq_idT_refl = lazy_init_constant ["Datatypes"] "refl_identity"
let coq_idT_ind = lazy_init_constant ["Datatypes"] "identity_ind"
let coq_idT_rec = lazy_init_constant ["Datatypes"] "identity_rec"
let coq_idT_rect = lazy_init_constant ["Datatypes"] "identity_rect"
let coq_idT_congr = lazy_init_constant ["Logic_Type"] "congr_id"
let coq_idT_sym = lazy_init_constant ["Logic_Type"] "sym_id"

let build_coq_idT_data () = {
  eq = Lazy.force coq_idT_eq;
  refl = Lazy.force coq_idT_refl;
  ind = Lazy.force coq_idT_ind;
  rrec = Some (Lazy.force coq_idT_rec);
  rect = Some (Lazy.force coq_idT_rect);
  congr = Lazy.force coq_idT_congr;
  sym  = Lazy.force coq_idT_sym }

let lazy_init_constant_v7 d id id7 =
  if !Options.v7 then lazy_init_constant d id else 
  lazy (anomaly
   (id7^" does no longer exist in V8 new syntax, use "^id
    ^" instead (probably an error in ML contributed code)"))

(* Empty Type *)
let coq_EmptyT = lazy_init_constant_v7 ["Logic"] "False" "EmptyT"

(* Unit Type and its unique inhabitant *)
let coq_UnitT  = lazy_init_constant_v7 ["Datatypes"] "unit" "UnitT"
let coq_IT     = lazy_init_constant_v7 ["Datatypes"] "tt" "IT"

(* The False proposition *)
let coq_False  = lazy_init_constant ["Logic"] "False"

(* The True proposition and its unique proof *)
let coq_True   = lazy_init_constant ["Logic"] "True"
let coq_I      = lazy_init_constant ["Logic"] "I"

(* Connectives *)
let coq_not = lazy_init_constant ["Logic"] "not"
let coq_and = lazy_init_constant ["Logic"] "and"
let coq_or = lazy_init_constant ["Logic"] "or"
let coq_ex = lazy_init_constant ["Logic"] "ex"

(* Runtime part *)
let build_coq_EmptyT () = Lazy.force coq_EmptyT
let build_coq_UnitT () = Lazy.force coq_UnitT
let build_coq_IT ()    = Lazy.force coq_IT

let build_coq_True ()  = Lazy.force coq_True
let build_coq_I ()     = Lazy.force coq_I

let build_coq_False () = Lazy.force coq_False
let build_coq_not ()   = Lazy.force coq_not
let build_coq_and ()   = Lazy.force coq_and
let build_coq_or ()   = Lazy.force coq_or
let build_coq_ex ()   = Lazy.force coq_ex

(****************************************************************************)
(*                             Patterns                                     *)
(* This needs to have interp_constrpattern available ... 

let parse_constr s =
  try 
    Pcoq.parse_string Pcoq.Constr.constr_eoi s 
  with Stdpp.Exc_located (_ , (Stream.Failure | Stream.Error _)) ->
    error "Syntax error : not a construction"

let parse_pattern s =
  Constrintern.interp_constrpattern Evd.empty (Global.env()) (parse_constr s)
let coq_eq_pattern =
  lazy (snd (parse_pattern "(Coq.Init.Logic.eq ?1 ?2 ?3)"))
let coq_eqT_pattern =
  lazy (snd (parse_pattern "(Coq.Init.Logic.eq ?1 ?2 ?3)"))
let coq_idT_pattern =
  lazy (snd (parse_pattern "(Coq.Init.Logic_Type.identityT ?1 ?2 ?3)"))
let coq_existS_pattern =
  lazy (snd (parse_pattern "(Coq.Init.Specif.existS ?1 ?2 ?3 ?4)"))
let coq_existT_pattern = 
  lazy (snd (parse_pattern "(Coq.Init.Specif.existT ?1 ?2 ?3 ?4)"))
let coq_not_pattern =
  lazy (snd (parse_pattern "(Coq.Init.Logic.not ?)"))
let coq_imp_False_pattern =
  lazy (snd (parse_pattern "? -> Coq.Init.Logic.False"))
let coq_imp_False_pattern =
  lazy (snd (parse_pattern "? -> Coq.Init.Logic.False"))
let coq_eqdec_partial_pattern =
  lazy (snd (parse_pattern "(sumbool (eq ?1 ?2 ?3) ?4)"))
let coq_eqdec_pattern =
  lazy (snd (parse_pattern "(x,y:?1){<?1>x=y}+{~(<?1>x=y)}"))
*)

(* The following is less readable but does not depend on parsing *)
let coq_eq_ref      = lazy (init_reference ["Logic"] "eq")
let coq_eqT_ref     = coq_eq_ref
let coq_idT_ref     = lazy (init_reference ["Datatypes"] "identity")
let coq_existS_ref  = lazy (init_reference ["Specif"] "existS")
let coq_existT_ref  = lazy (init_reference ["Specif"] "existT")
let coq_not_ref     = lazy (init_reference ["Logic"] "not")
let coq_False_ref   = lazy (init_reference ["Logic"] "False")
let coq_sumbool_ref = lazy (init_reference ["Specif"] "sumbool")
let coq_sig_ref = lazy (init_reference ["Specif"] "sig")
