(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Names
open Term
open Declare
open Pattern
open Nametab

let make_dir l = make_dirpath (List.map id_of_string l)
let coq_id = id_of_string "Coq"
let init_id = id_of_string "Init"
let arith_id = id_of_string "Arith"
let datatypes_id = id_of_string "Datatypes"

let logic_module = make_dir ["Coq";"Init";"Logic"]
let logic_type_module = make_dir ["Coq";"Init";"Logic_Type"]
let datatypes_module = make_dir ["Coq";"Init";"Datatypes"]
let arith_module = make_dir ["Coq";"Arith";"Arith"]

let nat_path = make_path datatypes_module (id_of_string "nat") CCI
let myvar_path =
  make_path arith_module (id_of_string "My_special_variable") CCI

let glob_nat = IndRef (nat_path,0)

let glob_O = ConstructRef ((nat_path,0),1)
let glob_S = ConstructRef ((nat_path,0),2)

let glob_My_special_variable_nat = ConstRef myvar_path

let eq_path = make_path logic_module (id_of_string "eq") CCI
let eqT_path = make_path logic_type_module (id_of_string "eqT") CCI

let glob_eq = IndRef (eq_path,0)
let glob_eqT = IndRef (eqT_path,0)

let reference dir s =
  let dir = make_dir ("Coq"::"Init"::[dir]) in
  let id = id_of_string s in
  try 
    Nametab.locate_in_absolute_module dir id
  with Not_found ->
    anomaly ("Coqlib: cannot find "^(string_of_qualid (make_qualid dir id)))

let constant dir s = Declare.constr_of_reference (reference dir s)

type coq_sigma_data = {
  proj1 : constr;
  proj2 : constr;
  elim  : constr;
  intro : constr;
  typ   : constr }

type 'a delayed = unit -> 'a

let build_sigma_set () =
  { proj1 = constant "Specif" "projS1";
    proj2 = constant "Specif" "projS2";
    elim = constant "Specif" "sigS_rec";
    intro = constant "Specif" "existS";
    typ = constant "Specif" "sigS" }

let build_sigma_type () =
  { proj1 = constant "Specif" "projT1";
    proj2 = constant "Specif" "projT2";
    elim = constant "Specif" "sigT_rec";
    intro = constant "Specif" "existT";
    typ = constant "Specif" "sigT" }

(* Equalities *)
type coq_leibniz_eq_data = {
  eq   : constr delayed;
  ind  : constr delayed;
  rrec : constr delayed option;
  rect : constr delayed option;
  congr: constr delayed;
  sym  : constr delayed }

let constant dir id = lazy (constant dir id)

(* Equality on Set *)
let coq_eq_eq = constant "Logic" "eq"
let coq_eq_ind = constant "Logic" "eq_ind"
let coq_eq_rec = constant "Logic" "eq_rec"
let coq_eq_rect = constant "Logic" "eq_rect"
let coq_eq_congr = constant "Logic" "f_equal"
let coq_eq_sym  = constant "Logic" "sym_eq"
let coq_f_equal2 = constant "Logic" "f_equal2"

let build_coq_eq_data = {
  eq = (fun () -> Lazy.force coq_eq_eq);
  ind = (fun () -> Lazy.force coq_eq_ind);
  rrec = Some (fun () -> Lazy.force coq_eq_rec);
  rect = Some (fun () -> Lazy.force coq_eq_rect);
  congr = (fun () -> Lazy.force coq_eq_congr);
  sym  = (fun () -> Lazy.force coq_eq_sym) }

let build_coq_eq = build_coq_eq_data.eq
let build_coq_f_equal2 () = Lazy.force coq_f_equal2

(* Specif *)
let coq_sumbool  = constant "Specif" "sumbool"

let build_coq_sumbool () = Lazy.force coq_sumbool

(* Equality on Type *)
let coq_eqT_eq = constant "Logic_Type" "eqT"
let coq_eqT_ind = constant "Logic_Type" "eqT_ind"
let coq_eqT_congr =constant "Logic_Type" "congr_eqT"
let coq_eqT_sym  = constant "Logic_Type" "sym_eqT"

let build_coq_eqT_data = {
  eq = (fun () -> Lazy.force coq_eqT_eq);
  ind = (fun () -> Lazy.force coq_eqT_ind);
  rrec = None;
  rect = None;
  congr = (fun () -> Lazy.force coq_eqT_congr);
  sym  = (fun () -> Lazy.force coq_eqT_sym) }

let build_coq_eqT = build_coq_eqT_data.eq
let build_coq_sym_eqT = build_coq_eqT_data.sym

(* Equality on Type as a Type *)
let coq_idT_eq = constant "Logic_Type" "identityT"
let coq_idT_ind = constant "Logic_Type" "identityT_ind"
let coq_idT_rec = constant "Logic_Type" "identityT_rec"
let coq_idT_rect = constant "Logic_Type" "identityT_rect"
let coq_idT_congr = constant "Logic_Type" "congr_idT"
let coq_idT_sym = constant "Logic_Type" "sym_idT"

let build_coq_idT_data = {
  eq = (fun () -> Lazy.force coq_idT_eq);
  ind = (fun () -> Lazy.force coq_idT_ind);
  rrec = Some (fun () -> Lazy.force coq_idT_rec);
  rect = Some (fun () -> Lazy.force coq_idT_rect);
  congr = (fun () -> Lazy.force coq_idT_congr);
  sym  = (fun () -> Lazy.force coq_idT_sym) }

(* Empty Type *)
let coq_EmptyT = constant "Logic_Type" "EmptyT"

(* Unit Type and its unique inhabitant *)
let coq_UnitT  = constant "Logic_Type" "UnitT"
let coq_IT     = constant "Logic_Type" "IT"

(* The False proposition *)
let coq_False  = constant "Logic" "False"

(* The True proposition and its unique proof *)
let coq_True   = constant "Logic" "True"
let coq_I      = constant "Logic" "I"

(* Connectives *)
let coq_not = constant "Logic" "not"
let coq_and = constant "Logic" "and"
let coq_or = constant "Logic" "or"
let coq_ex = constant "Logic" "ex"

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
let parse_astconstr s =
  try 
    Pcoq.parse_string Pcoq.Constr.constr_eoi s 
  with Stdpp.Exc_located (_ , (Stream.Failure | Stream.Error _)) ->
    error "Syntax error : not a construction"

let parse_pattern s =
  Astterm.interp_constrpattern Evd.empty (Global.env()) (parse_astconstr s)

let coq_eq_pattern =
  lazy (snd (parse_pattern "(Coq.Init.Logic.eq ?1 ?2 ?3)"))
let coq_eqT_pattern =
  lazy (snd (parse_pattern "(Coq.Init.Logic_Type.eqT ?1 ?2 ?3)"))
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
let coq_eqdec_partial_pattern
  lazy (snd (parse_pattern "(sumbool (eq ?1 ?2 ?3) ?4)"))
let coq_eqdec_pattern
  lazy (snd (parse_pattern "(x,y:?1){<?1>x=y}+{~(<?1>x=y)}"))
*)

(* The following is less readable but does not depend on parsing *)
let coq_eq_ref      = lazy (reference "Logic" "eq")
let coq_eqT_ref     = lazy (reference "Logic_Type" "eqT")
let coq_idT_ref     = lazy (reference "Logic_Type" "identityT")
let coq_existS_ref  = lazy (reference "Specif" "existS")
let coq_existT_ref  = lazy (reference "Specif" "existT")
let coq_not_ref     = lazy (reference "Logic" "not")
let coq_False_ref   = lazy (reference "Logic" "False")
let coq_sumbool_ref = lazy (reference "Specif" "sumbool")
let coq_sig_ref = lazy (reference "Specif" "sig")

(* Pattern "(sig ?1 ?2)" *)
let coq_sig_pattern = 
  lazy (PApp (PRef (Lazy.force coq_sig_ref), 
	      [| PMeta (Some 1); PMeta (Some 2) |]))

(* Patterns "(eq ?1 ?2 ?3)", "(eqT ?1 ?2 ?3)" and "(idT ?1 ?2 ?3)" *)
let coq_eq_pattern_gen eq = 
  lazy (PApp(PRef (Lazy.force eq), Array.init 3 (fun i -> PMeta (Some (i+1)))))
let coq_eq_pattern = coq_eq_pattern_gen coq_eq_ref
let coq_eqT_pattern = coq_eq_pattern_gen coq_eqT_ref
let coq_idT_pattern = coq_eq_pattern_gen coq_idT_ref

(* Patterns "(existS ?1 ?2 ?3 ?4)" and "(existT ?1 ?2 ?3 ?4)" *)
let coq_ex_pattern_gen ex =
  lazy (PApp(PRef (Lazy.force ex), Array.init 4 (fun i -> PMeta (Some (i+1)))))
let coq_existS_pattern = coq_ex_pattern_gen coq_existS_ref
let coq_existT_pattern = coq_ex_pattern_gen coq_existT_ref

(* Patterns "~ ?", "? -> False" and "(?1 -> ?2)" *)
let coq_not_pattern = lazy(PApp(PRef (Lazy.force coq_not_ref), [|PMeta None|]))
let imp a b = PProd (Anonymous, a, b)
let coq_imp_False_pattern =
  lazy (imp (PMeta None) (PRef (Lazy.force coq_False_ref)))
let coq_arrow_pattern = lazy (imp (PMeta (Some 1)) (PMeta (Some 2)))

(* Pattern "(sumbool (eq ?1 ?2 ?3) ?4)" *)
let coq_eqdec_partial_pattern =
  lazy
    (PApp
       (PRef (Lazy.force coq_sumbool_ref),
	[| Lazy.force coq_eq_pattern; PMeta (Some 4) |]))

(* The expected form of the goal for the tactic Decide Equality *)

(* Pattern "(x,y:?1){<?1>x=y}+{~(<?1>x=y)}" *)
(* i.e. "(x,y:?1)(sumbool (eq ?1 x y) ~(eq ?1 x y))" *)
let x = Name (id_of_string "x")
let y = Name (id_of_string "y")
let coq_eqdec_pattern =
  lazy
    (PProd (x, PMeta (Some 1), PProd (y, PMeta (Some 1), 
    PApp (PRef (Lazy.force coq_sumbool_ref),
	  [| PApp (PRef (Lazy.force coq_eq_ref),
		   [| PMeta (Some 1); PRel 2; PRel 1 |]);
	     PApp (PRef (Lazy.force coq_not_ref), 
		   [|PApp (PRef (Lazy.force coq_eq_ref),
 			   [| PMeta (Some 1); PRel 2; PRel 1 |])|]) |]))))

(* "(A : ?)(x:A)(? A x x)" and "(x : ?)(? x x)" *)
let name_A = Name (id_of_string "A")
let coq_refl_rel1_pattern =
  lazy
    (PProd
       (name_A, PMeta None,
	PProd (x, PRel 1, PApp (PMeta None, [|PRel 2; PRel 1; PRel 1|]))))
let coq_refl_rel2_pattern =
  lazy
    (PProd (x, PMeta None, PApp (PMeta None, [|PRel 1; PRel 1|])))


let build_coq_eq_pattern () = Lazy.force coq_eq_pattern
let build_coq_eqT_pattern () = Lazy.force coq_eqT_pattern
let build_coq_idT_pattern () = Lazy.force coq_idT_pattern
let build_coq_existS_pattern () = Lazy.force coq_existS_pattern
let build_coq_existT_pattern () = Lazy.force coq_existT_pattern
let build_coq_not_pattern () = Lazy.force coq_not_pattern
let build_coq_imp_False_pattern () = Lazy.force coq_imp_False_pattern
let build_coq_eqdec_partial_pattern () = Lazy.force coq_eqdec_partial_pattern
let build_coq_eqdec_pattern () = Lazy.force coq_eqdec_pattern
let build_coq_arrow_pattern () = Lazy.force coq_arrow_pattern
let build_coq_refl_rel1_pattern () = Lazy.force coq_refl_rel1_pattern
let build_coq_refl_rel2_pattern () = Lazy.force coq_refl_rel2_pattern
let build_coq_sig_pattern () = Lazy.force coq_sig_pattern
