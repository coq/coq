(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Coqast
open Pcoq
open Pp
open Util
open Names
open Ast
open Extend
open Topconstr
open Libnames
open Bignat

(**********************************************************************)
(* V7 parsing via Grammar *)

let get_z_sign loc =
  let mkid id =
    mkRefC (Qualid (loc,Libnames.make_short_qualid id))
  in
  ((mkid (id_of_string "xI"),
    mkid (id_of_string "xO"),
    mkid (id_of_string "xH")),
   (mkid (id_of_string "ZERO"), 
    mkid (id_of_string "POS"),
    mkid (id_of_string "NEG")))

let pos_of_bignat xI xO xH x =
  let rec pos_of x =
    match div2_with_rest x with
      | (q, true) when is_nonzero q -> mkAppC (xI, [pos_of q])
      | (q, false) -> mkAppC (xO, [pos_of q])
      | (_, true) -> xH
  in 
  pos_of x
    
let z_of_string pos_or_neg s dloc = 
  let ((xI,xO,xH),(aZERO,aPOS,aNEG)) = get_z_sign dloc in
  let v = Bignat.of_string s in
  if is_nonzero v then
    if pos_or_neg then
      mkAppC (aPOS, [pos_of_bignat xI xO xH v])
    else 
      mkAppC (aNEG, [pos_of_bignat xI xO xH v])
  else 
    aZERO

(* Declare the primitive parser with Grammar and without the scope mechanism *)
let zsyntax_create name =
  let e =
    Pcoq.create_constr_entry (Pcoq.get_univ "znatural") name in
  Pcoq.Gram.Unsafe.clear_entry e;
  e

let number = zsyntax_create "number" 

let negnumber = zsyntax_create "negnumber"
 
let _ =
  Gram.extend number None
    [None, None,
     [[Gramext.Stoken ("INT", "")],
      Gramext.action (z_of_string true)]]
    
let _ =
  Gram.extend negnumber None
    [None, None,
     [[Gramext.Stoken ("INT", "")],
      Gramext.action (z_of_string false)]]

(**********************************************************************)
(* Old v7 ast printing *)

open Coqlib

exception Non_closed_number

let get_z_sign_ast loc =
  let ast_of_id id = 
    Termast.ast_of_ref
      (reference_of_constr
	(gen_constant_in_modules "Z-printer" zarith_base_modules id))
  in
  ((ast_of_id "xI",
    ast_of_id "xO",
    ast_of_id "xH"),
   (ast_of_id "ZERO", 
    ast_of_id "POS",
    ast_of_id "NEG"))

let _ = if !Options.v7 then
let rec bignat_of_pos c1 c2 c3 p =
  match p with
    | Node (_,"APPLIST", [b; a]) when alpha_eq(b,c1) ->
        mult_2 (bignat_of_pos c1 c2 c3 a)
    | Node (_,"APPLIST", [b; a]) when alpha_eq(b,c2) ->
        add_1 (mult_2 (bignat_of_pos c1 c2 c3 a))
    | a when alpha_eq(a,c3) -> Bignat.one
    | _ -> raise Non_closed_number
in
let bignat_option_of_pos xI xO xH p =
  try 
    Some (bignat_of_pos xO xI xH p)
  with Non_closed_number -> 
    None
in
let pr_pos a = hov 0 (str "POS" ++ brk (1,1) ++ a) in
let pr_neg a = hov 0 (str "NEG" ++ brk (1,1) ++ a) in

let inside_printer posneg std_pr p =
  let ((xI,xO,xH),_) = get_z_sign_ast dummy_loc in
  match (bignat_option_of_pos xI xO xH p) with
    | Some n -> 
	if posneg then 
	  (str (Bignat.to_string n))
	else 
	  (str "(-" ++ str (Bignat.to_string n) ++ str ")")
    | None -> 
	let pr = if posneg then pr_pos else pr_neg in
	str "(" ++ pr (std_pr (ope("ZEXPR",[p]))) ++ str ")"
in
let outside_zero_printer std_pr p = str "`0`"
in
let outside_printer posneg std_pr p =
  let ((xI,xO,xH),_) = get_z_sign_ast dummy_loc in
  match (bignat_option_of_pos xI xO xH p) with
    | Some n -> 
	if posneg then 
	  (str "`" ++ str (Bignat.to_string n) ++ str "`")
	else 
	  (str "`-" ++ str (Bignat.to_string n) ++ str "`")
      | None -> 
	  let pr = if posneg then pr_pos else pr_neg in
	  str "(" ++ pr (std_pr p) ++ str ")"
in
(* For printing with Syntax and without the scope mechanism *)
let _ = Esyntax.Ppprim.add ("positive_printer", (outside_printer true)) in
let _ = Esyntax.Ppprim.add ("negative_printer", (outside_printer false)) in
let _ = Esyntax.Ppprim.add ("positive_printer_inside", (inside_printer true))in
let _ = Esyntax.Ppprim.add ("negative_printer_inside", (inside_printer false))
in ()

(**********************************************************************)
(* Parsing positive via scopes                                        *)
(**********************************************************************)

open Libnames
open Rawterm
let make_dir l = make_dirpath (List.map id_of_string (List.rev l))
let positive_module = ["Coq";"NArith";"BinPos"]

(* TODO: temporary hack *)
let make_path dir id = Libnames.encode_kn dir id

let positive_path = 
  make_path (make_dir positive_module) (id_of_string "positive")
let glob_positive = IndRef (positive_path,0)
let path_of_xI = ((positive_path,0),1)
let path_of_xO = ((positive_path,0),2)
let path_of_xH = ((positive_path,0),3)
let glob_xI = ConstructRef path_of_xI
let glob_xO = ConstructRef path_of_xO
let glob_xH = ConstructRef path_of_xH

let pos_of_bignat dloc x =
  let ref_xI = RRef (dloc, glob_xI) in
  let ref_xH = RRef (dloc, glob_xH) in
  let ref_xO = RRef (dloc, glob_xO) in
  let rec pos_of x =
    match div2_with_rest x with
      | (q,false) -> RApp (dloc, ref_xO,[pos_of q])
      | (q,true) when is_nonzero q -> RApp (dloc,ref_xI,[pos_of q])
      | (q,true) -> ref_xH
  in 
  pos_of x

let interp_positive dloc = function
  | POS n when is_nonzero n -> pos_of_bignat dloc n
  | _ ->
      user_err_loc (dloc, "interp_positive",
        str "Only strictly positive numbers in type \"positive\"!")

let rec pat_pos_of_bignat dloc x name =
  match div2_with_rest x with
    | (q,false) -> 
        PatCstr (dloc,path_of_xO,[pat_pos_of_bignat dloc q Anonymous],name)
    | (q,true) when is_nonzero q -> 
        PatCstr (dloc,path_of_xI,[pat_pos_of_bignat dloc q Anonymous],name)
    | (q,true) ->
        PatCstr (dloc,path_of_xH,[],name)

let pat_interp_positive dloc = function
  | POS n -> pat_pos_of_bignat dloc n
  | NEG n ->
      user_err_loc (dloc, "interp_positive",
        str "No negative number in type \"positive\"!")

(**********************************************************************)
(* Printing positive via scopes                                       *)
(**********************************************************************)

let rec bignat_of_pos = function
  | RApp (_, RRef (_,b),[a]) when b = glob_xO -> mult_2(bignat_of_pos a)
  | RApp (_, RRef (_,b),[a]) when b = glob_xI -> add_1(mult_2(bignat_of_pos a))
  | RRef (_, a) when a = glob_xH -> Bignat.one
  | _ -> raise Non_closed_number

let uninterp_positive p =
  try 
    Some (POS (bignat_of_pos p))
  with Non_closed_number -> 
    None

(************************************************************************)
(* Declaring interpreters and uninterpreters for positive *)
(************************************************************************)

let _ = Symbols.declare_numeral_interpreter "positive_scope"
  (glob_positive,positive_module)
  (interp_positive,Some pat_interp_positive)
  ([RRef (dummy_loc, glob_xI); 
    RRef (dummy_loc, glob_xO); 
    RRef (dummy_loc, glob_xH)],
   uninterp_positive,
   None)

(**********************************************************************)
(* Parsing N via scopes                                               *)
(**********************************************************************)

let binnat_module = ["Coq";"NArith";"BinNat"]
let n_path = make_path (make_dir binnat_module)
  (id_of_string (if !Options.v7 then "entier" else "N"))
let glob_n = IndRef (n_path,0)
let path_of_N0 = ((n_path,0),1)
let path_of_Npos = ((n_path,0),2)
let glob_N0 = ConstructRef path_of_N0
let glob_Npos = ConstructRef path_of_Npos

let n_of_posint dloc pos_or_neg n = 
  if is_nonzero n then
    RApp(dloc, RRef (dloc,glob_Npos), [pos_of_bignat dloc n])
  else 
    RRef (dloc, glob_N0)

let n_of_int dloc n =
  match n with
  | POS n -> n_of_posint dloc true n 
  | NEG n -> 
      user_err_loc (dloc, "",
        str "No negative number in type N")

let pat_n_of_binnat dloc n name = 
  if is_nonzero n then
    PatCstr (dloc, path_of_Npos, [pat_pos_of_bignat dloc n Anonymous], name)
  else 
    PatCstr (dloc, path_of_N0, [], name)

let pat_n_of_int dloc n name =
  match n with
  | POS n -> pat_n_of_binnat dloc n name
  | NEG n ->
      user_err_loc (dloc, "",
        str "No negative number in type N")

(**********************************************************************)
(* Printing N via scopes                                              *)
(**********************************************************************)

let bignat_of_n = function
  | RApp (_, RRef (_,b),[a]) when b = glob_Npos -> POS (bignat_of_pos a)
  | RRef (_, a) when a = glob_N0 -> POS (Bignat.zero)
  | _ -> raise Non_closed_number

let uninterp_n p =
  try Some (bignat_of_n p)
  with Non_closed_number -> None

(************************************************************************)
(* Declaring interpreters and uninterpreters for N *)

let _ = Symbols.declare_numeral_interpreter "N_scope"
  (glob_n,binnat_module)
  (n_of_int,Some pat_n_of_int)
  ([RRef (dummy_loc, glob_N0); 
    RRef (dummy_loc, glob_Npos)],
  uninterp_n,
  None)
   
(**********************************************************************)
(* Parsing Z via scopes                                               *)
(**********************************************************************)

let fast_integer_module = ["Coq";"ZArith";"BinInt"]
let z_path = make_path (make_dir fast_integer_module) (id_of_string "Z")
let glob_z = IndRef (z_path,0)
let path_of_ZERO = ((z_path,0),1)
let path_of_POS = ((z_path,0),2)
let path_of_NEG = ((z_path,0),3)
let glob_ZERO = ConstructRef path_of_ZERO
let glob_POS = ConstructRef path_of_POS
let glob_NEG = ConstructRef path_of_NEG

let z_of_posint dloc pos_or_neg n = 
  if is_nonzero n then
    let sgn = if pos_or_neg then glob_POS else glob_NEG in
    RApp(dloc, RRef (dloc,sgn), [pos_of_bignat dloc n])
  else 
    RRef (dloc, glob_ZERO)

let z_of_int dloc z =
  match z with
  | POS n -> z_of_posint dloc true n 
  | NEG n -> z_of_posint dloc false n 

let pat_z_of_posint dloc pos_or_neg n name = 
  if is_nonzero n then
    let sgn = if pos_or_neg then path_of_POS else path_of_NEG in
    PatCstr (dloc, sgn, [pat_pos_of_bignat dloc n Anonymous], name)
  else 
    PatCstr (dloc, path_of_ZERO, [], name)

let pat_z_of_int dloc n name =
  match n with
  | POS n -> pat_z_of_posint dloc true n name
  | NEG n -> pat_z_of_posint dloc false n name

(**********************************************************************)
(* Printing Z via scopes                                              *)
(**********************************************************************)

let bigint_of_z = function
  | RApp (_, RRef (_,b),[a]) when b = glob_POS -> POS (bignat_of_pos a)
  | RApp (_, RRef (_,b),[a]) when b = glob_NEG -> NEG (bignat_of_pos a)
  | RRef (_, a) when a = glob_ZERO -> POS (Bignat.zero)
  | _ -> raise Non_closed_number

let uninterp_z p =
  try
    Some (bigint_of_z p)
  with Non_closed_number -> None

(************************************************************************)
(* Declaring interpreters and uninterpreters for Z *)

let _ = Symbols.declare_numeral_interpreter "Z_scope"
  (glob_z,fast_integer_module)
  (z_of_int,Some pat_z_of_int)
  ([RRef (dummy_loc, glob_ZERO); 
    RRef (dummy_loc, glob_POS); 
    RRef (dummy_loc, glob_NEG)],
  uninterp_z,
  None)
   
(************************************************************************)
(* Old V7 ast Printers *)

open Esyntax

let _ = if !Options.v7 then
let bignat_of_pos p =
  let ((xI,xO,xH),_) = get_z_sign_ast dummy_loc in
  let c1 = xO in
  let c2 = xI in
  let c3 = xH in
  let rec transl = function
    | Node (_,"APPLIST",[b; a]) when alpha_eq(b,c1) -> mult_2(transl a)
    | Node (_,"APPLIST",[b; a]) when alpha_eq(b,c2) -> add_1(mult_2(transl a))
    | a when alpha_eq(a,c3) -> Bignat.one
    | _ -> raise Non_closed_number
  in transl p
in
let bignat_option_of_pos p =
  try 
    Some (bignat_of_pos p)
  with Non_closed_number -> 
    None
in
let z_printer posneg p =
  match bignat_option_of_pos p with
    | Some n -> 
	if posneg then 
	  Some (str (Bignat.to_string n))
	else 
	  Some (str "-" ++ str (Bignat.to_string n))
    | None -> None
in
let z_printer_ZERO _ =
  Some (int 0)
in
(* Declare pretty-printers for integers *)
let _ =
  declare_primitive_printer "z_printer_POS" "Z_scope" (z_printer true) in
let _ =
  declare_primitive_printer "z_printer_NEG" "Z_scope" (z_printer false) in
let _ =
  declare_primitive_printer "z_printer_ZERO" "Z_scope" z_printer_ZERO in
()
