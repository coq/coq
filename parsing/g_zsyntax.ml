(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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

open Bignat

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
      
exception Non_closed_number

let get_z_sign_ast loc =
  let ast_of_id id = 
    Termast.ast_of_ref (Nametab.locate (Libnames.make_short_qualid id))
  in
  ((ast_of_id (id_of_string "xI"),
    ast_of_id (id_of_string "xO"),
    ast_of_id (id_of_string "xH")),
   (ast_of_id (id_of_string "ZERO"), 
    ast_of_id (id_of_string "POS"),
    ast_of_id (id_of_string "NEG")))

let rec bignat_of_pos c1 c2 c3 p =
  match p with
    | Node (_,"APPLIST", [b; a]) when alpha_eq(b,c1) ->
        mult_2 (bignat_of_pos c1 c2 c3 a)
    | Node (_,"APPLIST", [b; a]) when alpha_eq(b,c2) ->
        add_1 (mult_2 (bignat_of_pos c1 c2 c3 a))
    | a when alpha_eq(a,c3) -> Bignat.one
    | _ -> raise Non_closed_number
	  
let bignat_option_of_pos xI xO xH p =
  try 
    Some (bignat_of_pos xO xI xH p)
  with Non_closed_number -> 
    None

let pr_pos a = hov 0 (str "POS" ++ brk (1,1) ++ a)
let pr_neg a = hov 0 (str "NEG" ++ brk (1,1) ++ a)

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

let outside_zero_printer std_pr p = str "`0`"

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

(* For printing with Syntax and without the scope mechanism *)
let _ = Esyntax.Ppprim.add ("positive_printer", (outside_printer true))
let _ = Esyntax.Ppprim.add ("negative_printer", (outside_printer false))
let _ = Esyntax.Ppprim.add ("positive_printer_inside", (inside_printer true))
let _ = Esyntax.Ppprim.add ("negative_printer_inside", (inside_printer false))

(* Declare the primitive parser with Grammar and without the scope mechanism *)
open Pcoq

let number = create_constr_entry (get_univ "znatural") "number" 

let negnumber = create_constr_entry (get_univ "znatural") "negnumber"
 
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
(* Parsing via scopes                                                 *)
(**********************************************************************)

open Libnames
open Rawterm
let make_dir l = make_dirpath (List.map id_of_string (List.rev l))
let fast_integer_module = make_dir ["Coq";"ZArith";"fast_integer"]

(* TODO: temporary hack *)
let make_path dir id = Libnames.encode_kn dir id

let z_path = make_path fast_integer_module (id_of_string "Z")
let glob_z = IndRef (z_path,0)
let glob_ZERO = ConstructRef ((z_path,0),1)
let glob_POS = ConstructRef ((z_path,0),2)
let glob_NEG = ConstructRef ((z_path,0),3)

let positive_path = make_path fast_integer_module (id_of_string "positive")
let glob_xI = ConstructRef ((positive_path,0),1)
let glob_xO = ConstructRef ((positive_path,0),2)
let glob_xH = ConstructRef ((positive_path,0),3)

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

let z_of_string2 dloc pos_or_neg n = 
  if is_nonzero n then
    let sgn = if pos_or_neg then glob_POS else glob_NEG in
    RApp(dloc, RRef (dloc,sgn), [pos_of_bignat dloc n])
  else 
    RRef (dloc, glob_ZERO)

let check_required_module loc d =
  let d' = List.map id_of_string d in
  let dir = make_dirpath (List.rev d') in
  if not (Library.library_is_loaded dir) then
    user_err_loc (loc,"z_of_int",
    str ("Cannot interpret numbers in Z without requiring first module "
    ^(list_last d)))

let z_of_int dloc z =
  check_required_module dloc ["Coq";"ZArith";"Zsyntax"];
  match z with
  | POS n -> z_of_string2 dloc true n 
  | NEG n -> z_of_string2 dloc false n 

let _ = Symbols.declare_numeral_interpreter "Z_scope" (z_of_int,None)

(***********************************************************************)
(* Printer for positive *)


(***********************************************************************)
(* Printers *)

exception Non_closed_number

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
	  
let bignat_option_of_pos p =
  try 
    Some (bignat_of_pos p)
  with Non_closed_number -> 
    None

let z_printer posneg p =
  match bignat_option_of_pos p with
    | Some n -> 
	if posneg then 
	  Some (str (Bignat.to_string n))
	else 
	  Some (str "-" ++ str (Bignat.to_string n))
    | None -> None

let z_printer_ZERO _ =
  Some (int 0)

(* Declare pretty-printers for integers *)
open Esyntax
let _ =
  declare_primitive_printer "z_printer_POS" "Z_scope" (z_printer true)
let _ =
  declare_primitive_printer "z_printer_NEG" "Z_scope" (z_printer false)
let _ =
  declare_primitive_printer "z_printer_ZERO" "Z_scope" z_printer_ZERO
