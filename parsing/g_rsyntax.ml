(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

open Coqast
open Ast
open Pp
open Util
open Names
open Pcoq
open Extend
open Topconstr
open Libnames

(**********************************************************************)
(* Parsing with Grammar                                               *)
(**********************************************************************)

let get_r_sign loc =
  let mkid id =
    mkRefC (Qualid (loc,Libnames.make_short_qualid id))
  in
  ((mkid (id_of_string "R0"),
    mkid (id_of_string "R1"),
    mkid (id_of_string "Rplus"),
    mkid (id_of_string "Rmult"),
    mkid (id_of_string "NRplus"),
    mkid (id_of_string "NRmult")))

let get_r_sign_ast loc =
  let mkid id =
    Termast.ast_of_ref (Nametab.locate (Libnames.make_short_qualid id))
  in
  ((mkid (id_of_string "R0"),
    mkid (id_of_string "R1"),
    mkid (id_of_string "Rplus"), 
    mkid (id_of_string "Rmult"),
    mkid (id_of_string "NRplus"),
    mkid (id_of_string "NRmult")))

let int_decomp n = 
let div2 k = 
let x = k mod 2 in
let y = k - x in (x,y/2) in
let rec list_ch m =
if m< 2 then [m]
else let (x1,x2) = div2 m in x1::(list_ch x2)
in list_ch n

let r_of_int n dloc =
  let (a0,a1,plus,mult,_,_) = get_r_sign dloc in
  let list_ch = int_decomp n in
  let a2 = mkAppC (plus, [a1; a1]) in
  let rec mk_r l =
    match l with
    | [] -> failwith "Error r_of_int"
    | [a] -> if a=1 then a1 else a0
    | a::[b] -> if a==1 then mkAppC (plus, [a1; a2]) else a2
    | a::l' -> if a=1 then mkAppC (plus, [a1; mkAppC (mult, [a2; mk_r l'])]) else mkAppC (mult, [a2; mk_r l'])
  in mk_r list_ch

let r_of_string s dloc = 
  r_of_int (int_of_string s) dloc

let rsyntax_create name =
  let e =
    Pcoq.create_constr_entry (Pcoq.get_univ "rnatural") name in
  Pcoq.Gram.Unsafe.clear_entry e;
  e

let rnumber = rsyntax_create "rnumber"

let _ = 
  Gram.extend rnumber None
    [None, None,
     [[Gramext.Stoken ("INT", "")],
      Gramext.action r_of_string]]

(**********************************************************************)
(* Old ast printing                                                   *)
(**********************************************************************)

exception Non_closed_number

let int_of_r p =
  let (a0,a1,plus,mult,_,_) = get_r_sign_ast dummy_loc in
  let rec int_of_r_rec p = 
    match p with
  | Node (_,"APPLIST", [b;a;c]) when alpha_eq(b,plus) & alpha_eq(a,a1) & alpha_eq(c,a1) -> 2
  | Node (_,"APPLIST", [b;a;c]) when alpha_eq(b,plus) & alpha_eq(a,a1) ->
      (match c with
      |	Node (_,"APPLIST", [e;d;f]) when alpha_eq(e,mult) -> 1 + int_of_r_rec c
      |	Node (_,"APPLIST", [e;d;f]) when alpha_eq(e,plus) & alpha_eq(d,a1) & alpha_eq(f,a1) -> 3
      |	_ -> raise Non_closed_number)
  | Node (_,"APPLIST", [b;a;c]) when alpha_eq(b,mult) ->
      (match a with
      |	Node (_,"APPLIST", [e;d;f]) when alpha_eq(e,plus) & alpha_eq(d,a1) & alpha_eq(f,a1) ->
	  (match c with
	  | g when alpha_eq(g,a1) -> raise Non_closed_number
	  | g when alpha_eq(g,a0) -> raise Non_closed_number
	  | _ -> 2 * int_of_r_rec c)
      |	_ -> raise Non_closed_number)
  | a when alpha_eq(a,a0) -> 0
  | a when alpha_eq(a,a1) -> 1
  | _ -> raise Non_closed_number in
  try 
    Some (int_of_r_rec p)
  with
    Non_closed_number -> None

let replace_plus p = 
  let (_,_,_,_,astnrplus,_) = get_r_sign_ast dummy_loc in
  ope ("REXPR",[ope("APPLIST",[astnrplus;p])])

let replace_mult p = 
  let (_,_,_,_,_,astnrmult) = get_r_sign_ast dummy_loc in
  ope ("REXPR",[ope("APPLIST",[astnrmult;p])])

let rec r_printer_odd std_pr p =
  let (_,a1,plus,_,_,_) = get_r_sign_ast dummy_loc in
  match (int_of_r (ope("APPLIST",[plus;a1;p]))) with
    | Some i -> str (string_of_int i)
    | None -> std_pr (replace_plus p)

let rec r_printer_odd_outside std_pr p =
  let (_,a1,plus,_,_,_) = get_r_sign_ast dummy_loc in
  match (int_of_r (ope("APPLIST",[plus;a1;p]))) with
    | Some i -> str"``" ++ str (string_of_int i) ++ str"``"
    | None -> std_pr (replace_plus p)

let rec r_printer_even std_pr p =
  let (_,a1,plus,mult,_,_) = get_r_sign_ast dummy_loc in
  match (int_of_r (ope("APPLIST",[mult;(ope("APPLIST",[plus;a1;a1]));p]))) with
    | Some i -> str (string_of_int i)
    | None -> std_pr (replace_mult p)

let rec r_printer_even_outside std_pr p =
  let (_,a1,plus,mult,_,_) = get_r_sign_ast dummy_loc in
  match (int_of_r (ope("APPLIST",[mult;(ope("APPLIST",[plus;a1;a1]));p]))) with
    | Some i -> str"``" ++ str (string_of_int i) ++ str"``"
    | None -> std_pr (replace_mult p)

let _ = Esyntax.Ppprim.add ("r_printer_odd", r_printer_odd)
let _ = Esyntax.Ppprim.add ("r_printer_odd_outside", r_printer_odd_outside)
let _ = Esyntax.Ppprim.add ("r_printer_even", r_printer_even)
let _ = Esyntax.Ppprim.add ("r_printer_even_outside", r_printer_even_outside)

(**********************************************************************)
(* Parsing Z via scopes                                               *)
(**********************************************************************)

open Libnames
open Rawterm
open Bignat

let make_dir l = make_dirpath (List.map id_of_string (List.rev l))
let rdefinitions = make_dir ["Coq";"Reals";"Rdefinitions"]

(* TODO: temporary hack *)
let make_path dir id = Libnames.encode_kn dir (id_of_string id)

let glob_R1 = ConstRef (make_path rdefinitions "R1")
let glob_R0 = ConstRef (make_path rdefinitions "R0")
let glob_Ropp = ConstRef (make_path rdefinitions "Ropp")
let glob_Rplus = ConstRef (make_path rdefinitions "Rplus")
let glob_Rmult = ConstRef (make_path rdefinitions "Rmult")

let r_of_posint dloc n =
  let ref_R0 = RRef (dloc, glob_R0) in
  let ref_R1 = RRef (dloc, glob_R1) in
  let ref_Rplus = RRef (dloc, glob_Rplus) in
  let ref_Rmult = RRef (dloc, glob_Rmult) in
  let a2 = RApp(dloc, ref_Rplus, [ref_R1; ref_R1]) in
  let list_ch = int_decomp n in
  let rec mk_r l =
    match l with
    | [] -> failwith "Error r_of_posint"
    | [a] -> if a=1 then ref_R1 else ref_R0
    | a::[b] -> if a==1 then RApp (dloc, ref_Rplus, [ref_R1; a2]) else a2
    | a::l' -> if a=1 then RApp (dloc, ref_Rplus, [ref_R1; RApp (dloc, ref_Rmult, [a2; mk_r l'])]) else RApp (dloc, ref_Rmult, [a2; mk_r l'])
  in mk_r list_ch

(* int_of_string o bigint_to_string : temporary hack ... *)
(* utiliser les bigint de caml ? *)
let r_of_int2 dloc z =
  match z with
  | NEG n -> RApp (dloc, RRef(dloc,glob_Ropp), [r_of_posint dloc (int_of_string (bigint_to_string (POS n)))]) 
  | POS n -> r_of_posint dloc (int_of_string (bigint_to_string z))

(**********************************************************************)
(* Printing R via scopes                                              *)
(**********************************************************************)

let rec bignat_of_r = function
  | RApp (_,RRef (_,p), [RRef (_,o1); RRef (_,o2)]) when p = glob_Rplus & o1 = glob_R1 & o2 = glob_R1 -> add_1 one
  | RApp (_,RRef (_,p), [RRef (_,o); RApp (_,RRef (_,p2),_) as a]) when p = glob_Rplus & o = glob_R1 -> 
      if p2 = glob_Rmult then add_1 (bignat_of_r a)
      else (match a with 
      |	RApp (_,RRef (_,p), [RRef (_,o1); RRef (_,o2)]) when p = glob_Rplus & o1 = glob_R1 & o2 = glob_R1 -> add_1 (add_1 one)
      |	_ -> raise Non_closed_number)
  | RApp (_,RRef (_,p), [RApp (_,RRef (_,o1), [RRef (_,o2); RRef (_,o3)]); RRef (_,q)]) when p = glob_Rmult & o1 = glob_Rplus & o2 = glob_R1 & o3 = glob_R1 & q = glob_R1 -> raise Non_closed_number 
  | RApp (_,RRef (_,p), [RApp (_,RRef (_,o1), [RRef (_,o2); RRef (_,o3)]); a]) when p = glob_Rmult & o1 = glob_Rplus & o2 = glob_R1 & o3 = glob_R1 -> mult_2 (bignat_of_r a) 
  | RRef (_,a) when a = glob_R1 -> one
  | RRef (_,a) when a = glob_R0 -> zero
  | _ -> raise Non_closed_number

let bigint_of_r = function
  | RApp (_,RRef (_,o), [a]) when o = glob_Ropp -> NEG (bignat_of_r a)
  | a -> POS (bignat_of_r a)

let uninterp_r p =
  try
    Some (bigint_of_r p)
  with Non_closed_number ->
    None

let _ = Symbols.declare_numeral_interpreter "R_scope"
  ["Coq";"Reals";"Rsyntax"]
  (r_of_int2,None)
  ([RRef(dummy_loc,glob_Ropp);RRef(dummy_loc,glob_R0);
    RRef(dummy_loc,glob_Rplus);RRef(dummy_loc,glob_Rmult);RRef(dummy_loc,glob_R1)],
    uninterp_r,
    None)

(***********************************************************************)
(* Old ast printers via scope *)

exception Non_closed_number

let bignat_of_pos p =
  let (_,one,plus,_,_,_) = get_r_sign_ast dummy_loc in
  let rec transl = function
    | Node (_,"APPLIST",[p; o; a]) when alpha_eq(p,plus) & alpha_eq(o,one)
        -> add_1(transl a)
    | a when alpha_eq(a,one) -> Bignat.one
    | _ -> raise Non_closed_number
  in transl p
	  
let bignat_option_of_pos p =
  try 
    Some (bignat_of_pos p)
  with Non_closed_number -> 
    None

let r_printer_Rplus1 p =
  match bignat_option_of_pos p with
    | Some n -> Some (str (Bignat.to_string (add_1 n)))
    | None -> None

let r_printer_Ropp p =
  match bignat_option_of_pos p with
    | Some n -> Some (str "-" ++ str (Bignat.to_string n))
    | None -> None

let r_printer_R1 _ =
  Some (int 1)

let r_printer_R0 _ =
  Some (int 0)

(* Declare pretty-printers for integers *)
let _ =
  Esyntax.declare_primitive_printer "r_printer_Ropp" "R_scope" (r_printer_Ropp)
let _ =
  Esyntax.declare_primitive_printer "r_printer_Rplus1" "R_scope" (r_printer_Rplus1)
let _ =
  Esyntax.declare_primitive_printer "r_printer_R1" "R_scope" (r_printer_R1)
let _ =
  Esyntax.declare_primitive_printer "r_printer_R0" "R_scope" r_printer_R0
