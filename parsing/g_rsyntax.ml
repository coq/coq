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

let get_r_sign loc =
  let mkid id =
    mkRefC (Qualid (loc,Libnames.make_short_qualid id))
  in
  ((mkid (id_of_string "R0"),
    mkid (id_of_string "R1"),
    mkid (id_of_string "Rplus"), 
    mkid (id_of_string "NRplus")))

let get_r_sign_ast loc =
  let mkid id =
    Termast.ast_of_ref (Nametab.locate (Libnames.make_short_qualid id))
  in
  ((mkid (id_of_string "R0"),
    mkid (id_of_string "R1"),
    mkid (id_of_string "Rplus"), 
    mkid (id_of_string "NRplus")))

(* Parsing via Grammar *)
let r_of_int n dloc =
  let (a0,a1,plus,_) = get_r_sign dloc in
  let rec mk_r n =
    if n <= 0 then
      a0
    else if n = 1 then 
      a1
    else
      mkAppC (plus, [a1; mk_r (n-1)])
  in 
  mk_r n

let r_of_string s dloc = 
  r_of_int (int_of_string s) dloc

let rnumber = create_constr_entry (get_univ "rnatural") "rnumber"

let _ = 
  Gram.extend rnumber None
    [None, None,
     [[Gramext.Stoken ("INT", "")],
      Gramext.action r_of_string]]

(** pp **)

exception Non_closed_number

let rec int_of_r_rec a1 plus p =
  match p with
    | Node (_,"APPLIST", [b; a; c]) when alpha_eq(b,plus) && 
                                         alpha_eq(a,a1) ->
        (int_of_r_rec a1 plus c)+1
    | a when alpha_eq(a,a1) -> 1  
    | _ -> raise Non_closed_number
          
let int_of_r p =
  let (_,a1,plus,_) = get_r_sign_ast dummy_loc in
  try 
    Some (int_of_r_rec a1 plus p)
  with
    Non_closed_number -> None

let replace_plus p = 
  let (_,a1,_,astnr) = get_r_sign_ast dummy_loc in
     ope ("REXPR",[ope("APPLIST", [astnr; a1; p])]) 

let r_printer std_pr p =
  let (_,a1,plus,_) = get_r_sign dummy_loc in
  match (int_of_r p) with
    | Some i -> str (string_of_int (i+1))
    | None -> std_pr (replace_plus p)

let r_printer_outside std_pr p =
  let (_,a1,plus,_) = get_r_sign dummy_loc in
  match (int_of_r p) with
    | Some i -> str "``" ++ str (string_of_int (i+1)) ++ str "``"
    | None -> std_pr (replace_plus p)

let _ = Esyntax.Ppprim.add ("r_printer", r_printer)
let _ = Esyntax.Ppprim.add ("r_printer_outside", r_printer_outside)

(**********************************************************************)
(* Parsing via scopes                                                 *)
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

let r_of_posint dloc n =
  if is_nonzero n then begin
    if Options.is_verbose () & less_than (of_string "5000") n then begin
	warning ("You may experiment stack overflow and segmentation fault\
                  \nwhile parsing numbers in R the absolute value of which is\
                  \ngreater than 5000");
	flush_all ()
      end;
    let ref_R1 = RRef (dloc, glob_R1) in
    let ref_Rplus = RRef (dloc, glob_Rplus) in
    let rec r_of_strictly_pos n =
      if is_one n then
        ref_R1
      else
        RApp(dloc, ref_Rplus, [ref_R1; r_of_strictly_pos (sub_1 n)])
    in r_of_strictly_pos n
  end
  else
    RRef (dloc, glob_R0)

let check_required_module loc d =
  let d' = List.map id_of_string d in
  let dir = make_dirpath (List.rev d') in
  if not (Library.library_is_loaded dir) then
    user_err_loc (loc,"z_of_int",
    str ("Cannot interpret numbers in Z without requiring first module "
    ^(list_last d)))

let r_of_int dloc z =
  check_required_module dloc ["Coq";"Reals";"Rsyntax"];
  match z with
  | NEG n -> RApp (dloc, RRef(dloc,glob_Ropp), [r_of_posint dloc n]) 
  | POS n -> r_of_posint dloc n 

let _ = Symbols.declare_numeral_interpreter "R_scope" (r_of_int,None)

(***********************************************************************)
(* Printers *)

exception Non_closed_number

let bignat_of_pos p =
  let (_,one,plus,_) = get_r_sign_ast dummy_loc in
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
