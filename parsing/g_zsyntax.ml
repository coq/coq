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

let get_z_sign loc =
  let ast_of_id id = Astterm.globalize_constr (Nvar(loc,id)) in
  ((ast_of_id (id_of_string "xI"),
    ast_of_id (id_of_string "xO"),
    ast_of_id (id_of_string "xH")),
   (ast_of_id (id_of_string "ZERO"), 
    ast_of_id (id_of_string "POS"),
    ast_of_id (id_of_string "NEG")))

let int_array_of_string s =
  let a = Array.create (String.length s) 0 in
  for i = 0 to String.length s - 1 do
    a.(i) <- int_of_string (String.sub s i 1)
  done;
  a
    
let string_of_int_array s =
  String.concat "" (Array.to_list (Array.map string_of_int s))
    
let is_nonzero a =
  let b = ref false in Array.iter (fun x -> b := x <> 0 || !b) a; !b
      
let div2_with_rest n =
  let len = Array.length n in
  let q = Array.create len 0 in
  for i = 0 to len - 2 do
    q.(i) <- q.(i) + n.(i) / 2; q.(i + 1) <- 5 * (n.(i) mod 2)
  done;
  q.(len - 1) <- q.(len - 1) + n.(len - 1) / 2;
  q, n.(len - 1) mod 2

let add_1 n =
  let m = Array.copy n
  and i = ref (Array.length n - 1) in
  m.(!i) <- m.(!i) + 1;
  while m.(!i) = 10 && !i > 0 do
    m.(!i) <- 0; decr i; m.(!i) <- m.(!i) + 1
  done;
  if !i = 0 && m.(0) = 10 then begin 
    m.(0) <- 0; Array.concat [[| 1 |]; m] 
  end else 
    m

let rec mult_2 n =
  let m = Array.copy n in
  m.(Array.length n - 1) <- 2 * m.(Array.length n - 1);
  for i = Array.length n - 2 downto 0 do
    m.(i) <- 2 * m.(i);
    if m.(i + 1) >= 10 then begin
      m.(i + 1) <- m.(i + 1) - 10; m.(i) <- m.(i) + 1 
    end
  done;
  if m.(0) >= 10 then begin 
    m.(0) <- m.(0) - 10; Array.concat [[| 1 |]; m] 
  end else 
    m

let pos_of_int_array astxI astxO astxH x =
  let rec pos_of x =
    match div2_with_rest x with
      | (q, 1) ->
          if is_nonzero q then ope("APPLIST", [astxI; pos_of q]) else astxH
      | (q, 0) -> ope("APPLIST", [astxO; pos_of q])
      | _ -> anomaly "n mod 2 is neither 1 nor 0. Do you bielive that ?"
  in 
  pos_of x
    
let z_of_string pos_or_neg s dloc = 
  let ((astxI,astxO,astxH),(astZERO,astPOS,astNEG)) = get_z_sign dloc in
  let v = int_array_of_string s in
  if is_nonzero v then
    if pos_or_neg then
      ope("APPLIST",[astPOS; pos_of_int_array astxI astxO astxH v])
    else 
      ope("APPLIST",[astNEG; pos_of_int_array astxI astxO astxH v])
  else 
    astZERO
      
exception Non_closed_number

let rec int_array_of_pos c1 c2 c3 p =
  match p with
    | Node (_,"APPLIST", [b; a]) when alpha_eq(b,c1) ->
        mult_2 (int_array_of_pos c1 c2 c3 a)
    | Node (_,"APPLIST", [b; a]) when alpha_eq(b,c2) ->
        add_1 (mult_2 (int_array_of_pos c1 c2 c3 a))
    | a when alpha_eq(a,c3) -> [| 1 |]
    | _ -> raise Non_closed_number
	  
let int_array_option_of_pos astxI astxO astxH p =
  try 
    Some (int_array_of_pos astxO astxI astxH p)
  with Non_closed_number -> 
    None

let pr_pos a = hov 0 (str "POS" ++ brk (1,1) ++ a)
let pr_neg a = hov 0 (str "NEG" ++ brk (1,1) ++ a)

let inside_printer posneg std_pr p =
  let ((astxI,astxO,astxH),_) = get_z_sign dummy_loc in
  match (int_array_option_of_pos astxI astxO astxH p) with
    | Some n -> 
	if posneg then 
	  (str (string_of_int_array n))
	else 
	  (str "(-" ++ str (string_of_int_array n) ++ str ")")
    | None -> 
	let pr = if posneg then pr_pos else pr_neg in
	str "(" ++ pr (std_pr (ope("ZEXPR",[p]))) ++ str ")"

let outside_printer posneg std_pr p =
  let ((astxI,astxO,astxH),_) = get_z_sign dummy_loc in
  match (int_array_option_of_pos astxI astxO astxH p) with
    | Some n -> 
	if posneg then 
	  (str "`" ++ str (string_of_int_array n) ++ str "`")
	else 
	  (str "`-" ++ str (string_of_int_array n) ++ str "`")
      | None -> 
	  let pr = if posneg then pr_pos else pr_neg in
	  str "(" ++ pr (std_pr p) ++ str ")"

(* Declare pretty-printers for integers *)
let _ = Esyntax.Ppprim.add ("positive_printer", (outside_printer true))
let _ = Esyntax.Ppprim.add ("negative_printer", (outside_printer false))
let _ = Esyntax.Ppprim.add ("positive_printer_inside", (inside_printer true))
let _ = Esyntax.Ppprim.add ("negative_printer_inside", (inside_printer false))

(* Declare the primitive parser *)
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

