
(* $Id$ *)

(* This file to allow writing (3) for (S (S (S O))) 
   and still write (S y) for (S y) *)

open Pcoq
open Pp
open Util
open Names
open Coqast
open Ast

exception Non_closed_number

let get_nat_sign loc =
  let ast_of_id id = Astterm.globalize_command (Nvar(loc,id)) in
  (ast_of_id "O", ast_of_id "S", ast_of_id "My_special_variable")
  
(* For example, (nat_of_string "3") is <<(S (S (S O)))>> *)
let nat_of_int n dloc =
  let (astO,astS,_) = get_nat_sign dloc in
  let rec mk_nat n =
    if n <= 0 then 
      astO
    else 
      Node(dloc,"APPLIST", [astS; mk_nat (n-1)])
  in 
  mk_nat n

let nat_of_string s dloc = 
  nat_of_int (int_of_string s) dloc
    
let rec int_of_nat_rec astS astO p =
  match p with
    | Node (_,"APPLIST", [b; a]) when alpha_eq(b,astS) ->
	(int_of_nat_rec astS astO a)+1
    | a when alpha_eq(a,astO) -> 1  
          (***** YES, 1, non 0 ... to print the successor of p *)
    | _ -> raise Non_closed_number
	  
let int_of_nat p =
  let (astO,astS,_) = get_nat_sign dummy_loc in
  try 
    Some (int_of_nat_rec astS astO p)
  with
    Non_closed_number -> None

let replace_S p = 
  let (_,astS,astmyvar) = get_nat_sign dummy_loc in
  let rec aux p =
    match p with
      | Node (l,"APPLIST", [b; a]) when b = astS ->
          Node (l, "APPLIST", [astmyvar; (aux a)])
      | _ -> p
  in 
  ope("APPLIST", [astmyvar; (aux p)])  


(* Declare the primitive printer *)

(* Prints not p, but the SUCCESSOR of p !!!!! *)
let nat_printer std_pr p =
  match (int_of_nat p) with
    | Some i -> [< 'sTR (string_of_int i) >]
    | None -> std_pr (replace_S p)

let _ = Esyntax.Ppprim.add ("nat_printer", nat_printer)

(* Declare the primitive parser *)

let number = 
  match create_entry (get_univ "nat") "number" ETast with
    | Ast n -> n
    | _ -> anomaly "G_natsyntax : create_entry number failed"
 
let _ = 
  Gram.extend number None
    [None, None,
     [[Gramext.Stoken ("INT", "")],
      Gramext.action nat_of_string]]
