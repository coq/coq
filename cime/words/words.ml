(***************************************************************************

This module defines the strings (or words) over a string signature

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)



		 
(*

  This module defines the strings (or words) over a string signature

*)

type 'symbol word = 'symbol list;;

open Format;;

let print s w =
  
  let rec print_end_list l = 
    match l with
	[] -> ()
      | a::l -> 
	  printf "@ %s" (s#string_of_symbol a);
	  print_end_list l

  in
    
    match w with
	[] -> print_string "(epsilon)"
      | a::l ->
	  print_string (s#string_of_symbol a);
	  print_end_list l
;;

let length = List.length ;;


let pretty_print s w =
  
  let print_symb separ symb nb_occ =
    separ ();
    print_string (s#string_of_symbol symb);
    if nb_occ >= 2 then printf "^%d" nb_occ;

  in
  
  let rec print_end_list separ last_symb nb_occ l = 
    match l with
	[] -> print_symb separ last_symb nb_occ 
      | a::l -> 
	  if last_symb = a
	  then print_end_list separ last_symb (succ nb_occ) l 
	  else
	    begin
	      print_symb separ last_symb nb_occ;
	      print_end_list print_space a 1 l
	    end

  in
    
    match w with
	[] -> print_string "(epsilon)"
      | a::l ->
	  open_box 0;
	  print_end_list (fun ()->()) a 1 l;
	  close_box ()

