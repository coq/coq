(***************************************************************************

(This sentence has been added automatically,
it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


open Format;;

type var_id = int;;

let string_of_var_id x = "V_" ^ (string_of_int x);;
 
let leftify_var var_id = 2*var_id

let rightify_var var_id = 2*var_id +1

module VarOrd =
  struct 
    type t = var_id 
    let compare = (-)
  end

module VarSet = Ordered_sets.Make(VarOrd);;

module VarMap = Inttagmap.Make(struct type t = var_id let tag x = x end);;


let canonical_renaming set_of_vars =
  let (_,res) =
    VarSet.fold 
      (fun v (n,partial_sigma) -> 
	 ((n+1 : var_id), VarMap.add v n partial_sigma))
      set_of_vars (0,VarMap.empty) in
    res

let rec fresh_variables n =
  if n=0
  then []
  else n::(fresh_variables (pred n))
;;


exception Found of int;;

let var_outside_set s =
  let i = ref 0
  in
    while VarSet.mem !i s do incr i done;
    !i
;;
      

let max_index_of_unif_var = ref 0

let init_for_unif s =
  max_index_of_unif_var := 0;
  VarSet.iter 
    (function i -> 
       if !max_index_of_unif_var <= i
       then max_index_of_unif_var := succ i) 
    s
  
let fresh_var_for_unif () = 
  let i = !max_index_of_unif_var in
  let _ = max_index_of_unif_var := succ i in
    i

let print_unif_var x =
  printf "%s" (string_of_var_id x)

exception Syntax_error of string;;

let rec split s =
  try
    let n = String.index s ' '
    in
      if n=0
      then
	split (String.sub s 1 (pred (String.length s)))
      else
	(String.sub s 0 n)
	::(split (String.sub s (n+1) ((String.length s)-n-1)))
  with Not_found -> if s="" then [] else [s]
;;

class type user_variables =
  object
    method string_of_var : var_id -> string 
    method var_of_string : string -> var_id
(*
    method print_all : unit -> unit
*)
  end;;

class from_table t =
  object 

    val var_list = t

    method string_of_var (x : var_id) = 
      if x<Array.length var_list
      then var_list.(x)
      else "V_"^(string_of_int x)

    method var_of_string s =
      try
	for i=0 to pred (Array.length var_list) do
	  if var_list.(i) = s
	  then raise (Found i)
	done;
	raise Not_found
      with 
	  Found x -> (x : var_id)

(*
    method print_all () = 
      for i=0 to pred (Array.length var_list) do
	print_string (var_list.(i)^" ")
      done
*)	      
  end

let from_list l = new from_table (Array.of_list l);;
let from_string s = from_list (split s);;

class default () = 
  object
    method string_of_var (x : var_id) = 
      "V_"^(string_of_int x)

    method var_of_string s =
      try 
	if String.sub s 0 2 <> "V_"
	then raise Not_found
	else int_of_string (String.sub s 2 (String.length s - 2))
      with Failure "int_of_string" | Invalid_argument "String.sub" 
	-> raise Not_found
  end   
;;

let default = new default ()
;;

