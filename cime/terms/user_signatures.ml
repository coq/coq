(***************************************************************************

(This sentence has been added automatically,
it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


open Signatures
open Signature_syntax
open Orderings_generalities

exception Found of int;;

class symbol_entry (n:string) (a:int) (f:symbol_fix) (t:symbol_theory) =
  object
    method name = n 
    method arity = a 
    method fix = f
    method theory = t
  end
;;


let get_fix f t =
  if f=Default
  then if t=Ac then Infix else Prefix
  else f
;;

let sig_of_string s =
  try
    let b = Lexing.from_string s
    in
    let t = Signature_parser.signature Signature_lexer.token b
    in
    let u =
      List.fold_left
	(fun l (ops,ar,f,t) ->
	   l @ (List.map 
		  (fun x -> new symbol_entry x ar (get_fix f t) t)
		  ops))
	[]
	t
    in
    Array.of_list u
  with
      Parsing.Parse_error -> 
	raise (Syntax_error "")
    | Failure "lexing: empty token" -> 
	raise (Syntax_error "invalid character")
    | Signature_lexer.Invalid_char s ->
	raise (Syntax_error ("invalid character '"^s^"'"))
;;

let look_for_ac_symbols table =
  let r = ref false
  in
    for i = 0 to pred (Array.length table) do
      if table.(i)#theory = Ac then r := true
    done;
    !r
;;

let look_for_only_free_symbols table =
  let r = ref true
  in
    for i = 0 to pred (Array.length table) do
      if table.(i)#theory <> Free then r := false
    done;
    !r
;;

type symbol_id = int;;

(*i
let symbol_extend f n i = f*n + i;;
let symbol_mod f n = f mod n;;
let symbol_div f n = f / n;;
i*)

class type user_signature = 
  object
    inherit [symbol_id] Signatures.signature
    method arity : symbol_id -> int
    method is_ac : symbol_id -> bool
    method is_commutative : symbol_id -> bool
    method is_free : symbol_id -> bool
    method contains_ac_symbols : bool      
    method contains_only_free_symbols : bool      
    method string_of_symbol : symbol_id -> string 
    method symbol_of_string : string -> symbol_id
    method symbol_fix : symbol_id -> Signatures.symbol_fix
    method smallest_constant : symbol_id ordering -> symbol_id
  end



class from_table table =
  object

    val symbol_table = (table : symbol_entry array) 
	
    method arity (f : symbol_id) = symbol_table.(f)#arity
				     
    method is_ac (f : symbol_id) = symbol_table.(f)#theory = Ac
							       
    method is_free (f : symbol_id) = symbol_table.(f)#theory = Free
								 
    method is_commutative (f : symbol_id) = 
      symbol_table.(f)#theory = Commutative

    method contains_ac_symbols = look_for_ac_symbols symbol_table
      
    method contains_only_free_symbols = look_for_only_free_symbols symbol_table    
    method string_of_symbol (f : symbol_id) = symbol_table.(f)#name
	
    method symbol_of_string name =
      try
	for i=0 to pred (Array.length symbol_table) do
	  if symbol_table.(i)#name = name
	  then raise (Found i)
	done;
	raise Not_found
      with 
	  Found f -> (f : symbol_id)

    method symbol_fix  (f : symbol_id) = symbol_table.(f)#fix
					   
    method smallest_constant (o : symbol_id ordering) = 
      if (Array.length symbol_table) <= 0
      then raise Not_found
      else 
	let c = ref 0 
	and found = ref false in
	let _ = if (symbol_table.(!c))#arity = 0 then found:= true in
	let _ = 
	  for i = 1 to pred (Array.length symbol_table) do
	      if (symbol_table.(i))#arity = 0
	      then
		begin
		  if !found
		  then
		    match o (!c) i with
			Less_than 
		      | Less_or_equivalent -> c := i
		      | _ -> () 
		  else
		    begin
		      found := true;
		      c := i;
		      end
		end
	  done in
	  if !found then ((!c) : symbol_id) else raise Not_found
  end;;

let from_string descr =
  new from_table (sig_of_string descr)
;;




class dummy_sig =
  object
    method arity (f : symbol_id) = 0
    method is_ac (f : symbol_id) = false
    method is_commutative (f : symbol_id) = false
    method is_free (f : symbol_id) = true
    method contains_ac_symbols = false
    method contains_only_free_symbols = true
    method string_of_symbol (f : symbol_id) = ""
    method symbol_of_string (s : string) = ((raise Not_found) : symbol_id)
    method symbol_fix (f : symbol_id) = Prefix
    method smallest_constant (o : symbol_id Orderings_generalities.ordering) =
      ((raise Not_found) : symbol_id)
  end

let default = new dummy_sig;;

