(***************************************************************************

This module provides all general notions about orderings

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


type comparison_result = 
  | Equivalent 
  | Greater_than
  | Less_than
  | Greater_or_equivalent
  | Less_or_equivalent
  | Uncomparable
;;

let string_of_comparison_result = function
  | Equivalent	      -> "equivalent"
  | Greater_or_equivalent -> "greater or equivalent"
  | Less_or_equivalent    -> "smaller or equivalent"
  | Greater_than          -> "strictly greater"
  | Less_than             -> "strictly smaller"
  | Uncomparable	      -> "not comparable" ;;

type 'a ordering = 'a -> 'a -> comparison_result;;

module type ORDERED_STRUCTURE =
   sig
     type t
     val cmp: t -> t -> comparison_result
   end


let is_greater_or_equal = function
    Equivalent | Greater_than | Greater_or_equivalent -> true
  | _ -> false;;

let is_less_or_equal = function
    Equivalent | Less_than | Less_or_equivalent -> true
  | _ -> false;;



(*
let produit_ordres = function
    (Equivalent,x) -> x
  | (x,Equivalent) -> x
  | (Greater,Greater) -> Greater
  | (Greater,Greater_or_equivalent) -> Greater
  | (Greater_or_equivalent,Greater) -> Greater
  | (Greater_or_equivalent,Greater_or_equivalent) -> Greater_or_equivalent
  | (Less_than,Less_than) -> Less_than
  | (Less_than,Less_or_equivalent) -> Less_than
  | (Less_or_equivalent,Less_than) -> Less_than
  | (Less_or_equivalent,Less_or_equivalent) -> Less_or_equivalent
  | _ -> Uncomparable;;
*)


let rec lexicographic_extension ordering l1 l2 = 
  match (l1,l2) with
      ([],[])         -> Equivalent
    | (t1::l1,t2::l2) -> 
      	begin
	  match ordering t1 t2 with
              Equivalent -> lexicographic_extension ordering l1 l2
            | Greater_or_equivalent -> 
            	begin
		  match lexicographic_extension ordering l1 l2 with
	              Equivalent -> Greater_or_equivalent
		    | Greater_than -> Greater_than
		    | Greater_or_equivalent -> Greater_or_equivalent
		    | _  -> Uncomparable
	    	end
            | Less_or_equivalent -> 
            	begin
		  match lexicographic_extension ordering l1 l2 with
	              Equivalent -> Less_or_equivalent
		    | Less_than -> Less_than
		    | Less_or_equivalent -> Less_or_equivalent
		    | _  -> Uncomparable
	    	end
            | x -> x
      	end
    | _  -> 
	raise 
	  (Invalid_argument "Orderings_generalities.lexicographic_extension");;



let rec lexicographic_extension_of_orderings orderings_list x y = 
  match orderings_list with
      []    -> Equivalent
    | o::ol -> 
       	match o x y with
            Equivalent -> lexicographic_extension_of_orderings ol x y
          | Greater_or_equivalent -> 
              begin
	    	match lexicographic_extension_of_orderings ol x y with
	            Equivalent -> Greater_or_equivalent
		  | Greater_than -> Greater_than
		  | Greater_or_equivalent -> Greater_or_equivalent
		  | _  -> Uncomparable
	      end
          | Less_or_equivalent -> 
              begin
	    	match lexicographic_extension_of_orderings ol x y with
	            Equivalent -> Less_or_equivalent
		  | Less_than -> Less_than
		  | Less_or_equivalent -> Less_or_equivalent
		  | _  -> Uncomparable
	      end
          | other -> other
;;




let rec greater_than_all order x = function
    []   -> true
  | y::l -> 
      if order x y = Greater_than
      then greater_than_all order x l
      else false;;

(*i
let rec existe_plus_grand_que_tous ordre l1 l2 = 
  match l1 with
      []    -> false
    | x::l1 -> 
	if greater_than_all ordre x l2 
        then true
        else existe_plus_grand_que_tous ordre l1 l2;;
i*)

let rec exists_greater_or_equal order l y = 
  match l with
      []      -> false
    | x::l1 -> 
	match order x y with
            Greater_than 
          | Equivalent
          | Greater_or_equivalent -> true
          | _ -> exists_greater_or_equal order l1 y;;

let rec forall_exists_greater ordre l1 l2 = 
  match l2 with
      []   -> true
    | y::l2 -> 
   	if exists_greater_or_equal ordre l1 y
   	then forall_exists_greater ordre l1 l2
   	else false;;

let rec remove_equivalent_elements ordre l1 l2 = 
  match l1 with
    []   -> ([],l2)
  | x::l1 -> 
      
      let rec supprime_x_si_existe = function
          []   -> raise Not_found
        | y::l -> 
	    if (ordre x y = Equivalent)
            then l
            else y::(supprime_x_si_existe l)
	    
      in 
	try
	  let l2' = (supprime_x_si_existe l2) 
	  in remove_equivalent_elements ordre l1 l2'
        with Not_found ->
	  let (l1',l2') = remove_equivalent_elements ordre l1 l2
	  in (x::l1',l2')


let multiset_extension ordering l1 l2 =
  match remove_equivalent_elements ordering l1 l2 with
      ([],[]) -> Equivalent
    | (l1,l2) -> 
	if forall_exists_greater ordering l1 l2 
        then Greater_than
        else 
	  if forall_exists_greater ordering l2 l1
          then Less_than
          else Uncomparable;;


