(***************************************************************************

  Various basic functions on arrays : body

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

(*

Obsolete header:

  CiME Project - Démons research team - LRI - Université Paris XI

  $Id$

***************************************************************************)

external unsafe_get: 'a array -> int -> 'a = "%array_unsafe_get"

exception Found of int


let index x vect = 
  try
    Array.iteri (fun i vect_i -> if vect_i = x then raise (Found i)) vect;
    raise Not_found
  with Found i -> i

let find p vect = 
  try
    Array.iteri (fun i vect_i -> if (p vect_i) then raise (Found i)) vect;
    raise Not_found
  with Found i -> i
  
let filter p vect =
  Array.fold_left 
    (fun partial_list_of_res vect_i -> 
       if p vect_i 
       then vect_i::partial_list_of_res 
       else partial_list_of_res) 
    [] vect



let fold_lefti f x a =
  let r = ref x in
  for i = 0 to Array.length a - 1 do
    r := f !r i (unsafe_get a i)
  done;
  !r

let fold_righti f a x =
  let r = ref x in
  for i = Array.length a - 1 downto 0 do
    r := f i (unsafe_get a i) !r
  done;
  !r

let filter_indices p vect =
  fold_lefti 
    (fun partial_list_of_res i vect_i -> 
       if p vect_i 
       then i::partial_list_of_res 
       else partial_list_of_res) 
    [] vect
