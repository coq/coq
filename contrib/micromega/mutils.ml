(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

let debug = false

let fst' (Micromega.Pair(x,y)) = x
let snd' (Micromega.Pair(x,y)) = y

let map_option f x = 
  match x with
    | None -> None
    | Some v -> Some (f v)

let from_option = function
  | None -> failwith "from_option"
  | Some v -> v  

let rec try_any l x = 
 match l with
  | [] -> None
  | (f,s)::l -> match f x with
     | None -> try_any l x
     | x -> x

let iteri f l =
 let rec xiter i l = 
  match l with
   | [] -> ()
   | e::l -> f i e ; xiter (i+1) l in
  xiter 0 l

let mapi f l =
 let rec xmap i l = 
  match l with
   | [] -> []
   | e::l -> (f i e)::xmap (i+1) l in
  xmap 0 l

let rec map3 f l1 l2 l3 = 
  match l1 , l2 ,l3 with
    | [] , [] , [] -> []
    | e1::l1 , e2::l2 , e3::l3 -> (f e1 e2 e3)::(map3 f l1 l2 l3)
    |      _   -> raise (Invalid_argument "map3")


let rec is_sublist l1 l2 = 
  match l1 ,l2 with
    | [] ,_ -> true
    | e::l1', [] -> false
    | e::l1' , e'::l2' -> 
	if e = e' then is_sublist l1' l2'
	else is_sublist l1 l2'
		


let list_try_find f =
  let rec try_find_f = function
    | [] -> failwith "try_find"
    | h::t -> try f h with Failure _ -> try_find_f t
  in
  try_find_f

let rec list_fold_right_elements f l =
  let rec aux = function
    | [] -> invalid_arg "list_fold_right_elements"
    | [x] -> x
    | x::l -> f x (aux l) in
  aux l

let interval n m = 
  let rec interval_n (l,m) =
    if n > m then l else interval_n (m::l,pred m)
  in 
  interval_n ([],m)

open Num
open Big_int

let ppcm x y = 
 let g = gcd_big_int x y in
 let x' = div_big_int x g in
 let y' = div_big_int y g in
  mult_big_int g (mult_big_int x' y')


let denominator = function
 | Int _ | Big_int _ -> unit_big_int
 | Ratio r -> Ratio.denominator_ratio r

let numerator = function
 | Ratio r -> Ratio.numerator_ratio r
 | Int i -> Big_int.big_int_of_int i
 | Big_int i -> i

let rec ppcm_list c l =
 match l with
  | [] -> c
  | e::l -> ppcm_list (ppcm c (denominator e)) l

let rec rec_gcd_list c l  = 
 match l with
  | [] -> c
  | e::l -> rec_gcd_list (gcd_big_int  c (numerator e)) l

let rec gcd_list l = 
 let res = rec_gcd_list zero_big_int l in
  if compare_big_int res zero_big_int = 0 
  then unit_big_int else res
   
   
   
let rats_to_ints l = 
 let c = ppcm_list unit_big_int l in
  List.map (fun x ->  (div_big_int (mult_big_int (numerator x) c) 
			(denominator x))) l
   
(* Nasty reordering of lists - useful to trim certificate down *)
let mapi f l =
 let rec xmapi i l = 
  match l with
   | []   -> []
   | e::l ->  (f e i)::(xmapi (i+1) l) in
  xmapi 0 l


let concatMapi f l = List.rev (mapi (fun e i -> (i,f e)) l)

(* assoc_pos j [a0...an] = [j,a0....an,j+n],j+n+1 *)
let assoc_pos j l = (mapi (fun e i -> e,i+j) l, j + (List.length l))

let assoc_pos_assoc l = 
 let rec xpos i l =
  match l with
   | [] -> []
   | (x,l) ::rst -> let (l',j) = assoc_pos i l in 
		     (x,l')::(xpos j rst) in
  xpos 0 l

let filter_pos f l =
 (* Could sort ... take care of duplicates... *)
 let rec xfilter l =
  match l with
   | []  -> []
   | (x,e)::l -> 
      if List.exists (fun ee -> List.mem ee f) (List.map snd e)
      then (x,e)::(xfilter l)
      else xfilter l in
  xfilter l

let  select_pos lpos l =
 let rec xselect i lpos l =
  match lpos with
   | [] -> []
   | j::rpos -> 
      match l with
       | []   -> failwith "select_pos"
       | e::l -> 
	  if i = j 
	  then e:: (xselect (i+1) rpos l)
	  else xselect (i+1) lpos l in
  xselect 0 lpos l


module CoqToCaml =
struct
 open Micromega

 let rec nat = function
  | O -> 0
  | S n -> (nat n) + 1


 let rec positive p = 
  match p with
   | XH -> 1
   | XI p -> 1+ 2*(positive p)
   | XO p -> 2*(positive p)


 let n nt =
  match nt with
   | N0 -> 0
   | Npos p -> positive p


 let rec index i = (* Swap left-right ? *)
  match i with
   | XH -> 1
   | XI i -> 1+(2*(index i))
   | XO i -> 2*(index i)


 let z x = 
  match x with
   | Z0 -> 0
   | Zpos p -> (positive p)
   | Zneg p -> - (positive p)

 open Big_int

 let rec positive_big_int p =
  match p with
   | XH -> unit_big_int
   | XI p -> add_int_big_int 1 (mult_int_big_int 2 (positive_big_int p))
   | XO p -> (mult_int_big_int 2 (positive_big_int p))


 let z_big_int x = 
  match x with
   | Z0 -> zero_big_int
   | Zpos p -> (positive_big_int p)
   | Zneg p -> minus_big_int (positive_big_int p)


 let num x = Num.Big_int (z_big_int x)

 let rec list elt l =
  match l with
   | Nil -> []
   | Cons(e,l) -> (elt e)::(list elt l)

 let q_to_num {qnum = x ; qden = y} = 
  Big_int (z_big_int x) // (Big_int (z_big_int (Zpos y)))
  
end


module CamlToCoq =
struct
 open Micromega

 let rec nat = function
  | 0 -> O
  | n -> S (nat (n-1))


 let rec positive n =
  if n=1 then XH
  else if n land 1 = 1 then XI (positive (n lsr 1))
  else  XO (positive (n lsr 1))

 let  n nt = 
  if nt < 0 
  then assert false
  else if nt = 0 then N0
  else Npos (positive nt)


   

   
 let rec index  n =
  if n=1 then XH
  else if n land 1 = 1 then XI (index (n lsr 1))
  else  XO (index (n lsr 1))


 let idx n = 
  (*a.k.a path_of_int *)
  (* returns the list of digits of n in reverse order with
     initial 1 removed *)
  let rec digits_of_int n =
   if n=1 then [] 
   else (n mod 2 = 1)::(digits_of_int (n lsr 1))
  in
   List.fold_right 
    (fun b c -> (if b then XI c else XO c))
    (List.rev (digits_of_int n))
    (XH)

    

 let z x = 
  match compare x 0 with
   | 0 -> Z0
   | 1 -> Zpos (positive x)
   | _ -> (* this should be -1 *)
      Zneg (positive (-x)) 

 open Big_int

 let positive_big_int n = 
  let two = big_int_of_int 2 in 
  let rec _pos n = 
   if eq_big_int n unit_big_int then XH
   else
    let (q,m) = quomod_big_int n two  in
     if eq_big_int unit_big_int m 
     then XI (_pos q)
     else XO (_pos q) in
   _pos n

 let bigint x = 
  match sign_big_int x with
   | 0 -> Z0
   | 1 -> Zpos (positive_big_int x)
   | _ -> Zneg (positive_big_int (minus_big_int x))

 let q n = 
  {Micromega.qnum = bigint (numerator n) ; 
   Micromega.qden = positive_big_int (denominator n)}


 let list elt l = List.fold_right (fun x l -> Cons(elt x, l)) l Nil

end

module Cmp =
struct

 let rec compare_lexical l = 
  match l with
   | [] -> 0 (* Equal *)
   | f::l -> 
      let cmp = f () in
       if cmp = 0 	then  compare_lexical l else cmp

 let rec compare_list cmp l1 l2 = 
  match l1 , l2 with
   | []  , [] -> 0
   | []  , _  -> -1
   | _   , [] -> 1
   | e1::l1 , e2::l2 -> 
      let c = cmp e1 e2 in
       if c = 0 then compare_list cmp l1 l2 else c
	
 let hash_list hash l = 
  let rec _hash_list l h =
   match l with
    | []  -> h lxor (Hashtbl.hash [])
    | e::l -> _hash_list l   ((hash e)  lxor h) in

   _hash_list  l 0
end
