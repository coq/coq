# 1 "compat/numbers_num.ml"



open Num;;

(*

  the type of numbers (integer or rational)

*)

type t = num;;

let biggest_int = 
  let length_of_int = Sys.word_size - 2 in
  let monster_int = 1 lsl length_of_int in
  Int (monster_int - 1);;

let hash n = 
    match n with
      | Int i -> i*65599
      | _ -> let i = int_of_num (floor_num (mod_num n biggest_int)) in i*65599 
;;

(*

  basic constants and conversion from machine ints

*)

let zero = num_of_int 0;;
let one = num_of_int 1;;
let two = num_of_int 2;;
let minus_one = num_of_int (-1);;
let of_int = num_of_int;;
let to_int n =
  try 
    int_of_num n
  with
      Failure _ -> invalid_arg "Numbers.to_int";;
(*

 basic operations overs rational numbers

*)

let is_zero = eq_num zero;;
let denominator = function
  Ratio r -> 
    let t = Ratio.normalize_ratio r in
    num_of_big_int (Ratio.denominator_ratio t)
| n -> one

let add = add_num;;
let sub = sub_num;;
let minus = minus_num;;
let abs = abs_num;;
let mult = mult_num;;
let div = div_num;;

let rec power_int x = function
    0 -> one
  | 1 -> x
  | n ->
      let y = square_num (power_int x (n/2))
      in
      	if (n mod 2)=0
      	then y
	else mult_num y x
;;

(*

  comparators

*)

let compare = compare_num;;
let eq = eq_num;;
let neq x y = not(eq_num x y);;
let ge = ge_num;;
let gt = gt_num;;
let le = le_num;;
let lt = lt_num;;
let max = max_num;;
let min = min_num;;

(*

integer operations

*)

let succ = succ_num;;
let pred = pred_num;;

let quo = quo_num;;
let modulo = mod_num;;

let rec pgcd n m =
  if eq_num m zero then n
  else pgcd m (mod_num n m);;

let ppcm n m = div_num (mult_num n m) (pgcd n m);;


let rec full_pgcd n m =
  if eq_num m zero  
  then (n,one,zero)
  else 
    let q = quo_num n m and r = mod_num n m in
    let (d,k1,k2) = full_pgcd m r in
    (* 
       here we have m = k1 * d  and r = k2 * d so
       n = q * m + r = q * k1 * d + k2 * d
    *)
    (d,add_num (mult_num q k1) k2,k1)
    

let div_floor x y = 
  floor_num (div_num x y);;

let div_ceil x y = 
  ceiling_num (div_num x y);;

(*
let sqrt_floor x =

  let rec approx y =
    let dy = 
      quo_num 
      	(sub_num (square_num y) x) 
      	(mult_num num_two y)
    in
    let new_y = sub_num y dy
    in
(*      if le_num (abs_num dy) num_zero then new_y else approx new_y *)
      if ge_num new_y y
      then y
      else approx new_y

  in 
  if le_num x num_one
  then x
  else pred_num (approx x)
;;
*)

(**)
let sqrt_floor x =

  let rec approx y =
    let new_y = 
      quo_num 
      	(add_num (square_num y) x) 
      	(mult_num two y)
    in
      if ge_num new_y y
      then y
      else approx new_y

  in 
  if le_num x one
  then x
  else approx x
;;

(**)

(*
let sqrt_floor_int x =

  let rec approx y =
    let new_y = (y*y+x)/(y+y)
    in
      if new_y >= y
      then y
      else approx new_y

  in 

  match x with
    0 -> 0
  | 1 -> 1
  | 2 -> 1
  | 3 -> 1
  | 4 -> 2
  | 5 -> 2
  | 6 -> 2
  | 7 -> 2
  | 8 -> 2
  | 9 -> 3
  | 10 -> 3
  | 11 -> 3
  | 12 -> 3
  | 13 -> 3
  | 14 -> 3
  | 15 -> 3
  | 16 -> 4
  | x -> approx x
;;

let sqrt_floor_big_int x =

  let rec approx y =
    let new_y = 
      quo_num 
      	(add_num (square_num y) x) 
      	(mult_num num_two y)
    in
      if ge_num new_y y
      then y
      else approx new_y

  in 
  approx x
;;

let sqrt_floor = function
    Int x -> Int (sqrt_floor_int x)
  | x -> sqrt_floor_big_int x
;;
*)

(*
for i=0  to 37 do 
  Printf.printf "i=%d r=%s\n" i (string_of_num (sqrt_floor (Int i))) 
done;;
*)

(*
let sqrt_ceil x =

  let rec approx y =
  let dy = 
    quo_num 
      (succ_num (sub_num (square_num y) x))
      (mult_num num_two y)
  in
  let new_y = sub_num y dy
  in
(* if le_num (abs_num dy) num_zero then new_y else approx new_y *)
    if ge_num new_y y
    then y
    else approx new_y

  in 
  if le_num x num_one
  then x
  else (approx x)
;;
*)

let sqrt_ceil x =
  succ_num (sqrt_floor (pred_num x))
;;


(*
for i=0  to 37 do 
  Printf.printf "i=%d r=%s\n" i (string_of_num (sqrt_ceil (Int i))) 
done;;
*)



let root_floor n x =

  if le_num x one
  then x
  else
    let predn = Pervasives.pred n
    in
    let numpredn = Int predn
    and numn = Int n
    in
    let rec approx y =
      let ypnm1 = (power_int y predn)
      in      
      let new_y = 
      	quo_num 
      	  (add_num (mult_num numpredn (mult_num y ypnm1)) x) 
	  (mult_num numn ypnm1)
      in
      	if ge_num new_y y
      	then y
      	else approx new_y
    in 
      approx x
;;

(*
for i=0  to 37 do 
  Printf.printf "i=%d r=%s\n" i (string_of_num (root_floor 2 (Int i))) 
done;;
for i=0  to 37 do 
  Printf.printf "i=%d r=%s\n" i (string_of_num (root_floor 3 (Int i))) 
done;;
for i=0  to 37 do 
  Printf.printf "i=%d r=%s\n" i (string_of_num (root_floor 4 (Int i))) 
done;;
*)


let root_ceil n x =
  succ_num (root_floor n (pred_num x))
;;

(*
for i=0  to 37 do 
  Printf.printf "i=%d r=%s\n" i (string_of_num (root_ceil 3 (Int i))) 
done;;
for i=0  to 37 do 
  Printf.printf "i=%d r=%s\n" i (string_of_num (root_ceil 4 (Int i))) 
done;;
*)


(*

  parsing and printing

*)

let from_string = num_of_string;;
let to_string = string_of_num;;
