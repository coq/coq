(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(*i*)
open Pp
(*i*)

(* Arbitrary big natural numbers *)

type bignat = int array

let digits =            8
let base =      100000000 (* let enough room for multiplication by 2 *)
let base_div_2 = 50000000
let base_to_string x = Printf.sprintf "%08d" x

let of_string s =
  let a = Array.create (String.length s / digits + 1) 0 in
  let r = String.length s mod digits in
  if r<>0 then a.(0) <- int_of_string (String.sub s 0 r);
  for i = 1 to String.length s / digits do
    a.(i) <- int_of_string (String.sub s ((i-1)*digits+r) digits)
  done;
  a

let rec to_string s =
  if s = [||] then "0" else
    if s.(0) = 0 then to_string (Array.sub s 1 (Array.length s - 1))
    else 
      String.concat ""
        ((string_of_int (s.(0)))
        ::(List.tl (Array.to_list (Array.map base_to_string s))))
  
let is_nonzero a =
  let b = ref false in Array.iter (fun x -> b := x <> 0 || !b) a; !b

let zero = [|0|]
let one = [|1|]

let is_one a =
  let rec leading_zero i = i<0 || (a.(i) = 0 && leading_zero (i-1)) in
  (a.(Array.length a - 1) = 1) && leading_zero (Array.length a - 2)
      
let div2_with_rest n =
  let len = Array.length n in
  let q = Array.create len 0 in
  for i = 0 to len - 2 do
    q.(i) <- q.(i) + n.(i) / 2; q.(i + 1) <- base_div_2 * (n.(i) mod 2)
  done;
  q.(len - 1) <- q.(len - 1) + n.(len - 1) / 2;
  q, (n.(len - 1) mod 2) = 1

let add_1 n =
  let m = Array.copy n
  and i = ref (Array.length n - 1) in
  while !i >= 0 && m.(!i) = base-1 do
    m.(!i) <- 0; decr i; 
  done;
  if !i < 0 then begin
    m.(0) <- 0; Array.concat [[| 1 |]; m] 
  end else begin
    m.(!i) <- m.(!i) + 1; m
  end

let sub_1 n =
  if is_nonzero n then
    let m = Array.copy n
    and i = ref (Array.length n - 1) in
    while m.(!i) = 0 && !i > 0 do
      m.(!i) <- base-1; decr i;
    done;
    m.(!i) <- m.(!i) - 1;
    m
  else n

let rec mult_2 n =
  let m = Array.copy n in
  m.(Array.length n - 1) <- 2 * m.(Array.length n - 1);
  for i = Array.length n - 2 downto 0 do
    m.(i) <- 2 * m.(i);
    if m.(i + 1) >= base then begin
      m.(i + 1) <- m.(i + 1) - base; m.(i) <- m.(i) + 1 
    end
  done;
  if m.(0) >= base then begin
    m.(0) <- m.(0) - base; Array.concat [[| 1 |]; m] 
  end else 
    m

let less_than m n =
  let lm = ref 0 in
  while !lm < Array.length m && m.(!lm) = 0 do incr lm done;
  let ln = ref 0 in
  while !ln < Array.length n && n.(!ln) = 0 do incr ln done;
  let um = Array.length m - !lm and un = Array.length n - !ln in
  let rec lt d =
    d < um && (m.(!lm+d) < n.(!ln+d) || (m.(!lm+d) = n.(!ln+d) && lt (d+1)))
  in
  (um < un) || (um = un && lt 0)

type bigint = POS of bignat | NEG of bignat

let pr_bigint = function
  | POS n -> str (to_string n)
  | NEG n -> str "-" ++ str (to_string n)

let bigint_to_string = function
  | POS n -> to_string n
  | NEG n -> "-" ^ (to_string n);;
