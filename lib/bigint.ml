(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(*i*)
open Pp
(*i*)

(***************************************************)
(* Basic operations on (unbounded) integer numbers *)
(***************************************************)

(* An integer is canonically represented as an array of k-digits blocs.

   0 is represented by the empty array and -1 by the singleton [|-1|].
   The first bloc is in the range ]0;10^k[ for positive numbers.
   The first bloc is in the range ]-10^k;-1[ for negative ones.
   All other blocs are numbers in the range [0;10^k[.

   Negative numbers are represented using 2's complementation. For instance,
   with 4-digits blocs, [-9655;6789] denotes -96543211
*)

(* The base is a power of 10 in order to facilitate the parsing and printing
   of numbers in digital notation.

   All functions, to the exception of to_string and of_string should work
   with an arbitrary base, even if not a power of 10.

   In practice, we set k=4 so that no overflow in ocaml machine words
   (i.e. the interval [-2^30;2^30-1]) occur when multiplying two
   numbers less than (10^k)
*)

(* The main parameters *)

let size =
  let rec log10 n = if n < 10 then 0 else 1 + log10 (n / 10) in
  (log10 max_int) / 2

let format_size =
  (* How to parametrize a printf format *)
  if size = 4 then Printf.sprintf "%04d"
  else fun n ->
    let rec aux j l n =
      if j=size then l else aux (j+1) (string_of_int (n mod 10) :: l) (n/10)
    in String.concat "" (aux 0 [] n)

(* The base is 10^size *)
let base =
  let rec exp10 = function 0 -> 1 | n -> 10 * exp10 (n-1) in exp10 size

(* Basic numbers *)
let zero = [||]
let neg_one = [|-1|]

(* Sign of an integer *)
let is_strictly_neg n = n<>[||] && n.(0) < 0
let is_strictly_pos n = n<>[||] && n.(0) > 0
let is_neg_or_zero n = n=[||] or n.(0) < 0
let is_pos_or_zero n = n=[||] or n.(0) > 0

let normalize_pos n =
  let k = ref 0 in
  while !k < Array.length n & n.(!k) = 0 do incr k done;
  Array.sub n !k (Array.length n - !k)

let normalize_neg n =
  let k = ref 1 in
  while !k < Array.length n & n.(!k) = base - 1 do incr k done;
  let n' = Array.sub n !k (Array.length n - !k) in
  if Array.length n' = 0 then [|-1|] else (n'.(0) <- n'.(0) - base; n')

let rec normalize n =
  if Array.length n = 0 then n else
    if n.(0) = -1 then normalize_neg n else normalize_pos n

let neg m =
  if m = zero then zero else
  let n = Array.copy m in
  let i = ref (Array.length m - 1) in
  while !i > 0 & n.(!i) = 0 do decr i done;
  if !i > 0 then begin
    n.(!i) <- base - n.(!i); decr i;
    while !i > 0 do n.(!i) <- base - 1 - n.(!i); decr i done;
    n.(0) <- - n.(0) - 1;
    if n.(0) < -1 then (n.(0) <- n.(0) + base; Array.append [| -1 |] n) else
    if n.(0) = - base then (n.(0) <- 0; Array.append [| -1 |] n)
    else normalize n
  end else (n.(0) <- - n.(0); n)

let push_carry r j =
  let j = ref j in
  while !j > 0 & r.(!j) < 0 do
    r.(!j) <- r.(!j) + base; decr j; r.(!j) <- r.(!j) - 1
  done;
  while !j > 0 & r.(!j) >= base do
    r.(!j) <- r.(!j) - base; decr j; r.(!j) <- r.(!j) + 1
  done;
  if r.(0) >= base then (r.(0) <- r.(0) - base; Array.append [| 1 |] r)
  else if r.(0) < -base then (r.(0) <- r.(0) + 2*base; Array.append [| -2 |] r)
  else if r.(0) = -base then (r.(0) <- 0; Array.append [| -1 |] r)
  else normalize r

let add_to r a j =
  if a = zero then r else begin
  for i = Array.length r - 1 downto j+1 do
    r.(i) <- r.(i) + a.(i-j);
    if r.(i) >= base then (r.(i) <- r.(i) - base; r.(i-1) <- r.(i-1) + 1)
  done;
  r.(j) <- r.(j) + a.(0);
  push_carry r j
  end

let add n m =
  let d = Array.length n - Array.length m in
  if d > 0 then add_to (Array.copy n) m d else add_to (Array.copy m) n (-d)

let sub_to r a j =
  if a = zero then r else begin
  for i = Array.length r - 1 downto j+1 do
    r.(i) <- r.(i) - a.(i-j);
    if r.(i) < 0 then (r.(i) <- r.(i) + base; r.(i-1) <- r.(i-1) - 1)
  done;
  r.(j) <- r.(j) - a.(0);
  push_carry r j
  end

let sub n m =
  let d = Array.length n - Array.length m in
  if d >= 0 then sub_to (Array.copy n) m d
  else let r = neg m in add_to r n (Array.length r - Array.length n)

let rec mult m n =
  if m = zero or n = zero then zero else
  let l = Array.length m + Array.length n in
  let r = Array.create l 0 in
  for i = Array.length m - 1 downto 0 do
    for j = Array.length n - 1 downto 0 do
      let p = m.(i) * n.(j) + r.(i+j+1) in
      let (q,s) =
        if p < 0
        then (p + 1) / base - 1, (p + 1) mod base + base - 1
        else p / base, p mod base in
      r.(i+j+1) <- s;
      if q <> 0 then r.(i+j) <- r.(i+j) + q;
    done
  done;
  normalize r

let rec less_than_same_size m n i j =
  i < Array.length m &&
  (m.(i) < n.(j) or (m.(i) = n.(j) && less_than_same_size m n (i+1) (j+1)))

let less_than m n =
  if is_strictly_neg m then
    is_pos_or_zero n or Array.length m > Array.length n
      or (Array.length m = Array.length n && less_than_same_size m n 0 0)
  else
    is_strictly_pos n && (Array.length m < Array.length n or
    (Array.length m = Array.length n && less_than_same_size m n 0 0))

let equal m n = (m = n)

let less_than_shift_pos k m n =
  (Array.length m - k < Array.length n)
  or (Array.length m - k = Array.length n && less_than_same_size m n k 0)

let rec can_divide k m d i =
  (i = Array.length d) or
  (m.(k+i) > d.(i)) or
  (m.(k+i) = d.(i) && can_divide k m d (i+1))

(* computes m - d * q * base^(|m|-k) in-place on positive numbers *)
let sub_mult m d q k =
  if q <> 0 then
  for i = Array.length d - 1 downto 0 do
    let v = d.(i) * q in
    m.(k+i) <- m.(k+i) - v mod base;
    if m.(k+i) < 0 then (m.(k+i) <- m.(k+i) + base; m.(k+i-1) <- m.(k+i-1) -1);
    if v >= base then m.(k+i-1) <- m.(k+i-1) - v / base;
  done

let euclid m d =
  let isnegm, m =
    if is_strictly_neg m then (-1),neg m else 1,Array.copy m in
  let isnegd, d = if is_strictly_neg d then (-1),neg d else 1,d in
  if d = zero then raise Division_by_zero;
  let q,r =
    if less_than m d then (zero,m) else
    let ql = Array.length m - Array.length d in
    let q = Array.create (ql+1) 0 in
    let i = ref 0 in
    while not (less_than_shift_pos !i m d) do
      if m.(!i)=0 then incr i else
      if can_divide !i m d 0 then begin
        let v =
          if Array.length d > 1 && d.(0) <> m.(!i) then
            (m.(!i) * base + m.(!i+1)) / (d.(0) * base + d.(1) + 1)
          else
            m.(!i) / d.(0) in
        q.(!i) <- q.(!i) + v;
	sub_mult m d v !i
      end else begin
        let v = (m.(!i) * base + m.(!i+1)) / (d.(0) + 1) in
        q.(!i) <- q.(!i) + v / base;
	sub_mult m d (v / base) !i;
        q.(!i+1) <- q.(!i+1) + v mod base;
	if q.(!i+1) >= base then
	  (q.(!i+1) <- q.(!i+1)-base; q.(!i) <- q.(!i)+1);
	sub_mult m d (v mod base) (!i+1)
      end
    done;
    (normalize q, normalize m) in
  (if isnegd * isnegm = -1 then neg q else q),
  (if isnegm = -1 then neg r else r)

(* Parsing/printing ordinary 10-based numbers *)

let of_string s =
  let isneg = String.length s > 1 & s.[0] = '-' in
  let n = if isneg then 1 else 0 in
  let d = ref n in
  while !d < String.length s && s.[!d] = '0' do incr d done;
  if !d = String.length s then zero else
  let r = (String.length s - !d) mod size in
  let h = String.sub s (!d) r in
  if !d = String.length s - 1 && isneg && h="1" then neg_one else
  let e = if h<>"" then 1 else 0 in
  let l = (String.length s - !d) / size in
  let a = Array.create (l + e + n) 0 in
  if isneg then begin
    a.(0) <- (-1);
    let carry = ref 0 in
    for i=l downto 1 do
      let v = int_of_string (String.sub s ((i-1)*size + !d +r) size)+ !carry in
      if v <> 0 then (a.(i+e)<- base - v; carry := 1) else carry := 0
    done;
    if e=1 then a.(1) <- base - !carry - int_of_string h;
  end
  else begin
    if e=1 then a.(0) <- int_of_string h;
    for i=1 to l do
      a.(i+e-1) <- int_of_string (String.sub s ((i-1)*size + !d + r) size)
    done
  end;
  a

let to_string_pos sgn n =
   if Array.length n = 0 then "0" else
     sgn ^
     String.concat ""
      (string_of_int n.(0) :: List.map format_size (List.tl (Array.to_list n)))

let to_string n =
  if is_strictly_neg n then to_string_pos "-" (neg n)
  else to_string_pos "" n

(******************************************************************)
(* Optimized operations on (unbounded) integer numbers            *)
(* integers smaller than base are represented as machine integers *)
(******************************************************************)

type bigint = Obj.t

let ints_of_int n =
  if n >= base then [| n / base; n mod base |]
  else if n <= - base then [| n / base - 1; n mod base + base |]
  else if n = 0 then [| |] else [| n |]

let big_of_int n =
  if n >= base then Obj.repr [| n / base; n mod base |]
  else if n <= - base then Obj.repr [| n / base - 1; n mod base + base |]
  else Obj.repr n

let big_of_ints n =
  let n = normalize n in
  if n = zero then Obj.repr 0 else
  if Array.length n = 1 then Obj.repr n.(0) else
  Obj.repr n

let coerce_to_int = (Obj.magic : Obj.t -> int)
let coerce_to_ints = (Obj.magic : Obj.t -> int array)

let ints_of_z n =
  if Obj.is_int n then ints_of_int (coerce_to_int n)
  else coerce_to_ints n

let app_pair f (m, n) =
  (f m, f n)

let add m n =
  if Obj.is_int m & Obj.is_int n
  then big_of_int (coerce_to_int m + coerce_to_int n)
  else big_of_ints (add (ints_of_z m) (ints_of_z n))

let sub m n =
  if Obj.is_int m & Obj.is_int n
  then big_of_int (coerce_to_int m - coerce_to_int n)
  else big_of_ints (sub (ints_of_z m) (ints_of_z n))

let mult m n =
  if Obj.is_int m & Obj.is_int n
  then big_of_int (coerce_to_int m * coerce_to_int n)
  else big_of_ints (mult (ints_of_z m) (ints_of_z n))

let euclid m n =
  if Obj.is_int m & Obj.is_int n
  then app_pair big_of_int
    (coerce_to_int m / coerce_to_int n, coerce_to_int m mod coerce_to_int n)
  else app_pair big_of_ints (euclid (ints_of_z m) (ints_of_z n))

let less_than m n =
  if Obj.is_int m & Obj.is_int n
  then coerce_to_int m < coerce_to_int n
  else less_than (ints_of_z m) (ints_of_z n)

let neg n =
  if Obj.is_int n then big_of_int (- (coerce_to_int n))
  else big_of_ints (neg (ints_of_z n))

let of_string m = big_of_ints (of_string m)
let to_string m = to_string (ints_of_z m)

let zero = big_of_int 0
let one = big_of_int 1
let sub_1 n = sub n one
let add_1 n = add n one
let two = big_of_int 2
let mult_2 n = add n n

let div2_with_rest n =
  let (q,b) = euclid n two in
  (q, b = one)

let is_strictly_neg n = is_strictly_neg (ints_of_z n)
let is_strictly_pos n = is_strictly_pos (ints_of_z n)
let is_neg_or_zero n = is_neg_or_zero (ints_of_z n)
let is_pos_or_zero n = is_pos_or_zero (ints_of_z n)

let pr_bigint n = str (to_string n)

(* spiwack: computes n^m *)
(* The basic idea of the algorithm is that n^(2m) = (n^2)^m *)
(* In practice the algorithm performs :
    k*n^0 = k
    k*n^(2m) = k*(n*n)^m
    k*n^(2m+1) = (n*k)*(n*n)^m *)
let pow  =
  let rec pow_aux odd_rest n m = (* odd_rest is the k from above *)
    if is_neg_or_zero m then
      odd_rest
    else
      let (quo,rem) = div2_with_rest m in
      pow_aux
	((* [if m mod 2 = 1]*)
         if rem then
          mult n odd_rest
	 else
          odd_rest )
	(* quo = [m/2] *)
	(mult n n) quo
  in
  pow_aux one

(* Testing suite *)

let check () =
  let numbers = [
  "1";"2";"99";"100";"101";"9999";"10000";"10001";
  "999999";"1000000";"1000001";"99999999";"100000000";"100000001";
  "1234";"5678";"12345678";"987654321";
  "-1";"-2";"-99";"-100";"-101";"-9999";"-10000";"-10001";
  "-999999";"-1000000";"-1000001";"-99999999";"-100000000";"-100000001";
  "-1234";"-5678";"-12345678";"-987654321";"0"
  ]
  in
  let eucl n m =
    let n' = abs_float n and m' = abs_float m in
    let q' = floor (n' /. m') in let r' = n' -. m' *. q' in
    (if n *. m < 0. & q' <> 0. then -. q' else q'),
    (if n < 0. then -. r' else r') in
  let round f = floor (abs_float f +. 0.5) *. (if f < 0. then -1. else 1.) in
  let i = ref 0 in
  let compare op n n' =
    incr i;
    let s = Printf.sprintf "%30s" (to_string n) in
    let s' = Printf.sprintf "% 30.0f" (round n') in
    if s <> s' then Printf.printf "%s: %s <> %s\n" op s s' in
List.iter (fun a -> List.iter (fun b ->
  let n = of_string a and m = of_string b in
  let n' = float_of_string a and m' = float_of_string b in
  let a = add n m and a' = n' +. m' in
  let s = sub n m and s' = n' -. m' in
  let p = mult n m and p' = n' *. m' in
  let q,r = try euclid n m with Division_by_zero -> zero,zero
  and q',r' = eucl n' m' in
  compare "+" a a';
  compare "-" s s';
  compare "*" p p';
  compare "/" q q';
  compare "%" r r') numbers) numbers;
  Printf.printf "%i tests done\n" !i


