(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(***************************************************)
(* Basic operations on (unbounded) integer numbers *)
(***************************************************)

(* An integer is canonically represented as an array of k-digits blocs,
   i.e. in base 10^k.

   0 is represented by the empty array and -1 by the singleton [|-1|].
   The first bloc is in the range ]0;base[ for positive numbers.
   The first bloc is in the range [-base;-1[ for numbers < -1.
   All other blocs are numbers in the range [0;base[.

   Negative numbers are represented using 2's complementation :
   one unit is "borrowed" from the top block for complementing
   the other blocs. For instance, with 4-digits blocs,
   [|-5;6789|] denotes -43211
   since -5.10^4+6789=-((4.10^4)+(10000-6789)) = -43211

   The base is a power of 10 in order to facilitate the parsing and printing
   of numbers in digital notation.

   All functions, to the exception of to_string and of_string should work
   with an arbitrary base, even if not a power of 10.

   In practice, we set k=4 on 32-bits machines, so that no overflow in ocaml
   machine words (i.e. the interval [-2^30;2^30-1]) occur when multiplying two
   numbers less than (10^k). On 64-bits machines, k=9.
*)

(* The main parameters *)

let size =
  let rec log10 n = if n < 10 then 0 else 1 + log10 (n / 10) in
  (log10 max_int) / 2

let format_size =
  (* How to parametrize a printf format *)
  if Int.equal size 4 then Printf.sprintf "%04d"
  else if Int.equal size 9 then Printf.sprintf "%09d"
  else fun n ->
    let rec aux j l n =
      if Int.equal j size then l else aux (j+1) (string_of_int (n mod 10) :: l) (n/10)
    in String.concat "" (aux 0 [] n)

(* The base is 10^size *)
let base =
  let rec exp10 = function 0 -> 1 | n -> 10 * exp10 (n-1) in exp10 size

(******************************************************************)
(* First, we represent all numbers by int arrays.
   Later, we will optimize the particular case of small integers  *)
(******************************************************************)

module ArrayInt = struct

(* Basic numbers *)
let zero = [||]

let is_zero = function
| [||] -> true
| _ -> false

(* An array is canonical when
   - it is empty
   - it is [|-1|]
   - its first bloc is in [-base;-1[U]0;base[
     and the other blocs are in [0;base[. *)
(*
let canonical n =
  let ok x = (0 <= x && x < base) in
  let rec ok_tail k = (Int.equal k 0) || (ok n.(k) && ok_tail (k-1)) in
  let ok_init x = (-base <= x && x < base && not (Int.equal x (-1)) && not (Int.equal x 0))
  in
  (is_zero n) || (match n with [|-1|] -> true | _ -> false) ||
    (ok_init n.(0) && ok_tail (Array.length n - 1))
*)

(* [normalize_pos] : removing initial blocks of 0 *)

let normalize_pos n =
  let k = ref 0 in
  while !k < Array.length n && Int.equal n.(!k) 0 do incr k done;
  Array.sub n !k (Array.length n - !k)

(* [normalize_neg] : avoid (-1) as first bloc.
   input: an array with -1 as first bloc and other blocs in [0;base[
   output: a canonical array *)

let normalize_neg n =
  let k = ref 1 in
  while !k < Array.length n && Int.equal n.(!k) (base - 1) do incr k done;
  let n' = Array.sub n !k (Array.length n - !k) in
  if Int.equal (Array.length n') 0 then [|-1|] else (n'.(0) <- n'.(0) - base; n')

(* [normalize] : avoid 0 and (-1) as first bloc.
   input: an array with first bloc in [-base;base[ and others in [0;base[
   output: a canonical array *)

let normalize n =
  if Int.equal (Array.length n) 0 then n
  else if Int.equal n.(0) (-1) then normalize_neg n
  else if Int.equal n.(0) 0 then normalize_pos n
  else n

(* Opposite (expects and returns canonical arrays) *)

let neg m =
  if is_zero m then zero else
  let n = Array.copy m in
  let i = ref (Array.length m - 1) in
  while !i > 0 && Int.equal n.(!i) 0 do decr i done;
  if Int.equal !i 0 then begin
    n.(0) <- - n.(0);
    (* n.(0) cannot be 0 since m is canonical *)
    if Int.equal n.(0) (-1) then normalize_neg n
    else if Int.equal n.(0) base then (n.(0) <- 0; Array.append [| 1 |] n)
    else n
  end else begin
    (* here n.(!i) <> 0, hence 0 < base - n.(!i) < base for n canonical *)
    n.(!i) <- base - n.(!i); decr i;
    while !i > 0 do n.(!i) <- base - 1 - n.(!i); decr i done;
    (* since -base <= n.(0) <= base-1, hence -base <= -n.(0)-1 <= base-1 *)
    n.(0) <- - n.(0) - 1;
    (* since m is canonical, m.(0)<>0 hence n.(0)<>-1,
       and m=-1 is already handled above, so here m.(0)<>-1 hence n.(0)<>0 *)
    n
  end

let push_carry r j =
  let j = ref j in
  while !j > 0 && r.(!j) < 0 do
    r.(!j) <- r.(!j) + base; decr j; r.(!j) <- r.(!j) - 1
  done;
  while !j > 0 && r.(!j) >= base do
    r.(!j) <- r.(!j) - base; decr j; r.(!j) <- r.(!j) + 1
  done;
  (* here r.(0) could be in [-2*base;2*base-1] *)
  if r.(0) >= base then (r.(0) <- r.(0) - base; Array.append [| 1 |] r)
  else if r.(0) < -base then (r.(0) <- r.(0) + 2*base; Array.append [| -2 |] r)
  else normalize r (* in case r.(0) is 0 or -1 *)

let add_to r a j =
  if is_zero a then r else begin
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
  if is_zero a then r else begin
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

let mult m n =
  if is_zero m || is_zero n then zero else
  let l = Array.length m + Array.length n in
  let r = Array.make l 0 in
  for i = Array.length m - 1 downto 0 do
    for j = Array.length n - 1 downto 0 do
      let p = m.(i) * n.(j) + r.(i+j+1) in
      let (q,s) =
        if p < 0
        then (p + 1) / base - 1, (p + 1) mod base + base - 1
        else p / base, p mod base in
      r.(i+j+1) <- s;
      if not (Int.equal q 0) then r.(i+j) <- r.(i+j) + q;
    done
  done;
  normalize r

(* Comparisons *)

let is_strictly_neg n = not (is_zero n) && n.(0) < 0
let is_strictly_pos n = not (is_zero n) && n.(0) > 0
let is_neg_or_zero n = is_zero n || n.(0) < 0
let is_pos_or_zero n = is_zero n || n.(0) > 0

(* Is m without its i first blocs less then n without its j first blocs ?
   Invariant : |m|-i = |n|-j *)

let rec less_than_same_size m n i j =
  i < Array.length m &&
  (m.(i) < n.(j) || (Int.equal m.(i) n.(j) && less_than_same_size m n (i+1) (j+1)))

let less_than m n =
  if is_strictly_neg m then
    is_pos_or_zero n || Array.length m > Array.length n
      || (Int.equal (Array.length m) (Array.length n) && less_than_same_size m n 0 0)
  else
    is_strictly_pos n && (Array.length m < Array.length n ||
    (Int.equal (Array.length m) (Array.length n) && less_than_same_size m n 0 0))

(* For this equality test it is critical that n and m are canonical *)

let rec array_eq len v1 v2 i =
  if Int.equal len i then true
  else
    Int.equal v1.(i) v2.(i) && array_eq len v1 v2 (succ i)

let equal m n =
  let lenm = Array.length m in
  let lenn = Array.length n in
  (Int.equal lenm lenn) && (array_eq lenm m n 0)

(* Is m without its k top blocs less than n ? *)

let less_than_shift_pos k m n =
  (Array.length m - k < Array.length n)
  || (Int.equal (Array.length m - k) (Array.length n) && less_than_same_size m n k 0)

let rec can_divide k m d i =
  (Int.equal i (Array.length d)) ||
  (m.(k+i) > d.(i)) ||
  (Int.equal m.(k+i) d.(i) && can_divide k m d (i+1))

(* For two big nums m and d and a small number q,
   computes m - d * q * base^(|m|-|d|-k) in-place (in m).
   Both m d and q are positive. *)

let sub_mult m d q k =
  if not (Int.equal q 0) then
  for i = Array.length d - 1 downto 0 do
    let v = d.(i) * q in
    m.(k+i) <- m.(k+i) - v mod base;
    if m.(k+i) < 0 then (m.(k+i) <- m.(k+i) + base; m.(k+i-1) <- m.(k+i-1) -1);
    if v >= base then begin
      m.(k+i-1) <- m.(k+i-1) - v / base;
      let j = ref (i-1) in
      while m.(k + !j) < 0 do (* result is positive, hence !j remains >= 0 *)
        m.(k + !j) <- m.(k + !j) + base; decr j; m.(k + !j) <- m.(k + !j) -1
      done
    end
  done

(** Euclid division m/d = (q,r), with m = q*d+r and |r|<|q|.
    This is the "Trunc" variant (a.k.a "Truncated-Toward-Zero"),
    as with ocaml's / (but not as ocaml's Big_int.quomod_big_int).
    We have sign r = sign m *)

let euclid m d =
  let isnegm, m =
    if is_strictly_neg m then (-1),neg m else 1,Array.copy m in
  let isnegd, d = if is_strictly_neg d then (-1),neg d else 1,d in
  if is_zero d then raise Division_by_zero;
  let q,r =
    if less_than m d then (zero,m) else
    let ql = Array.length m - Array.length d in
    let q = Array.make (ql+1) 0 in
    let i = ref 0 in
    while not (less_than_shift_pos !i m d) do
      if Int.equal m.(!i) 0 then incr i else
      if can_divide !i m d 0 then begin
        let v =
          if Array.length d > 1 && not (Int.equal d.(0) m.(!i)) then
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
  (if Int.equal (isnegd * isnegm) (-1) then neg q else q),
  (if Int.equal isnegm (-1) then neg r else r)

(* Parsing/printing ordinary 10-based numbers *)

let of_string s =
  let len = String.length s in
  let isneg = len > 1 && s.[0] == '-' in
  let d = ref (if isneg then 1 else 0) in
  while !d < len && s.[!d] == '0' do incr d done;
  if Int.equal !d len then zero else
  let r = (len - !d) mod size in
  let h = String.sub s (!d) r in
  let e = match h with "" -> 0 | _ -> 1 in
  let l = (len - !d) / size in
  let a = Array.make (l + e) 0 in
  if Int.equal e 1 then a.(0) <- int_of_string h;
  for i = 1 to l do
    a.(i+e-1) <- int_of_string (String.sub s ((i-1)*size + !d + r) size)
  done;
  if isneg then neg a else a

let to_string_pos sgn n =
   if Int.equal (Array.length n) 0 then "0" else
     sgn ^
     String.concat ""
      (string_of_int n.(0) :: List.map format_size (List.tl (Array.to_list n)))

let to_string n =
  if is_strictly_neg n then to_string_pos "-" (neg n)
  else to_string_pos "" n

end

(******************************************************************)
(* Optimized operations on (unbounded) integer numbers            *)
(* integers smaller than base are represented as machine integers *)
(******************************************************************)

open ArrayInt

type bigint = Obj.t

(* Since base is the largest power of 10 such that base*base <= max_int,
   we have max_int < 100*base*base : any int can be represented
   by at most three blocs *)

let small n = (-base <= n) && (n < base)

let mkarray n =
  (* n isn't small, this case is handled separately below *)
  let lo = n mod base
  and hi = n / base in
  let t = if small hi then [|hi;lo|] else [|hi/base;hi mod base;lo|]
  in
  for i = Array.length t -1 downto 1 do
    if t.(i) < 0 then (t.(i) <- t.(i) + base; t.(i-1) <- t.(i-1) -1)
  done;
  t

let ints_of_int n =
  if Int.equal n 0 then [| |]
  else if small n then [| n |]
  else mkarray n

let of_int n =
  if small n then Obj.repr n else Obj.repr (mkarray n)

let of_ints n =
  let n = normalize n in (* TODO: using normalize here seems redundant now *)
  if is_zero n then Obj.repr 0 else
  if Int.equal (Array.length n) 1 then Obj.repr n.(0) else
  Obj.repr n

let coerce_to_int = (Obj.magic : Obj.t -> int)
let coerce_to_ints = (Obj.magic : Obj.t -> int array)

let to_ints n =
  if Obj.is_int n then ints_of_int (coerce_to_int n)
  else coerce_to_ints n

let int_of_ints =
  let maxi = mkarray max_int and mini = mkarray min_int in
  fun t ->
    let l = Array.length t in
    if (l > 3) || (Int.equal l 3 && (less_than maxi t || less_than t mini))
    then failwith "Bigint.to_int: too large";
    let sum = ref 0 in
    let pow = ref 1 in
    for i = l-1 downto 0 do
      sum := !sum + t.(i) * !pow;
      pow := !pow*base;
    done;
    !sum

let to_int n =
  if Obj.is_int n then coerce_to_int n
  else int_of_ints (coerce_to_ints n)

let app_pair f (m, n) =
  (f m, f n)

let add m n =
  if Obj.is_int m && Obj.is_int n
  then of_int (coerce_to_int m + coerce_to_int n)
  else of_ints (add (to_ints m) (to_ints n))

let sub m n =
  if Obj.is_int m && Obj.is_int n
  then of_int (coerce_to_int m - coerce_to_int n)
  else of_ints (sub (to_ints m) (to_ints n))

let mult m n =
  if Obj.is_int m && Obj.is_int n
  then of_int (coerce_to_int m * coerce_to_int n)
  else of_ints (mult (to_ints m) (to_ints n))

let euclid m n =
  if Obj.is_int m && Obj.is_int n
  then app_pair of_int
    (coerce_to_int m / coerce_to_int n, coerce_to_int m mod coerce_to_int n)
  else app_pair of_ints (euclid (to_ints m) (to_ints n))

let less_than m n =
  if Obj.is_int m && Obj.is_int n
  then coerce_to_int m < coerce_to_int n
  else less_than (to_ints m) (to_ints n)

let neg n =
  if Obj.is_int n then of_int (- (coerce_to_int n))
  else of_ints (neg (to_ints n))

let of_string m = of_ints (of_string m)
let to_string m = to_string (to_ints m)

let zero = of_int 0
let one = of_int 1
let two = of_int 2
let sub_1 n = sub n one
let add_1 n = add n one
let mult_2 n = add n n

let div2_with_rest n =
  let (q,b) = euclid n two in
  (q, b == one)

let is_strictly_neg n = is_strictly_neg (to_ints n)
let is_strictly_pos n = is_strictly_pos (to_ints n)
let is_neg_or_zero n = is_neg_or_zero (to_ints n)
let is_pos_or_zero n = is_pos_or_zero (to_ints n)

let equal m n =
  if Obj.is_block m && Obj.is_block n then
    ArrayInt.equal (Obj.obj m) (Obj.obj n)
  else m == n

(* spiwack: computes n^m *)
(* The basic idea of the algorithm is that n^(2m) = (n^2)^m *)
(* In practice the algorithm performs :
    k*n^0 = k
    k*n^(2m) = k*(n*n)^m
    k*n^(2m+1) = (n*k)*(n*n)^m *)
let pow  =
  let rec pow_aux odd_rest n m = (* odd_rest is the k from above *)
    if m<=0 then
      odd_rest
    else
      let quo = m lsr 1 (* i.e. m/2 *)
      and odd = not (Int.equal (m land 1) 0) in
      pow_aux
	(if odd then mult n odd_rest else odd_rest)
	(mult n n)
	quo
  in
  pow_aux one

(** Testing suite w.r.t. OCaml's Big_int *)

(*
module B = struct
  open Big_int
  let zero = zero_big_int
  let to_string = string_of_big_int
  let of_string = big_int_of_string
  let add = add_big_int
  let opp = minus_big_int
  let sub = sub_big_int
  let mul = mult_big_int
  let abs = abs_big_int
  let sign = sign_big_int
  let euclid n m =
    let n' = abs n and m' = abs m in
    let q',r' = quomod_big_int n' m' in
    (if sign (mul n m) < 0 && sign q' <> 0 then opp q' else q'),
    (if sign n < 0 then opp r' else r')
end

let check () =
  let roots = [ 1; 100; base; 100*base; base*base ] in
  let rands = [ 1234; 5678; 12345678; 987654321 ] in
  let nums = (List.flatten (List.map (fun x -> [x-1;x;x+1]) roots)) @ rands in
  let numbers =
    List.map string_of_int nums @
    List.map (fun n -> string_of_int (-n)) nums
  in
  let i = ref 0 in
  let compare op x y n n' =
    incr i;
    let s = Printf.sprintf "%30s" (to_string n) in
    let s' = Printf.sprintf "%30s" (B.to_string n') in
    if s <> s' then Printf.printf "%s%s%s: %s <> %s\n" x op y s s' in
  let test x y =
    let n = of_string x and m = of_string y in
    let n' = B.of_string x and m' = B.of_string y in
    let a = add n m and a' = B.add n' m' in
    let s = sub n m and s' = B.sub n' m' in
    let p = mult n m and p' = B.mul n' m' in
    let q,r = try euclid n m with Division_by_zero -> zero,zero
    and q',r' = try B.euclid n' m' with Division_by_zero -> B.zero, B.zero
    in
    compare "+" x y a a';
    compare "-" x y s s';
    compare "*" x y p p';
    compare "/" x y q q';
    compare "%" x y r r'
  in
  List.iter (fun a -> List.iter (test a) numbers) numbers;
  Printf.printf "%i tests done\n" !i
*)
