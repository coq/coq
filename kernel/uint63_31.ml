(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Invariant: the msb should be 0 *)
type t = Int64.t

let _ = assert (Sys.word_size = 32)

let uint_size = 63

let maxuint63 = Int64.of_string "0x7FFFFFFFFFFFFFFF"
let maxuint31 = Int64.of_string "0x7FFFFFFF"

let zero = Int64.zero
let one = Int64.one

    (* conversion from an int *)
let mask63 i = Int64.logand i maxuint63
let of_int i = Int64.of_int i
let to_int2 i = (Int64.to_int (Int64.shift_right_logical i 31), Int64.to_int i)
let of_int64 i = i
let hash i =
  let (h,l) = to_int2 i in
  (*Hashset.combine h l*)
  h * 65599 + l

    (* conversion of an uint63 to a string *)
let to_string i = Int64.to_string i

let of_string s =
  let i64 = Int64.of_string s in
  if Int64.compare Int64.zero i64 <= 0
      && Int64.compare i64 maxuint63 <= 0
  then i64
  else raise (Failure "Int63.of_string")

(* Compiles an unsigned int to OCaml code *)
let compile i = Printf.sprintf "Uint63.of_int64 (%LiL)" i

    (* comparison *)
let lt x y =
  Int64.compare x y < 0

let le x y =
  Int64.compare x y <= 0

    (* logical shift *)
let l_sl x y =
  if le 0L y && lt y 63L then mask63 (Int64.shift_left x (Int64.to_int y)) else 0L

let l_sr x y =
  if le 0L y && lt y 63L then Int64.shift_right x (Int64.to_int y) else 0L

let l_and x y = Int64.logand x y
let l_or x y = Int64.logor x y
let l_xor x y = Int64.logxor x y

    (* addition of int63 *)
let add x y = mask63 (Int64.add x y)

let addcarry x y = add (add x y) Int64.one

    (* subtraction *)
let sub x y = mask63 (Int64.sub x y)

let subcarry x y = sub (sub x y) Int64.one

    (* multiplication *)
let mul x y = mask63 (Int64.mul x y)

    (* division *)
let div x y =
  if y = 0L then 0L else Int64.div x y

    (* modulo *)
let rem x y =
  if y = 0L then 0L else Int64.rem x y

let diveucl x y = (div x y, rem x y)

let addmuldiv p x y =
  l_or (l_sl x p) (l_sr y Int64.(sub (of_int uint_size) p))

    (* division of two numbers by one *)
(* precondition: xh < y *)
(* outputs: q, r s.t. x = q * y + r, r < y *)
let div21 xh xl y =
  let nh = ref xh in
  let nl = ref xl in
  let q = ref 0L in
  for _i = 0 to 62 do
    (* invariants: 0 <= nh < y, nl = (xl*2^i) % 2^64,
       (q*y + nh) * 2^(63-i) + (xl % 2^(63-i)) = (xh%y) * 2^63 + xl *)
    nl := Int64.shift_left !nl 1;
    nh := Int64.logor (Int64.shift_left !nh 1) (Int64.shift_right_logical !nl 63);
    q := Int64.shift_left !q 1;
    (* TODO: use "Int64.unsigned_compare !nh y >= 0",
       once OCaml 4.08 becomes the minimal required version *)
    if Int64.compare !nh 0L < 0 || Int64.compare !nh y >= 0 then
      begin q := Int64.logor !q 1L; nh := Int64.sub !nh y; end
  done;
  !q, !nh

let div21 xh xl y =
  if Int64.compare y xh <= 0 then zero, zero else div21 xh xl y

     (* exact multiplication *)
let mulc x y =
  let lx = ref (Int64.logand x maxuint31) in
  let ly = ref (Int64.logand y maxuint31) in
  let hx = Int64.shift_right x 31 in
  let hy = Int64.shift_right y 31 in
  let hr = ref (Int64.mul hx hy) in
  let lr = ref (Int64.logor (Int64.mul !lx !ly) (Int64.shift_left !hr 62)) in
  hr := (Int64.shift_right_logical !hr 1);
  lx := Int64.mul !lx hy;
  ly := Int64.mul hx !ly;
  hr := Int64.logor !hr (Int64.add (Int64.shift_right !lx 32) (Int64.shift_right !ly 32));
  lr := Int64.add !lr (Int64.shift_left !lx 31);
  hr := Int64.add !hr (Int64.shift_right_logical !lr 63);
  lr := Int64.add (Int64.shift_left !ly 31) (mask63 !lr);
  hr := Int64.add !hr (Int64.shift_right_logical !lr 63);
  if Int64.logand !lr Int64.min_int <> 0L
  then Int64.(sub !hr one, mask63 !lr)
  else (!hr, !lr)

let equal x y = mask63 x = mask63 y

let compare x y = Int64.compare x y

(* Number of leading zeroes *)
let head0 x =
  let r = ref 0 in
  let x = ref x in
  if Int64.logand !x 0x7FFFFFFF00000000L = 0L then r := !r + 31
  else x := Int64.shift_right !x 31;
  if Int64.logand !x 0xFFFF0000L = 0L then (x := Int64.shift_left !x 16; r := !r + 16);
  if Int64.logand !x 0xFF000000L = 0L then (x := Int64.shift_left !x 8; r := !r + 8);
  if Int64.logand !x 0xF0000000L = 0L then (x := Int64.shift_left !x 4; r := !r + 4);
  if Int64.logand !x 0xC0000000L = 0L then (x := Int64.shift_left !x 2; r := !r + 2);
  if Int64.logand !x 0x80000000L = 0L then (x := Int64.shift_left !x 1; r := !r + 1);
  if Int64.logand !x 0x80000000L = 0L then (r := !r + 1);
  Int64.of_int !r

(* Number of trailing zeroes *)
let tail0 x =
  let r = ref 0 in
  let x = ref x in
  if Int64.logand !x 0xFFFFFFFFL = 0L then (x := Int64.shift_right !x 32; r := !r + 32);
  if Int64.logand !x 0xFFFFL = 0L then (x := Int64.shift_right !x 16; r := !r + 16);
  if Int64.logand !x 0xFFL = 0L then (x := Int64.shift_right !x 8; r := !r + 8);
  if Int64.logand !x 0xFL = 0L then (x := Int64.shift_right !x 4; r := !r + 4);
  if Int64.logand !x 0x3L = 0L then (x := Int64.shift_right !x 2; r := !r + 2);
  if Int64.logand !x 0x1L = 0L then (r := !r + 1);
  Int64.of_int !r

(* May an object be safely cast into an Uint63.t ? *)
let is_uint63 t =
  Obj.is_block t && CInt.equal (Obj.tag t) Obj.custom_tag
  && le (Obj.magic t) maxuint63

(* Arithmetic with explicit carries *)

(* Analog of Numbers.Abstract.Cyclic.carry *)
type 'a carry = C0 of 'a | C1 of 'a

let addc x y =
  let r = add x y in
  if lt r x then C1 r else C0 r

let addcarryc x y =
  let r = addcarry x y in
  if le r x then C1 r else C0 r

let subc x y =
  let r = sub x y in
  if le y x then C0 r else C1 r

let subcarryc x y =
  let r = subcarry x y in
  if lt y x then C0 r else C1 r

(* Register all exported functions so that they can be called from C code *)

let () =
  Callback.register "uint63 add" add;
  Callback.register "uint63 addcarry" addcarry;
  Callback.register "uint63 addmuldiv" addmuldiv;
  Callback.register "uint63 div" div;
  Callback.register "uint63 div21_ml" div21;
  Callback.register "uint63 eq" equal;
  Callback.register "uint63 eq0" (equal Int64.zero);
  Callback.register "uint63 head0" head0;
  Callback.register "uint63 land" l_and;
  Callback.register "uint63 leq" le;
  Callback.register "uint63 lor" l_or;
  Callback.register "uint63 lsl" l_sl;
  Callback.register "uint63 lsl1" (fun x -> l_sl x Int64.one);
  Callback.register "uint63 lsr" l_sr;
  Callback.register "uint63 lsr1" (fun x -> l_sr x Int64.one);
  Callback.register "uint63 lt" lt;
  Callback.register "uint63 lxor" l_xor;
  Callback.register "uint63 mod" rem;
  Callback.register "uint63 mul" mul;
  Callback.register "uint63 mulc_ml" mulc;
  Callback.register "uint63 one" one;
  Callback.register "uint63 sub" sub;
  Callback.register "uint63 subcarry" subcarry;
  Callback.register "uint63 tail0" tail0
