(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t = int

let _ = assert (Sys.word_size = 64)

let uint_size = 63

let maxuint63 = Int64.of_string "0x7FFFFFFFFFFFFFFF"
let maxuint31 = 0x7FFFFFFF

    (* conversion from an int *)
let to_uint64 i = Int64.logand (Int64.of_int i) maxuint63

let of_int i = i
[@@ocaml.inline always]

let to_int2 i = (0,i)

let of_int64 = Int64.to_int
let to_int64 = to_uint64

let of_float = int_of_float

external to_float : int -> (float [@unboxed])
  = "coq_uint63_to_float_byte" "coq_uint63_to_float"
[@@noalloc]

let hash i = i
[@@ocaml.inline always]

    (* conversion of an uint63 to a string *)
let to_string i = Int64.to_string (to_uint64 i)

(* Compiles an unsigned int to OCaml code *)
let compile i = Printf.sprintf "Uint63.of_int (%i)" i

let zero = 0
let one = 1

    (* logical shift *)
let l_sl x y =
  if 0 <= y && y < 63 then x lsl y else 0

let l_sr x y =
  if 0 <= y && y < 63 then x lsr y else 0

    (* arithmetic shift (for sint63) *)
let a_sr x y =
  if 0 <= y && y < 63 then x asr y else 0

let l_and x y = x land y
[@@ocaml.inline always]

let l_or x y = x lor y
[@@ocaml.inline always]

let l_xor x y = x lxor y
[@@ocaml.inline always]

    (* addition of int63 *)
let add x y = x + y
[@@ocaml.inline always]

    (* subtraction *)
let sub x y = x - y
[@@ocaml.inline always]

    (* multiplication *)
let mul x y = x * y
[@@ocaml.inline always]

    (* division *)
let div (x : int) (y : int) =
  if y = 0 then 0 else Int64.to_int (Int64.div (to_uint64 x) (to_uint64 y))

    (* modulo *)
let rem (x : int) (y : int) =
  if y = 0 then x else Int64.to_int (Int64.rem (to_uint64 x) (to_uint64 y))

let diveucl x y = (div x y, rem x y)

    (* signed division *)
let divs (x : int) (y : int) =
  if y = 0 then 0 else x / y

    (* modulo *)
let rems (x : int) (y : int) =
  if y = 0 then x else x mod y

let addmuldiv p x y =
  l_or (l_sl x p) (l_sr y (uint_size - p))

    (* comparison *)
let lt (x : int) (y : int) =
  (x lxor 0x4000000000000000) < (y lxor 0x4000000000000000)
[@@ocaml.inline always]

let le (x : int) (y : int) =
  (x lxor 0x4000000000000000) <= (y lxor 0x4000000000000000)
[@@ocaml.inline always]

    (* signed comparison *)
let lts (x : int) (y : int) =
  x < y
[@@ocaml.inline always]

let les (x : int) (y : int) =
  x <= y
[@@ocaml.inline always]

let to_int_min n m =
  if lt n m then n else m
[@@ocaml.inline always]

    (* division of two numbers by one *)
(* precondition: xh < y *)
(* outputs: q, r s.t. x = q * y + r, r < y *)
let div21 xh xl y =
  (* nh might temporarily grow as large as 2*y - 1 in the loop body,
     so we store it as a 64-bit unsigned integer *)
  let nh = ref xh in
  let nl = ref xl in
  let q = ref 0 in
  for _i = 0 to 62 do
    (* invariants: 0 <= nh < y, nl = (xl*2^i) % 2^63,
       (q*y + nh) * 2^(63-i) + (xl % 2^(63-i)) = (xh%y) * 2^63 + xl *)
    nh := Int64.logor (Int64.shift_left !nh 1) (Int64.of_int (!nl lsr 62));
    nl := !nl lsl 1;
    q := !q lsl 1;
    if Int64.unsigned_compare !nh y >= 0 then
      begin q := !q lor 1; nh := Int64.sub !nh y; end
  done;
  !q, Int64.to_int !nh

let div21 xh xl y =
  let xh = to_uint64 xh in
  let y = to_uint64 y in
  if Int64.compare y xh <= 0 then 0, 0 else div21 xh xl y

     (* exact multiplication *)
(* TODO: check that none of these additions could be a logical or *)


(* size = 32 + 31
   (hx << 31 + lx) * (hy << 31 + ly) =
   hxhy << 62 + (hxly + lxhy) << 31 + lxly
*)

(* precondition : (x lsr 62 = 0 || y lsr 62 = 0) *)
let mulc_aux x y =
  let lx = x land maxuint31 in
  let ly = y land maxuint31 in
  let hx = x lsr 31  in
  let hy = y lsr 31 in
    (* hx and hy are 32 bits value but at most one is 32 *)
  let hxy  = hx * hy in (* 63 bits *)
  let hxly = hx * ly in (* 63 bits *)
  let lxhy = lx * hy in (* 63 bits *)
  let lxy  = lx * ly in (* 62 bits *)
  let l  = lxy lor (hxy lsl 62) (* 63 bits *) in
  let h  = hxy lsr 1 in (* 62 bits *)
  let hl = hxly + lxhy in (* We can have a carry *)
  let h  = if lt hl hxly then h + (1 lsl 31) else h in
  let hl'= hl lsl 31 in
  let l  = l + hl' in
  let h  = if lt l hl' then h + 1 else h in
  let h  = h + (hl lsr 32) in
  (h,l)

let mulc x y =
  if (x lsr 62 = 0 || y lsr 62 = 0) then mulc_aux x y
  else
    let yl = y lxor (1 lsl 62) in
    let (h,l) = mulc_aux x yl in
    (* h << 63 + l = x * yl
       x * y = x * (1 << 62 + yl)  =
       x << 62 + x*yl = x << 62 + h << 63 + l *)
    let l' = l + (x lsl 62) in
    let h = if lt l' l then h + 1 else h in
    (h + (x lsr 1), l')

let equal (x : int) (y : int) = x = y
[@@ocaml.inline always]

let compare (x:int) (y:int) =
  let x = x lxor 0x4000000000000000 in
  let y = y lxor 0x4000000000000000 in
  Int.compare x y

let compares (x : int) (y : int) =
  Int.compare x y

    (* head tail *)

let head0 x =
  let r = ref 0 in
  let x = ref x in
  if !x land 0x7FFFFFFF00000000 = 0 then r := !r + 31
  else x := !x lsr 31;
  if !x land 0xFFFF0000 = 0 then (x := !x lsl 16; r := !r + 16);
  if !x land 0xFF000000 = 0 then (x := !x lsl 8; r := !r + 8);
  if !x land 0xF0000000 = 0 then (x := !x lsl 4; r := !r + 4);
  if !x land 0xC0000000 = 0 then (x := !x lsl 2; r := !r + 2);
  if !x land 0x80000000 = 0 then (x := !x lsl 1; r := !r + 1);
  if !x land 0x80000000 = 0 then (               r := !r + 1);
  !r;;

let tail0 x =
  let r = ref 0 in
  let x = ref x in
  if !x land 0xFFFFFFFF = 0 then (x := !x lsr 32; r := !r + 32);
  if !x land 0xFFFF = 0 then (x := !x lsr 16; r := !r + 16);
  if !x land 0xFF = 0   then (x := !x lsr 8;  r := !r + 8);
  if !x land 0xF = 0    then (x := !x lsr 4;  r := !r + 4);
  if !x land 0x3 = 0    then (x := !x lsr 2;  r := !r + 2);
  if !x land 0x1 = 0    then (                r := !r + 1);
  !r

let is_uint63 t =
  Obj.is_int t
[@@ocaml.inline always]

(* Arithmetic with explicit carries *)

(* Analog of Numbers.Abstract.Cyclic.carry *)
type 'a carry = C0 of 'a | C1 of 'a

let addc x y =
  let r = x + y in
  if lt r x then C1 r else C0 r

let addcarryc x y =
  let r = x + y + 1 in
  if le r x then C1 r else C0 r

let subc x y =
  let r = x - y in
  if le y x then C0 r else C1 r

let subcarryc x y =
  let r = x - y - 1 in
  if lt y x then C0 r else C1 r
