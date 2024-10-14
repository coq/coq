(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Stream = Gramlib.Stream

(** We keep the string to preserve the user representation,
    e.g. "e"/"E" or the presence of leading 0s, or the presence of a +
    in the exponent *)

type num_class = CDec | CHex

let string_del_head n s = String.sub s n (String.length s - n)

module UnsignedNat =
struct
  type t = string
  let of_string s =
    assert (String.length s > 0);
    assert (s.[0] >= '0' && s.[0] <= '9');
    s
  let to_string s =
    String.(map Char.lowercase_ascii (concat "" (split_on_char '_' s)))

  let sprint s = s
  let print s = Pp.str (sprint s)

  let classify s =
    if String.length s >= 2 && (s.[1] = 'x' || s.[1] = 'X') then CHex else CDec

  (** Comparing two raw numbers (base 10 or 16, big-endian, non-negative).
      A bit nasty, but not critical: used e.g. to decide when a number
      is considered as large (see threshold warnings in notation.ml). *)

  exception Comp of int

  let rec compare s s' =
    let l = String.length s and l' = String.length s' in
    if l < l' then - compare s' s
    else
      let d = l-l' in
      try
        for i = 0 to d-1 do if s.[i] != '0' then raise (Comp 1) done;
        for i = d to l-1 do
          let c = Stdlib.compare s.[i] s'.[i-d] in
          if c != 0 then raise (Comp c)
        done;
        0
      with Comp c -> c

  let compare n d =
    assert (classify d = CDec);
    match classify n with
    | CDec -> compare (to_string n) (to_string d)
    | CHex -> compare (string_del_head 2 (to_string n)) (to_string d)

  let is_zero s =
    compare s "0" = 0
end

type sign = SPlus | SMinus

type 'a exp = EDec of 'a | EBin of 'a

module SignedNat =
struct
  type t = sign * UnsignedNat.t
  let of_string s =
    assert (String.length s > 0);
    let sign,n =
      match s.[0] with
      | '-' -> (SMinus,string_del_head 1 s)
      | '+' -> (SPlus,string_del_head 1 s)
      | _ -> (SPlus,s) in
    (sign,UnsignedNat.of_string n)
  let to_string (sign,n) =
    (match sign with SPlus -> "" | SMinus -> "-") ^ UnsignedNat.to_string n
  let classify (_,n) = UnsignedNat.classify n
  let bigint_of_string (sign,n) = Z.of_string (to_string (sign,n))
  let to_bigint n = bigint_of_string n
  let string_of_nonneg_bigint c n =
    match c with
    | CDec -> Z.format "%d" n
    | CHex -> Z.format "%#x" n
  let of_bigint c n =
    let sign, n = if Int.equal (-1) (Z.sign n) then (SMinus, Z.neg n) else (SPlus, n) in
    (sign, string_of_nonneg_bigint c n)
end

module Unsigned =
struct

  type t = {
    int : string;
    frac : string;
    exp : string
  }
  (**
    - int: \[0-9\]\[0-9_\]*
    - frac: empty or \[0-9_\]+
    - exp: empty or \[eE\]\[+-\]?\[0-9\]\[0-9_\]*
    or
    - int: 0\[xX\]\[0-9a-fA-F\]\[0-9a-fA-F_\]*
    - frac: empty or \[0-9a-fA-F_\]+
    - exp: empty or \[pP\]\[+-\]?\[0-9\]\[0-9_\]* *)

  let equal n1 n2 =
    String.(equal n1.int n2.int && equal n1.frac n2.frac && equal n1.exp n2.exp)

  let parse =
    let buff = ref (Bytes.create 80) in
    let store len x =
      let open Bytes in
      if len >= length !buff then
        buff := cat !buff (create (length !buff));
      set !buff len x;
      succ len in
    let get_buff len = Bytes.sub_string !buff 0 len in
    (* reads [0-9_]* *)
    let rec number len s = match Stream.peek () s with
      | Some ('0'..'9' as c) -> Stream.junk () s; number (store len c) s
      | Some ('_' as c) when len > 0 -> Stream.junk () s; number (store len c) s
      | _ -> len in
    (* reads [0-9a-fA-F_]* *)
    let rec hex_number len s = match Stream.peek () s with
      | Some (('0'..'9' | 'a'..'f' | 'A'..'F') as c) ->
         Stream.junk () s; hex_number (store len c) s
      | Some ('_' as c) when len > 0 ->
         Stream.junk () s; hex_number (store len c) s
      | _ -> len in
    fun s ->
    let hex, i =
      match Stream.npeek () 3 s with
      | '0' :: (('x' | 'X') as x) :: (('0'..'9' | 'a'..'f' | 'A'..'F') as c) :: _ ->
         Stream.junk () s; Stream.junk () s; Stream.junk () s;
         true, get_buff (hex_number (store (store (store 0 '0') x) c) s)
      | _ -> false, get_buff (number 0 s) in
    assert (i <> "");
    let f =
      match hex, Stream.npeek () 2 s with
      | true, '.' :: (('0'..'9' | 'a'..'f' | 'A'..'F' | '_') as c) :: _ ->
         Stream.junk () s; Stream.junk () s; get_buff (hex_number (store 0 c) s)
      | false, '.' :: (('0'..'9' | '_') as c) :: _ ->
         Stream.junk () s; Stream.junk () s; get_buff (number (store 0 c) s)
      | _ -> "" in
    let e =
      match hex, Stream.npeek () 2 s with
      | true, (('p'|'P') as e) :: ('0'..'9' as c) :: _
      | false, (('e'|'E') as e) :: ('0'..'9' as c) :: _ ->
         Stream.junk () s; Stream.junk () s; get_buff (number (store (store 0 e) c) s)
      | true, (('p'|'P') as e) :: (('+'|'-') as sign) :: _
      | false, (('e'|'E') as e) :: (('+'|'-') as sign) :: _ ->
         begin match Stream.npeek () 3 s with
         | _ :: _ :: ('0'..'9' as c) :: _ ->
            Stream.junk () s; Stream.junk () s; Stream.junk () s;
            get_buff (number (store (store (store 0 e) sign) c) s)
         | _ -> ""
         end
      | _ -> "" in
    { int = i; frac = f; exp = e }

  let sprint n =
    n.int ^ (if n.frac = "" then "" else "." ^ n.frac) ^ n.exp

  let print n =
    Pp.str (sprint n)

  let parse_string s =
    if s = "" || s.[0] < '0' || s.[0] > '9' then None else
      let strm = Stream.of_string (s ^ "  ") in
      let n = parse strm in
      if Stream.count strm >= String.length s then Some n else None

  let of_string s =
    match parse_string s with
    | None -> assert false
    | Some s -> s

  let to_string =
    sprint (* We could remove the '_' but not necessary for float_of_string *)

  let to_nat = function
    | { int = i; frac = ""; exp = "" } -> Some i
    | _ -> None

  let is_nat = function
    | { int = _; frac = ""; exp = "" } -> true
    | _ -> false

  let classify n = UnsignedNat.classify n.int
end

open Unsigned

module Signed =
struct

  type t = sign * Unsigned.t

  let equal (s1,n1) (s2,n2) =
    s1 = s2 && equal n1 n2

  let is_zero = function
    | (SPlus,{int;frac;exp}) -> UnsignedNat.is_zero int && UnsignedNat.is_zero frac
    | _ -> false

  let of_int_frac_and_exponent (sign,int) f e =
    assert (match e with None -> true | Some e -> SignedNat.classify e = CDec);
    let c = UnsignedNat.classify int in
    let exp = match e with None -> "" | Some e ->
      let e = SignedNat.to_string e in
      match c with CDec -> "e" ^ e | CHex -> "p" ^ e in
    let frac = match f with None -> "" | Some f ->
      assert (c = UnsignedNat.classify f);
      let f = UnsignedNat.to_string f in
      match c with CDec -> f | CHex -> string_del_head 2 f in
    sign, { int; frac; exp }

  let to_int_frac_and_exponent (sign, { int; frac; exp }) =
    let e =
      if exp = "" then None else
        Some (match exp.[1] with
        | '-' -> SMinus, string_del_head 2 exp
        | '+' -> SPlus, string_del_head 2 exp
        | _ -> SPlus, string_del_head 1 exp) in
    let f =
      if frac = "" then None else
        Some (match UnsignedNat.classify int with
        | CDec -> frac
        | CHex -> "0x" ^ frac) in
    (sign, int), f, e

  let of_nat i =
    (SPlus,{ int = i; frac = ""; exp = "" })

  let of_int (s,i) =
    (s,{ int = i; frac = ""; exp = "" })

  let of_int_string s = of_int (SignedNat.of_string s)

  let to_int = function
    | (s, { int = i; frac = ""; exp = "" }) -> Some (s,i)
    | _ -> None

  let is_int n = match to_int n with None -> false | Some _ -> true

  let sprint (s,i) =
    (match s with SPlus -> "" | SMinus -> "-") ^ Unsigned.sprint i

  let print i =
    Pp.str (sprint i)

  let parse_string s =
    if s = "" || s = "-" || s = "+" ||
       (s.[0] < '0' || s.[0] > '9') && ((s.[0] <> '-' && s.[0] <> '+') || s.[1] < '0' || s.[1] > '9') then None else
      let strm = Stream.of_string (s ^ "  ") in
      let sign = match s.[0] with
        | '-' -> (Stream.junk () strm; SMinus)
        | '+' -> (Stream.junk () strm; SPlus)
        | _ -> SPlus in
      let n = parse strm in
      if Stream.count strm >= String.length s then Some (sign,n) else None

  let of_string s =
    assert (s <> "");
    let sign,u = match s.[0] with
    | '-' -> (SMinus, string_del_head 1 s)
    | '+' -> (SPlus, string_del_head 1 s)
    | _ -> (SPlus, s) in
    (sign, Unsigned.of_string u)

  let to_string (sign,u) =
    (match sign with SPlus -> "" | SMinus -> "-") ^ Unsigned.to_string u

  let to_bigint = function
    | (sign, { int = n; frac = ""; exp = "" }) ->
      Some (SignedNat.to_bigint (sign,UnsignedNat.to_string n))
    | _ -> None

  let of_bigint c n =
    of_int (SignedNat.of_bigint c n)

  let to_bigint_and_exponent (s, { int; frac; exp }) =
    let c = UnsignedNat.classify int in
    let int = UnsignedNat.to_string int in
    let frac = UnsignedNat.to_string frac in
    let i = SignedNat.to_bigint (s, int ^ frac) in
    let e =
      let e = if exp = "" then Z.zero else match exp.[1] with
      | '+' -> Z.of_string (UnsignedNat.to_string (string_del_head 2 exp))
      | '-' -> Z.(neg (of_string (UnsignedNat.to_string (string_del_head 2 exp))))
      | _ -> Z.of_string (UnsignedNat.to_string (string_del_head 1 exp)) in
      let l = String.length frac in
      let l = match c with CDec -> l | CHex -> 4 * l in
      Z.(sub e (of_int l)) in
    (i, match c with CDec -> EDec e | CHex -> EBin e)

  let of_bigint_and_exponent i e =
    let c = match e with EDec _ -> CDec | EBin _ -> CHex in
    let e = match e with EDec e | EBin e -> Some (SignedNat.of_bigint CDec e) in
    of_int_frac_and_exponent (SignedNat.of_bigint c i) None e

  let is_bigger_int_than (s, { int; frac; exp }) i =
    frac = "" && exp = "" && UnsignedNat.compare int i > 0

  let classify (_, n) = Unsigned.classify n
end
