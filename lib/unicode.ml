(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** Unicode utilities *)

type status = Letter | IdentPart | Symbol

exception Unsupported

(* The following table stores classes of Unicode characters that
   are used by the lexer. There are 3 different classes so 2 bits are
   allocated for each character. We only use 16 bits over the 31 bits
   to simplify the masking process. (This choice seems to be a good
   trade-off between speed and space after some benchmarks.) *)

(* A 256ko table, initially filled with zeros. *)
let table = Array.make (1 lsl 17) 0

(* Associate a 2-bit pattern to each status at position [i].
   Only the 3 lowest bits of [i] are taken into account to
   define the position of the pattern in the word.
   Notice that pattern "00" means "undefined". *)
let mask i = function
  | Letter    -> 1 lsl ((i land 7) lsl 1) (* 01 *)
  | IdentPart -> 2 lsl ((i land 7) lsl 1) (* 10 *)
  | Symbol    -> 3 lsl ((i land 7) lsl 1) (* 11 *)

(* Helper to reset 2 bits in a word. *)
let reset_mask i =
  lnot (3 lsl ((i land 7) lsl 1))

(* Initialize the lookup table from a list of segments, assigning
   a status to every character of each segment. The order of these
   assignments is relevant: it is possible to assign status [s] to
   a segment [(c1, c2)] and later assign [s'] to [c] even if [c] is
   between [c1] and [c2]. *)
let mk_lookup_table_from_unicode_tables_for status tables =
  List.iter
    (List.iter
       (fun (c1, c2) ->
          for i = c1 to c2 do
            table.(i lsr 3) <-
              (table.(i lsr 3) land (reset_mask i)) lor (mask i status)
          done))
    tables

(* Look up into the table and interpret the found pattern. *)
let lookup x =
  let v = (table.(x lsr 3) lsr ((x land 7) lsl 1)) land 3 in
    if      v = 1 then Letter
    else if v = 2 then IdentPart
    else if v = 3 then Symbol
    else raise Unsupported

(* [classify] discriminates between 3 different kinds of
   symbols based on the standard unicode classification (extracted from
   Camomile). *)
let classify =
  let single c = [ (c, c) ] in
    (* General tables. *)
    mk_lookup_table_from_unicode_tables_for Symbol
      [
        Unicodetable.sm;           (* Symbol, maths.                    *)
        Unicodetable.sc;           (* Symbol, currency.                 *)
        Unicodetable.so;           (* Symbol, modifier.                 *)
        Unicodetable.pd;           (* Punctation, dash.                 *)
        Unicodetable.pc;           (* Punctation, connector.            *)
        Unicodetable.pe;           (* Punctation, open.                 *)
        Unicodetable.ps;           (* Punctation, close.                *)
        Unicodetable.pi;           (* Punctation, initial quote.        *)
        Unicodetable.pf;           (* Punctation, final quote.          *)
        Unicodetable.po;           (* Punctation, other.                *)
      ];
    mk_lookup_table_from_unicode_tables_for Letter
      [
        Unicodetable.lu;           (* Letter, uppercase.                *)
        Unicodetable.ll;           (* Letter, lowercase.                *)
        Unicodetable.lt;           (* Letter, titlecase.                *)
        Unicodetable.lo;           (* Letter, others.                   *)
      ];
    mk_lookup_table_from_unicode_tables_for IdentPart
      [
        Unicodetable.nd;           (* Number, decimal digits.           *)
        Unicodetable.nl;           (* Number, letter.                   *)
        Unicodetable.no;           (* Number, other.                    *)
      ];

    (* Workaround. Some characters seems to be missing in
       Camomile's category tables. We add them manually. *)
    mk_lookup_table_from_unicode_tables_for Letter
      [
        [(0x01D00, 0x01D7F)];      (* Phonetic Extensions.              *)
        [(0x01D80, 0x01DBF)];      (* Phonetic Extensions Suppl.        *)
        [(0x01DC0, 0x01DFF)];      (* Combining Diacritical Marks Suppl.*)
      ];

    (* Exceptions (from a previous version of this function).           *)
    mk_lookup_table_from_unicode_tables_for Symbol
      [
        [(0x000B2, 0x000B3)];      (* Superscript 2-3.                  *)
        single 0x000B9;            (* Superscript 1.                    *)
        single 0x02070;            (* Superscript 0.                    *)
        [(0x02074, 0x02079)];      (* Superscript 4-9.                  *)
        single 0x0002E;            (* Dot.                              *)
      ];
    mk_lookup_table_from_unicode_tables_for Letter
      [
        single 0x005F;             (* Underscore.                       *)
        single 0x00A0;             (* Non breaking space.               *)
      ];
    mk_lookup_table_from_unicode_tables_for IdentPart
      [
        single 0x0027;             (* Special space.                    *)
      ];
    (* Lookup *)
    lookup

exception End_of_input

let utf8_of_unicode n =
  if n < 128 then
    String.make 1 (Char.chr n)
  else if n < 2048 then
    let s = String.make 2 (Char.chr (128 + n mod 64)) in
    begin
      s.[0] <- Char.chr (192 + n / 64);
      s
    end
  else if n < 65536 then
    let s = String.make 3 (Char.chr (128 + n mod 64)) in
    begin
      s.[1] <- Char.chr (128 + (n / 64) mod 64);
      s.[0] <- Char.chr (224 + n / 4096);
      s
    end
  else
    let s = String.make 4 (Char.chr (128 + n mod 64)) in
    begin
      s.[2] <- Char.chr (128 + (n / 64) mod 64);
      s.[1] <- Char.chr (128 + (n / 4096) mod 64);
      s.[0] <- Char.chr (240 + n / 262144);
      s
    end

let next_utf8 s i =
  let err () = invalid_arg "utf8" in
  let l = String.length s - i in
  if l = 0 then raise End_of_input
  else let a = Char.code s.[i] in if a <= 0x7F then
    1, a
  else if a land 0x40 = 0 || l = 1 then err ()
  else let b = Char.code s.[i+1] in if b land 0xC0 <> 0x80 then err ()
  else if a land 0x20 = 0 then
    2, (a land 0x1F) lsl 6 + (b land 0x3F)
  else if l = 2 then err ()
  else let c = Char.code s.[i+2] in if c land 0xC0 <> 0x80 then err ()
  else if a land 0x10 = 0 then
    3, (a land 0x0F) lsl 12 + (b land 0x3F) lsl 6 + (c land 0x3F)
  else if l = 3 then err ()
  else let d = Char.code s.[i+3] in if d land 0xC0 <> 0x80 then err ()
  else if a land 0x08 = 0 then
    4, (a land 0x07) lsl 18 + (b land 0x3F) lsl 12 +
       (c land 0x3F) lsl 6 + (d land 0x3F)
  else err ()

(* Check the well-formedness of an identifier *)

let initial_refutation j n s =
  match classify n with
  | Letter -> None
  | _ ->
      let c = String.sub s 0 j in
      Some (false,
            "Invalid character '"^c^"' at beginning of identifier \""^s^"\".")

let trailing_refutation i j n s =
  match classify n with
  | Letter | IdentPart -> None
  | _ ->
      let c = String.sub s i j in
      Some (false,
            "Invalid character '"^c^"' in identifier \""^s^"\".")

let ident_refutation s =
  if s = ".." then None else try
    let j, n = next_utf8 s 0 in
      match initial_refutation j n s with
        |None ->
           begin try
             let rec aux i =
               let j, n = next_utf8 s i in
                 match trailing_refutation i j n s with
                   |None -> aux (i + j)
                   |x -> x
             in aux j
           with End_of_input -> None
           end
        |x -> x
  with
  | End_of_input -> Some (true,"The empty string is not an identifier.")
  | Unsupported -> Some (true,s^": unsupported character in utf8 sequence.")
  | Invalid_argument _ -> Some (true,s^": invalid utf8 sequence.")

let lowercase_unicode =
  let tree = Segmenttree.make Unicodetable.to_lower in
  fun unicode ->
    try
      match Segmenttree.lookup unicode tree with
        | `Abs c -> c
        | `Delta d -> unicode + d
    with Not_found -> unicode

let lowercase_first_char s =
  assert (s <> "");
  let j, n = next_utf8 s 0 in
  utf8_of_unicode (lowercase_unicode n)

(** For extraction, we need to encode unicode character into ascii ones *)

let is_basic_ascii s =
  let ok = ref true in
  String.iter (fun c -> if Char.code c >= 128 then ok := false) s;
  !ok

let ascii_of_ident s =
  if is_basic_ascii s then s else
    let i = ref 0 and out = ref "" in
    begin try while true do
      let j, n = next_utf8 s !i in
      out :=
        if n >= 128
        then Printf.sprintf "%s__U%04x_" !out n
        else Printf.sprintf "%s%c" !out s.[!i];
      i := !i + j
    done with End_of_input -> () end;
    !out
