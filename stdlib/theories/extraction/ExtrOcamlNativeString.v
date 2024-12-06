(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Extraction to Ocaml : extract ascii to OCaml's char type
   and string to OCaml's string type. *)

Require Stdlib.extraction.Extraction.

Require Import Ascii String Stdlib.Strings.Byte.
Require Export ExtrOcamlChar.

(* python -c 'print(" ".join(r""" "%s" """.strip() % (r"'"'\''"'" if chr(i) == "'"'"'" else repr(""" "" """.strip()) if chr(i) == """ " """.strip() else repr(chr(i))) for i in range(256)))' # " to satisfy Coq's comment parser *)
Extract Inductive byte => char
["'\x00'" "'\x01'" "'\x02'" "'\x03'" "'\x04'" "'\x05'" "'\x06'" "'\x07'" "'\x08'" "'\t'" "'\n'" "'\x0b'" "'\x0c'" "'\r'" "'\x0e'" "'\x0f'" "'\x10'" "'\x11'" "'\x12'" "'\x13'" "'\x14'" "'\x15'" "'\x16'" "'\x17'" "'\x18'" "'\x19'" "'\x1a'" "'\x1b'" "'\x1c'" "'\x1d'" "'\x1e'" "'\x1f'" "' '" "'!'" "'""'" "'#'" "'$'" "'%'" "'&'" "'\''" "'('" "')'" "'*'" "'+'" "','" "'-'" "'.'" "'/'" "'0'" "'1'" "'2'" "'3'" "'4'" "'5'" "'6'" "'7'" "'8'" "'9'" "':'" "';'" "'<'" "'='" "'>'" "'?'" "'@'" "'A'" "'B'" "'C'" "'D'" "'E'" "'F'" "'G'" "'H'" "'I'" "'J'" "'K'" "'L'" "'M'" "'N'" "'O'" "'P'" "'Q'" "'R'" "'S'" "'T'" "'U'" "'V'" "'W'" "'X'" "'Y'" "'Z'" "'['" "'\\'" "']'" "'^'" "'_'" "'`'" "'a'" "'b'" "'c'" "'d'" "'e'" "'f'" "'g'" "'h'" "'i'" "'j'" "'k'" "'l'" "'m'" "'n'" "'o'" "'p'" "'q'" "'r'" "'s'" "'t'" "'u'" "'v'" "'w'" "'x'" "'y'" "'z'" "'{'" "'|'" "'}'" "'~'" "'\x7f'" "'\x80'" "'\x81'" "'\x82'" "'\x83'" "'\x84'" "'\x85'" "'\x86'" "'\x87'" "'\x88'" "'\x89'" "'\x8a'" "'\x8b'" "'\x8c'" "'\x8d'" "'\x8e'" "'\x8f'" "'\x90'" "'\x91'" "'\x92'" "'\x93'" "'\x94'" "'\x95'" "'\x96'" "'\x97'" "'\x98'" "'\x99'" "'\x9a'" "'\x9b'" "'\x9c'" "'\x9d'" "'\x9e'" "'\x9f'" "'\xa0'" "'\xa1'" "'\xa2'" "'\xa3'" "'\xa4'" "'\xa5'" "'\xa6'" "'\xa7'" "'\xa8'" "'\xa9'" "'\xaa'" "'\xab'" "'\xac'" "'\xad'" "'\xae'" "'\xaf'" "'\xb0'" "'\xb1'" "'\xb2'" "'\xb3'" "'\xb4'" "'\xb5'" "'\xb6'" "'\xb7'" "'\xb8'" "'\xb9'" "'\xba'" "'\xbb'" "'\xbc'" "'\xbd'" "'\xbe'" "'\xbf'" "'\xc0'" "'\xc1'" "'\xc2'" "'\xc3'" "'\xc4'" "'\xc5'" "'\xc6'" "'\xc7'" "'\xc8'" "'\xc9'" "'\xca'" "'\xcb'" "'\xcc'" "'\xcd'" "'\xce'" "'\xcf'" "'\xd0'" "'\xd1'" "'\xd2'" "'\xd3'" "'\xd4'" "'\xd5'" "'\xd6'" "'\xd7'" "'\xd8'" "'\xd9'" "'\xda'" "'\xdb'" "'\xdc'" "'\xdd'" "'\xde'" "'\xdf'" "'\xe0'" "'\xe1'" "'\xe2'" "'\xe3'" "'\xe4'" "'\xe5'" "'\xe6'" "'\xe7'" "'\xe8'" "'\xe9'" "'\xea'" "'\xeb'" "'\xec'" "'\xed'" "'\xee'" "'\xef'" "'\xf0'" "'\xf1'" "'\xf2'" "'\xf3'" "'\xf4'" "'\xf5'" "'\xf6'" "'\xf7'" "'\xf8'" "'\xf9'" "'\xfa'" "'\xfb'" "'\xfc'" "'\xfd'" "'\xfe'" "'\xff'"].

Extract Inlined Constant Byte.eqb => "(=)".
Extract Inlined Constant Byte.byte_eq_dec => "(=)".
Extract Inlined Constant Ascii.ascii_of_byte => "(fun x -> x)".
Extract Inlined Constant Ascii.byte_of_ascii => "(fun x -> x)".

(* This differs from ExtrOcamlString.v: the latter extracts "string"
   to "char list", and we extract "string" to "string" *)

Extract Inductive string => "string"
[
(* EmptyString *)
"(* If this appears, you're using String internals. Please don't *)
  """"
"
(* String *)
"(* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)
"
]
"(* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))
".

Extract Inlined Constant String.string_dec => "(=)".
Extract Inlined Constant String.eqb => "(=)".
Extract Inlined Constant String.append => "(^)".
Extract Inlined Constant String.concat => "String.concat".
Extract Inlined Constant String.prefix =>
  "(fun s1 s2 ->
     let l1 = String.length s1 and l2 = String.length s2 in
     l1 <= l2 && String.sub s2 0 l1 = s1)".
Extract Inlined Constant String.string_of_list_ascii =>
  "(fun l ->
      let a = Array.of_list l in
      String.init (Array.length a) (fun i -> a.(i)))".
Extract Inlined Constant String.list_ascii_of_string =>
  "(fun s -> List.init (String.length s) (fun i -> s.[i]))".
Extract Inlined Constant String.string_of_list_byte =>
  "(fun l ->
      let a = Array.of_list l in
      String.init (Array.length a) (fun i -> a.(i)))".
Extract Inlined Constant String.list_byte_of_string =>
  "(fun s -> List.init (String.length s) (fun i -> s.[i]))".

(* Other operations in module String (at the time of this writing):
      String.length
      String.get
      String.substring
      String.index
      String.findex
   They all use type "nat".  If we know that "nat" extracts
   to O | S of nat, we can provide OCaml implementations
   for these functions that work directly on OCaml's strings.
   However "nat" could be extracted to other OCaml types...
*)

(*
Definition test := "ceci est un test"%string.

Recursive Extraction test Ascii.zero Ascii.one.
*)
