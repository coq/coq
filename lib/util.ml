(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp

(* Errors *)

exception Anomaly of string * std_ppcmds  (* System errors *)
let anomaly string = raise (Anomaly(string, str string))
let anomalylabstrm string pps = raise (Anomaly(string,pps))

exception UserError of string * std_ppcmds (* User errors *)
let error string = raise (UserError(string, str string))
let errorlabstrm l pps = raise (UserError(l,pps))

let todo s = prerr_string ("TODO: "^s^"\n")

type loc = Compat.loc
let dummy_loc = Compat.dummy_loc
let unloc = Compat.unloc
let make_loc = Compat.make_loc
let join_loc = Compat.join_loc

(* raising located exceptions *)
type 'a located = loc * 'a
let anomaly_loc (loc,s,strm) = Stdpp.raise_with_loc loc (Anomaly (s,strm))
let user_err_loc (loc,s,strm) = Stdpp.raise_with_loc loc (UserError (s,strm))
let invalid_arg_loc (loc,s) = Stdpp.raise_with_loc loc (Invalid_argument s)

let located_fold_left f x (_,a) = f x a 
let located_iter2 f (_,a) (_,b) = f a b

(* Like Exc_located, but specifies the outermost file read, the filename
   associated to the location of the error, and the error itself. *)

exception Error_in_file of string * (bool * string * loc) * exn

(* Mapping under pairs *)

let on_fst f (a,b) = (f a,b)
let on_snd f (a,b) = (a,f b)

(* Projections from triplets *)

let pi1 (a,_,_) = a
let pi2 (_,a,_) = a
let pi3 (_,_,a) = a

(* Characters *)

let is_letter c = (c >= 'a' && c <= 'z') or (c >= 'A' && c <= 'Z')
let is_digit c = (c >= '0' && c <= '9')
let is_ident_tail c =
  is_letter c or is_digit c or c = '\'' or c = '_'

(* Strings *)

let explode s = 
  let rec explode_rec n =
    if n >= String.length s then
      []
    else 
      String.make 1 (String.get s n) :: explode_rec (succ n)
  in 
  explode_rec 0

let implode sl = String.concat "" sl

(* substring searching... *)

(* gdzie = where, co = what *)
(* gdzie=gdzie(string) gl=gdzie(length) gi=gdzie(index) *)
let rec is_sub gdzie gl gi co cl ci = 
  (ci>=cl) ||
  ((String.unsafe_get gdzie gi = String.unsafe_get co ci) && 
   (is_sub gdzie gl (gi+1) co cl (ci+1)))

let rec raw_str_index i gdzie l c co cl = 
  let i' = String.index_from gdzie i c in
    if (i'+cl <= l) && (is_sub gdzie l i' co cl 0) then i' else
      raw_str_index (i'+1) gdzie l c co cl

let string_index_from gdzie i co = 
  if co="" then i else
    raw_str_index i gdzie (String.length gdzie)
      (String.unsafe_get co 0) co (String.length co)

let string_string_contains ~where ~what =
  try
    let _ = string_index_from where 0 what in true
  with
      Not_found -> false

let plural n s = if n>1 then s^"s" else s

let ordinal n =
  let s = match n mod 10 with 1 -> "st" | 2 -> "nd" | 3 -> "rd" | _ -> "th" in
  string_of_int n ^ s

(* string parsing *)

let parse_loadpath s =
  let len = String.length s in
  let rec decoupe_dirs n =
    try  
      let pos = String.index_from s n '/' in
      if pos = n then
	invalid_arg "parse_loadpath: find an empty dir in loadpath";
      let dir = String.sub s n (pos-n) in
      dir :: (decoupe_dirs (succ pos))
    with
      | Not_found -> [String.sub s n (len-n)]
  in
  if len = 0 then [] else decoupe_dirs 0

module Stringset = Set.Make(struct type t = string let compare = compare end)

module Stringmap = Map.Make(struct type t = string let compare = compare end)

type utf8_status = UnicodeLetter | UnicodeIdentPart | UnicodeSymbol

exception UnsupportedUtf8

let classify_unicode unicode =
    match unicode land 0x1F000 with
    | 0x0 ->
    begin match unicode with
    (* utf-8 Basic Latin underscore *)
    | x when x = 0x005F -> UnicodeLetter
    (* utf-8 Basic Latin letters *)
    | x when 0x0041 <= x & x <= 0x005A -> UnicodeLetter
    | x when 0x0061 <= x & x <= 0x007A -> UnicodeLetter
    (* utf-8 Basic Latin digits and quote *)
    | x when 0x0030 <= x & x <= 0x0039 or x = 0x0027 -> UnicodeIdentPart
    (* utf-8 Basic Latin symbols *)
    | x when x <= 0x007F -> UnicodeSymbol
    (* utf-8 Latin-1 non breaking space U00A0 *)
    | 0x00A0 -> UnicodeLetter
    (* utf-8 Latin-1 symbols U00A1-00BF *)
    | x when 0x00A0 <= x & x <= 0x00BF -> UnicodeSymbol
    (* utf-8 Latin-1 letters U00C0-00D6 *)
    | x when 0x00C0 <= x & x <= 0x00D6 -> UnicodeLetter
    (* utf-8 Latin-1 symbol U00D7 *)
    | 0x00D7 -> UnicodeSymbol
    (* utf-8 Latin-1 letters U00D8-00F6 *)
    | x when 0x00D8 <= x & x <= 0x00F6 -> UnicodeLetter
    (* utf-8 Latin-1 symbol U00F7 *)
    | 0x00F7 -> UnicodeSymbol
    (* utf-8 Latin-1 letters U00F8-00FF *)
    | x when 0x00F8 <= x & x <= 0x00FF -> UnicodeLetter
    (* utf-8 Latin Extended A U0100-017F and Latin Extended B U0180-U0241 *)
    | x when 0x0100 <= x & x <= 0x0241 -> UnicodeLetter
    (* utf-8 Phonetic letters U0250-02AF *)
    | x when 0x0250 <= x & x <= 0x02AF -> UnicodeLetter
    (* utf-8 what do to with diacritics U0300-U036F ? *)
    (* utf-8 Greek letters U0380-03FF *)
    | x when 0x0380 <= x & x <= 0x03FF -> UnicodeLetter
    (* utf-8 Cyrillic letters U0400-0481 *)
    | x when 0x0400 <= x & x <= 0x0481 -> UnicodeLetter
    (* utf-8 Cyrillic symbol U0482 *)
    | 0x0482 -> UnicodeSymbol
    (* utf-8 what do to with diacritics U0483-U0489 \ U0487 ? *)
    (* utf-8 Cyrillic letters U048A-U4F9 (Warning: 04CF) *)
    | x when 0x048A <= x & x <= 0x04F9 -> UnicodeLetter
    (* utf-8 Cyrillic supplement letters U0500-U050F *)
    | x when 0x0500 <= x & x <= 0x050F -> UnicodeLetter
    (* utf-8 Hebrew letters U05D0-05EA *)
    | x when 0x05D0 <= x & x <= 0x05EA -> UnicodeLetter
    (* utf-8 Arabic letters U0621-064A *)
    | x when 0x0621 <= x & x <= 0x064A -> UnicodeLetter
    (* utf-8 Arabic supplement letters U0750-076D *)
    | x when 0x0750 <= x & x <= 0x076D -> UnicodeLetter
    | _ -> raise UnsupportedUtf8
    end
    | 0x1000 ->
    begin match unicode with
    (* utf-8 Georgian U10A0-10FF (has holes) *)
    | x when 0x10A0 <= x & x <= 0x10FF -> UnicodeLetter
    (* utf-8 Hangul Jamo U1100-11FF (has holes) *)
    | x when 0x1100 <= x & x <= 0x11FF -> UnicodeLetter
    (* utf-8 Latin additional letters U1E00-1E9B and U1EA0-1EF9 *)
    | x when 0x1E00 <= x & x <= 0x1E9B -> UnicodeLetter
    | x when 0x1EA0 <= x & x <= 0x1EF9 -> UnicodeLetter
    | _ -> raise UnsupportedUtf8
    end
    | 0x2000 ->
    begin match unicode with
    (* utf-8 general punctuation U2080-2089 *)
    (* Hyphens *)
    | x when 0x2010 <= x & x <= 0x2011 -> UnicodeLetter 
    (* Dashes and other symbols *)
    | x when 0x2012 <= x & x <= 0x2027 -> UnicodeSymbol
    (* Per mille and per ten thousand signs *)
    | x when 0x2030 <= x & x <= 0x2031 -> UnicodeSymbol
    (* Prime letters *)
    | x when 0x2032 <= x & x <= 0x2034 or x = 0x2057 -> UnicodeIdentPart
    (* Miscellaneous punctuation *)
    | x when 0x2039 <= x & x <= 0x2056 -> UnicodeSymbol
    | x when 0x2058 <= x & x <= 0x205E -> UnicodeSymbol
    (* Invisible mathematical operators *)
    | x when 0x2061 <= x & x <= 0x2063 -> UnicodeSymbol
    (* utf-8 superscript U2070-207C *) 
    | x when 0x2070 <= x & x <= 0x207C -> UnicodeSymbol
    (* utf-8 subscript U2080-2089 *) 
    | x when 0x2080 <= x & x <= 0x2089 -> UnicodeIdentPart
    (* utf-8 letter-like U2100-214F *)
    | x when 0x2100 <= x & x <= 0x214F -> UnicodeLetter
    (* utf-8 number-forms U2153-2183 *)
    | x when 0x2153 <= x & x <= 0x2183 -> UnicodeSymbol
    (* utf-8 arrows A U2190-21FF *)
    (* utf-8 mathematical operators U2200-22FF *)
    (* utf-8 miscellaneous technical U2300-23FF *)
    | x when 0x2190 <= x & x <= 0x23FF -> UnicodeSymbol
    (* utf-8 box drawing U2500-257F has ceiling, etc. *)
    (* utf-8 block elements U2580-259F *)
    (* utf-8 geom. shapes U25A0-25FF (has triangles, losange, etc) *)
    (* utf-8 miscellaneous symbols U2600-26FF *)
    | x when 0x2500 <= x & x <= 0x26FF -> UnicodeSymbol
    (* utf-8 arrows B U2900-297F *)
    | x when 0x2900 <= x & x <= 0x297F -> UnicodeSymbol
    (* utf-8 mathematical operators U2A00-2AFF *)
    | x when 0x2A00 <= x & x <= 0x2AFF -> UnicodeSymbol
    (* utf-8 bold symbols U2768-U2775 *)
    | x when 0x2768 <= x & x <= 0x2775 -> UnicodeSymbol
    (* utf-8 arrows and brackets U27E0-U27FF *)
    | x when 0x27E0 <= x & x <= 0x27FF -> UnicodeSymbol
    (* utf-8 brackets, braces and parentheses *)
    | x when 0x2980 <= x & x <= 0x299F -> UnicodeSymbol
    (* utf-8 miscellaneous including double-plus U29F0-U29FF *)
    | x when 0x29F0 <= x & x <= 0x29FF -> UnicodeSymbol
    | _ -> raise UnsupportedUtf8
    end
    | _ ->
    begin match unicode with
    (* utf-8 Hiragana U3040-309F and Katakana U30A0-30FF *)
    | x when 0x3040 <= x & x <= 0x30FF -> UnicodeLetter
    (* utf-8 Unified CJK Ideographs U4E00-9FA5 *)
    | x when 0x4E00 <= x & x <= 0x9FA5 -> UnicodeLetter
    (* utf-8 Hangul syllables UAC00-D7AF *)
    | x when 0xAC00 <= x & x <= 0xD7AF -> UnicodeLetter
    (* utf-8 Gothic U10330-1034A *)
    | x when 0x10330 <= x & x <= 0x1034A -> UnicodeLetter
    (* utf-8 Math Alphanumeric Symbols U1D400-1D7FF (letters) (has holes) *)
    | x when 0x1D400 <= x & x <= 0x1D7CB -> UnicodeLetter
    (* utf-8 Math Alphanumeric Symbols U1D400-1D7FF (digits) *)
    | x when 0x1D7CE <= x & x <= 0x1D7FF -> UnicodeIdentPart
    | _ -> raise UnsupportedUtf8
    end

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
  else if a land 0x40 = 0 or l = 1 then err ()
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

let check_ident s =
  let i = ref 0 in
  if s <> ".." then try
    let j, n = next_utf8 s 0 in
    match classify_unicode n with
    | UnicodeLetter ->
	i := !i + j;
	begin try
	  while true do
	    let j, n = next_utf8 s !i in
	    match classify_unicode n with
	    | UnicodeLetter | UnicodeIdentPart -> i := !i + j
	    | _ -> error
		("invalid character "^(String.sub s !i j)^" in identifier "^s)
	  done
	with End_of_input -> () end
    | _ -> error (s^": an identifier should start with a letter")
  with 
  | End_of_input -> error "The empty string is not an identifier"
  | UnsupportedUtf8 -> error (s^": unsupported character in utf8 sequence")
  | Invalid_argument _ -> error (s^": invalid utf8 sequence")

let lowercase_unicode s unicode =
    match unicode land 0x1F000 with
    | 0x0 ->
    begin match unicode with
    (* utf-8 Basic Latin underscore *)
    | x when x = 0x005F -> x
    (* utf-8 Basic Latin letters *)
    | x when 0x0041 <= x & x <= 0x005A -> x + 32
    | x when 0x0061 <= x & x <= 0x007A -> x
    (* utf-8 Latin-1 non breaking space U00A0 *)
    | 0x00A0 as x -> x
    (* utf-8 Latin-1 letters U00C0-00D6 *)
    | x when 0x00C0 <= x & x <= 0x00D6 -> x + 32
    (* utf-8 Latin-1 letters U00D8-00F6 *)
    | x when 0x00D8 <= x & x <= 0x00DE -> x + 32
    | x when 0x00E0 <= x & x <= 0x00F6 -> x
    (* utf-8 Latin-1 letters U00F8-00FF *)
    | x when 0x00F8 <= x & x <= 0x00FF -> x
    (* utf-8 Latin Extended A U0100-017F and Latin Extended B U0180-U0241 *)
    | x when 0x0100 <= x & x <= 0x017F ->
	if x mod 2 = 1 then x else x + 1
    | x when 0x0180 <= x & x <= 0x0241 ->
	warning ("Unable to decide which lowercase letter to map to "^s); x
    (* utf-8 Phonetic letters U0250-02AF *)
    | x when 0x0250 <= x & x <= 0x02AF -> x
    (* utf-8 what do to with diacritics U0300-U036F ? *)
    (* utf-8 Greek letters U0380-03FF *)
    | x when 0x0380 <= x & x <= 0x0385 -> x
    | 0x0386 -> 0x03AC
    | x when 0x0388 <= x & x <= 0x038A -> x + 37
    | 0x038C -> 0x03CC
    | x when 0x038E <= x & x <= 0x038F -> x + 63
    | x when 0x0390 <= x & x <= 0x03AB & x <> 0x03A2 -> x + 32
    (* utf-8 Greek lowercase letters U03B0-03CE *)	
    | x when 0x03AC <= x & x <= 0x03CE -> x
    | x when 0x03CF <= x & x <= 0x03FF ->
	warning ("Unable to decide which lowercase letter to map to "^s); x
    (* utf-8 Cyrillic letters U0400-0481 *)
    | x when 0x0400 <= x & x <= 0x040F -> x + 80
    | x when 0x0410 <= x & x <= 0x042F -> x + 32
    | x when 0x0430 <= x & x <= 0x045F -> x 
    | x when 0x0460 <= x & x <= 0x0481 ->
	if x mod 2 = 1 then x else x + 1
    (* utf-8 Cyrillic letters U048A-U4F9 (Warning: 04CF) *)
    | x when 0x048A <= x & x <= 0x04F9 & x <> 0x04CF -> 
	if x mod 2 = 1 then x else x + 1
    (* utf-8 Cyrillic supplement letters U0500-U050F *)
    | x when 0x0500 <= x & x <= 0x050F ->
	if x mod 2 = 1 then x else x + 1
    (* utf-8 Hebrew letters U05D0-05EA *)
    | x when 0x05D0 <= x & x <= 0x05EA -> x
    (* utf-8 Arabic letters U0621-064A *)
    | x when 0x0621 <= x & x <= 0x064A -> x
    (* utf-8 Arabic supplement letters U0750-076D *)
    | x when 0x0750 <= x & x <= 0x076D -> x
    | _ -> raise UnsupportedUtf8
    end
    | 0x1000 ->
    begin match unicode with
    (* utf-8 Georgian U10A0-10FF (has holes) *)
    | x when 0x10A0 <= x & x <= 0x10FF -> x
    (* utf-8 Hangul Jamo U1100-11FF (has holes) *)
    | x when 0x1100 <= x & x <= 0x11FF -> x
    (* utf-8 Latin additional letters U1E00-1E9B and U1EA0-1EF9 *)
    | x when 0x1E00 <= x & x <= 0x1E95 ->
	if x mod 2 = 1 then x else x + 1
    | x when 0x1E96 <= x & x <= 0x1E9B -> x
    | x when 0x1EA0 <= x & x <= 0x1EF9 ->
	if x mod 2 = 1 then x else x + 1
    | _ -> raise UnsupportedUtf8
    end
    | 0x2000 ->
    begin match unicode with
    (* utf-8 general punctuation U2080-2089 *)
    (* Hyphens *)
    | x when 0x2010 <= x & x <= 0x2011 -> x
    (* utf-8 letter-like U2100-214F *)
    | 0x2102 (* double-struck C *) -> Char.code 'x'
    | 0x2115 (* double-struck N *) -> Char.code 'n'
    | 0x2119 (* double-struck P *) -> Char.code 'x'
    | 0x211A (* double-struck Q *) -> Char.code 'x'
    | 0x211D (* double-struck R *) -> Char.code 'r'
    | 0x2124 (* double-struck Z *) -> Char.code 'x'
    | x when 0x2100 <= x & x <= 0x214F ->
	warning ("Unable to decide which lowercase letter to map to "^s); x
    | _ -> raise UnsupportedUtf8
    end
    | _ ->
    begin match unicode with
    (* utf-8 Hiragana U3040-309F and Katakana U30A0-30FF *)
    | x when 0x3040 <= x & x <= 0x30FF -> x
    (* utf-8 Unified CJK Ideographs U4E00-9FA5 *)
    | x when 0x4E00 <= x & x <= 0x9FA5 -> x
    (* utf-8 Hangul syllables UAC00-D7AF *)
    | x when 0xAC00 <= x & x <= 0xD7AF -> x
    (* utf-8 Gothic U10330-1034A *)
    | x when 0x10330 <= x & x <= 0x1034A -> x
    (* utf-8 Math Alphanumeric Symbols U1D400-1D7FF (letters) (has holes) *)
    | x when 0x1D6A8 <= x & x <= 0x1D7C9 ->
        let a = (x - 0x1D6A8) mod 58 in
        if a <= 16 or (18 <= a & a <= 24)
        then x + 26 (* all but nabla and theta symbol *)
        else x
    | x when 0x1D538 <= x & x <= 0x1D56B ->
        (* Use ordinary lowercase in both small and capital double-struck *)
        (x - 0x1D538) mod 26 + Char.code 'a'
    | x when 0x1D468 <= x & x <= 0x1D6A3 -> (* General case *)
        if (x - 0x1D400 / 26) mod 2 = 0 then x + 26 else x
    | x when 0x1D400 <= x & x <= 0x1D7CB -> (* fallback *)
        x
    (* utf-8 Math Alphanumeric Symbols U1D400-1D7FF (digits) *)
    | x when 0x1D7CE <= x & x <= 0x1D7FF -> x
    | _ -> raise UnsupportedUtf8
    end

let lowercase_first_char_utf8 s =
  assert (s <> "");
  let j, n = next_utf8 s 0 in
  utf8_of_unicode (lowercase_unicode (String.sub s 0 j) n)

(* Lists *)

let list_intersect l1 l2 = 
  List.filter (fun x -> List.mem x l2) l1

let list_union l1 l2 = 
  let rec urec = function
    | [] -> l2
    | a::l -> if List.mem a l2 then urec l else a::urec l
  in 
  urec l1

let list_unionq l1 l2 = 
  let rec urec = function
    | [] -> l2
    | a::l -> if List.memq a l2 then urec l else a::urec l
  in 
  urec l1

let list_subtract l1 l2 =
  if l2 = [] then l1 else List.filter (fun x -> not (List.mem x l2)) l1

let list_subtractq l1 l2 = 
  if l2 = [] then l1 else List.filter (fun x -> not (List.memq x l2)) l1

let list_chop n l = 
  let rec chop_aux acc = function
    | (0, l2) -> (List.rev acc, l2)
    | (n, (h::t)) -> chop_aux (h::acc) (pred n, t)
    | (_, []) -> failwith "list_chop"
  in 
  chop_aux [] (n,l)

let list_tabulate f len = 
  let rec tabrec n =
    if n = len then [] else (f n)::(tabrec (n+1))
  in 
  tabrec 0

let list_assign l n e = 
  let rec assrec stk = function
    | ((h::t), 0) -> List.rev_append stk (e::t)
    | ((h::t), n) -> assrec (h::stk) (t, n-1)
    | ([], _) -> failwith "list_assign"
  in 
  assrec [] (l,n)

let rec list_smartmap f l = match l with
    [] -> l
  | h::tl -> 
      let h' = f h and tl' = list_smartmap f tl in
	if h'==h && tl'==tl then l
	else h'::tl'

let list_map_left f = (* ensures the order in case of side-effects *)
  let rec map_rec = function
    | [] -> [] 
    | x::l -> let v = f x in v :: map_rec l
  in 
  map_rec

let list_map_i f = 
  let rec map_i_rec i = function
    | [] -> [] 
    | x::l -> let v = f i x in v :: map_i_rec (i+1) l
  in 
  map_i_rec

let list_map2_i f i l1 l2 =  
  let rec map_i i = function
    | ([], []) -> []
    | ((h1::t1), (h2::t2)) -> let v = f i h1 h2 in v :: map_i (succ i) (t1,t2)
    | (_, _) -> invalid_arg "map2_i"
  in 
  map_i i (l1,l2)

let list_map3 f l1 l2 l3 =
  let rec map = function
    | ([], [], []) -> []
    | ((h1::t1), (h2::t2), (h3::t3)) -> let v = f h1 h2 h3 in v::map (t1,t2,t3)
    | (_, _, _) -> invalid_arg "map3"
  in 
  map (l1,l2,l3)

let list_map4 f l1 l2 l3 l4 =
  let rec map = function
    | ([], [], [], []) -> []
    | ((h1::t1), (h2::t2), (h3::t3), (h4::t4)) -> let v = f h1 h2 h3 h4 in v::map (t1,t2,t3,t4)
    | (_, _, _, _) -> invalid_arg "map4"
  in 
  map (l1,l2,l3,l4)

let list_index x = 
  let rec index_x n = function
    | y::l -> if x = y then n else index_x (succ n) l
    | [] -> raise Not_found
  in 
  index_x 1

let list_index0 x l = list_index x l - 1 

let list_unique_index x = 
  let rec index_x n = function
    | y::l -> 
	if x = y then 
	  if List.mem x l then raise Not_found
	  else n 
	else index_x (succ n) l
    | [] -> raise Not_found 
  in index_x 1

let list_fold_right_i f i l =
  let rec it_list_f i l a = match l with
    | [] -> a
    | b::l -> f (i-1) b (it_list_f (i-1) l a)
  in 
  it_list_f (List.length l + i) l

let list_fold_left_i f = 
  let rec it_list_f i a = function
    | [] -> a 
    | b::l -> it_list_f (i+1) (f i a b) l
  in 
  it_list_f 

(* [list_fold_right_and_left f [a1;...;an] hd =
   f (f (... (f (f hd
                   an
                   [an-1;...;a1])
              an-1
              [an-2;...;a1])
         ...)
        a2
        [a1])
     a1
     []] *)

let rec list_fold_right_and_left f l hd =
  let rec aux tl = function
    | [] -> hd
    | a::l -> let hd = aux (a::tl) l in f hd a tl
   in aux [] l

let list_iter3 f l1 l2 l3 =
  let rec iter = function
    | ([], [], []) -> ()
    | ((h1::t1), (h2::t2), (h3::t3)) -> f h1 h2 h3; iter (t1,t2,t3)
    | (_, _, _) -> invalid_arg "map3"
  in 
  iter (l1,l2,l3)

let list_iter_i f l = list_fold_left_i (fun i _ x -> f i x) 0 () l

let list_for_all_i p = 
  let rec for_all_p i = function
    | [] -> true 
    | a::l -> p i a && for_all_p (i+1) l
  in 
  for_all_p

let list_except x l = List.filter (fun y -> not (x = y)) l

let list_remove = list_except (* Alias *)

let rec list_remove_first a = function
  | b::l when a = b -> l
  | b::l -> b::list_remove_first a l
  | [] -> raise Not_found

let list_add_set x l = if List.mem x l then l else x::l

let list_eq_set l1 l2 =
  let rec aux l1 = function
  | [] -> l1 = []
  | a::l2 -> aux (list_remove_first a l1) l2 in
  try aux l1 l2 with Not_found -> false

let list_for_all2eq f l1 l2 = try List.for_all2 f l1 l2 with Failure _ -> false

let list_map_i f = 
  let rec map_i_rec i = function
    | [] -> [] 
    | x::l -> let v = f i x in v::map_i_rec (i+1) l
  in 
  map_i_rec

let rec list_sep_last = function
  | [] -> failwith "sep_last"
  | hd::[] -> (hd,[])
  | hd::tl -> let (l,tl) = list_sep_last tl in (l,hd::tl)

let list_try_find_i f = 
  let rec try_find_f n = function
    | [] -> failwith "try_find_i"
    | h::t -> try f n h with Failure _ -> try_find_f (n+1) t
  in 
  try_find_f

let list_try_find f = 
  let rec try_find_f = function
    | [] -> failwith "try_find"
    | h::t -> try f h with Failure _ -> try_find_f t
  in 
  try_find_f

let list_uniquize l =
  let visited = Hashtbl.create 23 in
  let rec aux acc = function
    | h::t -> if Hashtbl.mem visited h then aux acc t else
	  begin
	    Hashtbl.add visited h h;
	    aux (h::acc) t
	  end
    | [] -> List.rev acc
  in aux [] l

let rec list_distinct l = 
  let visited = Hashtbl.create 23 in
  let rec loop = function
    | h::t ->
	if Hashtbl.mem visited h then false
	else 
	  begin
	    Hashtbl.add visited h h;
	    loop t
	  end
    | [] -> true
  in loop l

let rec list_merge_uniq cmp l1 l2 =
  match l1, l2 with
  | [], l2 -> l2
  | l1, [] -> l1
  | h1 :: t1, h2 :: t2 ->
      let c = cmp h1 h2 in 
      if c = 0 
      then h1 :: list_merge_uniq cmp t1 t2
      else if c <= 0 
      then h1 :: list_merge_uniq cmp t1 l2
      else h2 :: list_merge_uniq cmp l1 t2

let rec list_duplicates = function
  | [] -> []
  | x::l ->
      let l' = list_duplicates l in
      if List.mem x l then list_add_set x l' else l'

let rec list_filter2 f = function
  | [], [] as p -> p
  | d::dp, l::lp ->
     let (dp',lp' as p) = list_filter2 f (dp,lp) in
      if f d l then d::dp', l::lp' else p
  | _ -> invalid_arg "list_filter2"

let list_subset l1 l2 =
  let t2 = Hashtbl.create 151 in
  List.iter (fun x -> Hashtbl.add t2 x ()) l2;
  let rec look = function
    | [] -> true
    | x::ll -> try Hashtbl.find t2 x; look ll with Not_found -> false
  in 
  look l1

let list_splitby p = 
  let rec splitby_loop x y = 
    match y with 
      | []      -> ([],[])
      | (a::l)  -> if (p a) then (x,y) else (splitby_loop (x@[a]) l)
  in 
  splitby_loop []

let rec list_split3 = function
  | [] -> ([], [], [])
  | (x,y,z)::l ->
      let (rx, ry, rz) = list_split3 l in (x::rx, y::ry, z::rz)

let rec list_insert_in_class f a = function
  | [] -> [[a]]
  | (b::_ as l)::classes when f a b -> (a::l)::classes
  | l::classes -> l :: list_insert_in_class f a classes

let list_partition_by f l =
  List.fold_right (list_insert_in_class f) l []

let list_firstn n l =
  let rec aux acc = function
    | (0, l) -> List.rev acc
    | (n, (h::t)) -> aux (h::acc) (pred n, t)
    | _ -> failwith "firstn"
  in 
  aux [] (n,l)

let rec list_last = function
  | [] -> failwith "list_last"
  | [x] -> x
  | _ :: l -> list_last l

let list_lastn n l =
  let len = List.length l in
  let rec aux m l =
    if m = n then l else aux (m - 1) (List.tl l)
  in
  if len < n then failwith "lastn" else aux len l

let rec list_skipn n l = match n,l with 
  | 0, _ -> l 
  | _, [] -> failwith "list_fromn"
  | n, _::l -> list_skipn (pred n) l

let rec list_addn n x l = 
  if n = 0 then l else x :: (list_addn (pred n) x l)

let list_prefix_of prefl l = 
  let rec prefrec = function
    | (h1::t1, h2::t2) -> h1 = h2 && prefrec (t1,t2)
    | ([], _) -> true
    | (_, _) -> false
  in 
    prefrec (prefl,l)

let list_drop_prefix p l =
(* if l=p++t then return t else l *)
  let rec list_drop_prefix_rec = function
    | ([], tl) -> Some tl
    | (_, []) -> None
    | (h1::tp, h2::tl) -> 
	if h1 = h2 then list_drop_prefix_rec (tp,tl) else None
  in
    match list_drop_prefix_rec (p,l) with
      | Some r -> r
      | None -> l

let list_map_append f l = List.flatten (List.map f l)
let list_join_map = list_map_append   (* Alias *)

let list_map_append2 f l1 l2 = List.flatten (List.map2 f l1 l2)

let list_share_tails l1 l2 =
  let rec shr_rev acc = function
    | ((x1::l1), (x2::l2)) when x1 == x2 -> shr_rev (x1::acc) (l1,l2)
    | (l1,l2) -> (List.rev l1, List.rev l2, acc)
  in 
  shr_rev [] (List.rev l1, List.rev l2)

let rec list_fold_map f e = function
  |  []  -> (e,[])
  |  h::t ->
       let e',h' = f e h in
       let e'',t' = list_fold_map f e' t in
         e'',h'::t'

(* (* tail-recursive version of the above function *)
let list_fold_map f e l = 
  let g (e,b') h = 
    let (e',h') = f e h in
      (e',h'::b') 
  in
  let (e',lrev) = List.fold_left g (e,[]) l in
    (e',List.rev lrev)
*)

(* The same, based on fold_right, with the effect accumulated on the right *)
let list_fold_map' f l e =
  List.fold_right (fun x (l,e) -> let (y,e) = f x e in (y::l,e)) l ([],e)

let list_map_assoc f = List.map (fun (x,a) -> (x,f a))

(* Specification:
   - =p= is set equality (double inclusion)
   - f such that \forall l acc, (f l acc) =p= append (f l []) acc
   - let g = fun x -> f x [] in
   - union_map f l acc =p= append (flatten (map g l)) acc
 *)
let list_union_map f l acc =
  List.fold_left
    (fun x y -> f y x)
    acc
    l

(* A generic cartesian product: for any operator (**), 
   [list_cartesian (**) [x1;x2] [y1;y2] = [x1**y1; x1**y2; x2**y1; x2**y1]], 
   and so on if there are more elements in the lists. *)

let rec list_cartesian op l1 l2 = 
  list_map_append (fun x -> List.map (op x) l2) l1

(* [list_cartesians] is an n-ary cartesian product: it iterates 
   [list_cartesian] over a list of lists.  *)

let list_cartesians op init ll = 
  List.fold_right (list_cartesian op) ll [init]

(* list_combinations [[a;b];[c;d]] gives [[a;c];[a;d];[b;c];[b;d]] *)

let list_combinations l = list_cartesians (fun x l -> x::l) [] l

(* Arrays *)

let array_exists f v = 
  let rec exrec = function
    | -1 -> false
    | n -> (f v.(n)) || (exrec (n-1))
  in 
  exrec ((Array.length v)-1) 

let array_for_all f v = 
  let rec allrec = function
    | -1 -> true
    | n -> (f v.(n)) && (allrec (n-1))
  in 
  allrec ((Array.length v)-1) 

let array_for_all2 f v1 v2 =
  let rec allrec = function
    | -1 -> true
    | n -> (f v1.(n) v2.(n)) && (allrec (n-1))
  in 
  let lv1 = Array.length v1 in
  lv1 = Array.length v2 && allrec (pred lv1) 

let array_for_all3 f v1 v2 v3 =
  let rec allrec = function
    | -1 -> true
    | n -> (f v1.(n) v2.(n) v3.(n)) && (allrec (n-1))
  in 
  let lv1 = Array.length v1 in
  lv1 = Array.length v2 && lv1 = Array.length v3 && allrec (pred lv1) 

let array_for_all4 f v1 v2 v3 v4 =
  let rec allrec = function
    | -1 -> true
    | n -> (f v1.(n) v2.(n) v3.(n) v4.(n)) && (allrec (n-1))
  in 
  let lv1 = Array.length v1 in
  lv1 = Array.length v2 &&
  lv1 = Array.length v3 &&
  lv1 = Array.length v4 &&
    allrec (pred lv1) 

let array_hd v = 
  match Array.length v with
    | 0 -> failwith "array_hd"
    | _ -> v.(0)

let array_tl v = 
  match Array.length v with
    | 0 -> failwith "array_tl"
    | n -> Array.sub v 1 (pred n)

let array_last v =
  match Array.length v with
    | 0 -> failwith "array_last"
    | n -> v.(pred n)

let array_cons e v = Array.append [|e|] v

let array_rev t = 
  let n=Array.length t in
    if n <=0 then () 
    else
      let tmp=ref t.(0) in
      for i=0 to pred (n/2) do 
	tmp:=t.((pred n)-i);
	t.((pred n)-i)<- t.(i);
	t.(i)<- !tmp
      done

let array_fold_right_i f v a =
  let rec fold a n =
    if n=0 then a
    else
      let k = n-1 in
      fold (f k v.(k) a) k in
  fold a (Array.length v)

let array_fold_left_i f v a =
  let n = Array.length a in
  let rec fold i v = if i = n then v else fold (succ i) (f i v a.(i)) in
  fold 0 v

let array_fold_right2 f v1 v2 a =
  let lv1 = Array.length v1 in
  let rec fold a n =
    if n=0 then a
    else
      let k = n-1 in
      fold (f v1.(k) v2.(k) a) k in
  if Array.length v2 <> lv1 then invalid_arg "array_fold_right2";
  fold a lv1

let array_fold_left2 f a v1 v2 =
  let lv1 = Array.length v1 in
  let rec fold a n = 
    if n >= lv1 then a else fold (f a v1.(n) v2.(n)) (succ n)
  in
  if Array.length v2 <> lv1 then invalid_arg "array_fold_left2";
  fold a 0

let array_fold_left2_i f a v1 v2 =
  let lv1 = Array.length v1 in
  let rec fold a n = 
    if n >= lv1 then a else fold (f n a v1.(n) v2.(n)) (succ n)
  in
  if Array.length v2 <> lv1 then invalid_arg "array_fold_left2";
  fold a 0

let array_fold_left_from n f a v = 
  let rec fold a n =
    if n >= Array.length v then a else fold (f a v.(n)) (succ n)
  in 
  fold a n

let array_fold_right_from n f v a = 
  let rec fold n =
    if n >= Array.length v then a else f v.(n) (fold (succ n))
  in 
  fold n

let array_app_tl v l = 
  if Array.length v = 0 then invalid_arg "array_app_tl";
  array_fold_right_from 1 (fun e l -> e::l) v l

let array_list_of_tl v =
  if Array.length v = 0 then invalid_arg "array_list_of_tl";
  array_fold_right_from 1 (fun e l -> e::l) v []

let array_map_to_list f v =
  List.map f (Array.to_list v)

let array_chop n v =
  let vlen = Array.length v in
  if n > vlen then failwith "array_chop";
  (Array.sub v 0 n, Array.sub v n (vlen-n))

exception Local of int

(* If none of the elements is changed by f we return ar itself.
   The for loop looks for the first such an element.
   If found it is temporarily stored in a ref and the new array is produced, 
   but f is not re-applied to elements that are already checked *)
let array_smartmap f ar = 
  let ar_size = Array.length ar in
  let aux = ref None in
  try
    for i = 0 to ar_size-1 do
      let a = ar.(i) in
      let a' = f a in
	if a != a' then (* pointer (in)equality *) begin
	  aux := Some a';
	  raise (Local i)
	end
    done;
    ar
  with
      Local i -> 
	let copy j = 
	  if j<i then ar.(j) 
	  else if j=i then 
	    match !aux with Some a' -> a' | None -> failwith "Error"
	  else f (ar.(j))
	in
	  Array.init ar_size copy

let array_map2 f v1 v2 =
  if Array.length v1 <> Array.length v2 then invalid_arg "array_map2";
  if Array.length v1 == 0 then 
    [| |] 
  else begin
    let res = Array.create (Array.length v1) (f v1.(0) v2.(0)) in
    for i = 1 to pred (Array.length v1) do
      res.(i) <- f v1.(i) v2.(i)
    done;
    res
  end

let array_map2_i f v1 v2 =
  if Array.length v1 <> Array.length v2 then invalid_arg "array_map2";
  if Array.length v1 == 0 then 
    [| |] 
  else begin
    let res = Array.create (Array.length v1) (f 0 v1.(0) v2.(0)) in
    for i = 1 to pred (Array.length v1) do
      res.(i) <- f i v1.(i) v2.(i)
    done;
    res
  end

let array_map3 f v1 v2 v3 =
  if Array.length v1 <> Array.length v2 ||
     Array.length v1 <> Array.length v3 then invalid_arg "array_map3";
  if Array.length v1 == 0 then 
    [| |] 
  else begin
    let res = Array.create (Array.length v1) (f v1.(0) v2.(0) v3.(0)) in
    for i = 1 to pred (Array.length v1) do
      res.(i) <- f v1.(i) v2.(i) v3.(i)
    done;
    res
  end

let array_map_left f a = (* Ocaml does not guarantee Array.map is LR *)
  let l = Array.length a in (* (even if so), then we rewrite it *)
  if l = 0 then [||] else begin
    let r = Array.create l (f a.(0)) in
    for i = 1 to l - 1 do
      r.(i) <- f a.(i)
    done;
    r
  end

let array_map_left_pair f a g b =
  let l = Array.length a in
  if l = 0 then [||],[||] else begin
    let r = Array.create l (f a.(0)) in
    let s = Array.create l (g b.(0)) in
    for i = 1 to l - 1 do
      r.(i) <- f a.(i);
      s.(i) <- g b.(i)
    done;
    r, s
  end

let array_iter2 f v1 v2 =
  let n = Array.length v1 in
  if Array.length v2 <> n then invalid_arg "array_iter2"
  else for i = 0 to n - 1 do f v1.(i) v2.(i) done

let pure_functional = false

let array_fold_map' f v e =
if pure_functional then
  let (l,e) =
    Array.fold_right 
      (fun x (l,e) -> let (y,e) = f x e in (y::l,e))
      v ([],e) in
  (Array.of_list l,e)
else
  let e' = ref e in
  let v' = Array.map (fun x -> let (y,e) = f x !e' in e' := e; y) v in
  (v',!e')

let array_fold_map f e v =
  let e' = ref e in
  let v' = Array.map (fun x -> let (e,y) = f !e' x in e' := e; y) v in
  (!e',v')

let array_fold_map2' f v1 v2 e =
  let e' = ref e in
  let v' = 
    array_map2 (fun x1 x2 -> let (y,e) = f x1 x2 !e' in e' := e; y) v1 v2 
  in
  (v',!e')

let array_distinct v =
  try
    for i=0 to Array.length v-1 do
      for j=i+1 to Array.length v-1 do
	if v.(i)=v.(j) then raise Exit
      done
    done;
    true
  with Exit ->
    false

let array_union_map f a acc =
  Array.fold_left
    (fun x y -> f y x)
    acc
    a

(* Matrices *)

let matrix_transpose mat =
  List.fold_right (List.map2 (fun p c -> p::c)) mat
    (if mat = [] then [] else List.map (fun _ -> []) (List.hd mat))

(* Functions *)

let identity x = x

let compose f g x = f (g x)

let iterate f = 
  let rec iterate_f n x =
    if n <= 0 then x else iterate_f (pred n) (f x)
  in 
  iterate_f

let repeat n f x =
  for i = 1 to n do f x done

let iterate_for a b f x =
  let rec iterate i v = if i > b then v else iterate (succ i) (f i v) in
  iterate a x
 
(* Misc *)

type ('a,'b) union = Inl of 'a | Inr of 'b

module Intset = Set.Make(struct type t = int let compare = compare end)

module Intmap = Map.Make(struct type t = int let compare = compare end)

let intmap_in_dom x m =
  try let _ = Intmap.find x m in true with Not_found -> false

let intmap_to_list m = Intmap.fold (fun n v l -> (n,v)::l) m []

let intmap_inv m b = Intmap.fold (fun n v l -> if v = b then n::l else l) m []

let interval n m = 
  let rec interval_n (l,m) =
    if n > m then l else interval_n (m::l,pred m)
  in 
  interval_n ([],m)


let map_succeed f = 
  let rec map_f = function 
    | [] -> []
    |  h::t -> try (let x = f h in x :: map_f t) with Failure _ -> map_f t
  in 
  map_f 

(* Pretty-printing *)
  
let pr_spc = spc
let pr_fnl = fnl
let pr_int = int
let pr_str = str
let pr_coma () = str "," ++ spc ()
let pr_semicolon () = str ";" ++ spc ()
let pr_bar () = str "|" ++ spc ()
let pr_arg pr x = spc () ++ pr x
let pr_opt pr = function None -> mt () | Some x -> pr_arg pr x
let pr_opt_no_spc pr = function None -> mt () | Some x -> pr x

let nth n = str (ordinal n)

let rec prlist elem l = match l with 
  | []   -> mt ()
  | h::t -> Stream.lapp (fun () -> elem h) (prlist elem t)

(* unlike all other functions below, [prlist] works lazily.
   if a strict behavior is needed, use [prlist_strict] instead. *)

let rec prlist_strict elem l = match l with 
  | []   -> mt ()
  | h::t -> (elem h)++(prlist_strict elem t)

let rec prlist_with_sep sep elem l = match l with
  | []   -> mt ()
  | [h]  -> elem h
  | h::t ->
      let e = elem h and s = sep() and r = prlist_with_sep sep elem t in
      e ++ s ++ r

let pr_vertical_list pr = function
  | [] -> str "none" ++ fnl ()
  | l -> fnl () ++ str "  " ++ hov 0 (prlist_with_sep pr_fnl pr l) ++ fnl ()
      
let prvecti elem v =
  let n = Array.length v in
  let rec pr i =
    if i = 0 then 
      elem 0 v.(0)
    else
      let r = pr (i-1) and e = elem i v.(i) in r ++ e
  in
  if n = 0 then mt () else pr (n - 1)

let prvect_with_sep sep elem v =
  let rec pr n =
    if n = 0 then 
      elem v.(0)
    else 
      let r = pr (n-1) and s = sep() and e = elem v.(n) in 
      r ++ s ++ e
      in
  let n = Array.length v in
  if n = 0 then mt () else pr (n - 1)

let prvect elem v = prvect_with_sep mt elem v

let surround p = hov 1 (str"(" ++ p ++ str")")

(*s Size of ocaml values. *)

module Size = struct
  
  open Obj

  (*s Pointers already visited are stored in a hash-table, where
      comparisons are done using physical equality. *)

  module H = Hashtbl.Make(
    struct 
      type t = Obj.t 
      let equal = (==) 
      let hash o = Hashtbl.hash (magic o : int)
    end)
	       
  let node_table = (H.create 257 : unit H.t)
		     
  let in_table o = try H.find node_table o; true with Not_found -> false
      
  let add_in_table o = H.add node_table o ()
			 
  let reset_table () = H.clear node_table
			 
  (*s Objects are traversed recursively, as soon as their tags are less than
      [no_scan_tag]. [count] records the numbers of words already visited. *)

  let size_of_double = size (repr 1.0)
			 
  let count = ref 0
		
  let rec traverse t =
    if not (in_table t) then begin
      add_in_table t;
      if is_block t then begin
	let n = size t in
	let tag = tag t in
	if tag < no_scan_tag then begin
	  count := !count + 1 + n;
	  for i = 0 to n - 1 do
      	    let f = field t i in 
	    if is_block f then traverse f
	  done
	end else if tag = string_tag then
	  count := !count + 1 + n 
	else if tag = double_tag then
	  count := !count + size_of_double
	else if tag = double_array_tag then
	  count := !count + 1 + size_of_double * n 
	else
	  incr count
      end
    end
      
  (*s Sizes of objects in words and in bytes. The size in bytes is computed
      system-independently according to [Sys.word_size]. *)

  let size_w o =
    reset_table ();
    count := 0;
    traverse (repr o);
    !count

  let size_b o = (size_w o) * (Sys.word_size / 8)

  let size_kb o = (size_w o) / (8192 / Sys.word_size)

end

let size_w = Size.size_w
let size_b = Size.size_b
let size_kb = Size.size_kb

(*s Total size of the allocated ocaml heap. *)

let heap_size () =
  let stat = Gc.stat ()
  and control = Gc.get () in
  let max_words_total = stat.Gc.heap_words + control.Gc.minor_heap_size in
  (max_words_total * Sys.word_size / 8)

let heap_size_kb () = (heap_size () + 1023) / 1024

(*s interruption *)

let interrupt = ref false
let check_for_interrupt () = 
  if !interrupt then begin interrupt := false; raise Sys.Break end

