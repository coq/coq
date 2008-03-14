(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

let norm_char c = match Char.uppercase c with
  | '\192'..'\198' -> 'A'
  | '\199' -> 'C'
  | '\200'..'\203' -> 'E'
  | '\204'..'\207' -> 'I'
  | '\209' -> 'N'
  | '\210'..'\214' -> 'O'
  | '\217'..'\220' -> 'U'
  | '\221' -> 'Y'
  | c -> c

let norm_string s =
  let u = String.copy s in
  for i = 0 to String.length s - 1 do
    u.[i] <- norm_char s.[i]
  done;
  u

let compare_char c1 c2 = match norm_char c1, norm_char c2 with
  | ('A'..'Z' as c1), ('A'..'Z' as c2) -> compare c1 c2
  | 'A'..'Z', _ -> -1
  | _, 'A'..'Z' -> 1
  | c1, c2 -> compare c1 c2

let compare_string s1 s2 = 
  let n1 = String.length s1 in
  let n2 = String.length s2 in
  let rec cmp i = 
    if i == n1 || i == n2 then
      n1 - n2
    else
      let c = compare_char s1.[i] s2.[i] in
      if c == 0 then cmp (succ i) else c
  in
  cmp 0
