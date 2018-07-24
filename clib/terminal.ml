(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type color = [
  `DEFAULT
| `BLACK
| `RED
| `GREEN
| `YELLOW
| `BLUE
| `MAGENTA
| `CYAN
| `WHITE
| `LIGHT_BLACK
| `LIGHT_RED
| `LIGHT_GREEN
| `LIGHT_YELLOW
| `LIGHT_BLUE
| `LIGHT_MAGENTA
| `LIGHT_CYAN
| `LIGHT_WHITE
| `INDEX of int
| `RGB of (int * int * int)
]

type style = {
  fg_color : color option;
  bg_color : color option;
  bold : bool option;
  italic : bool option;
  underline : bool option;
  negative : bool option;
  prefix : string option;
  suffix : string option;
}

let set o1 o2 = match o1 with
| None -> o2
| Some _ ->
  match o2 with
  | None -> o1
  | Some _ -> o2

let default = {
  fg_color = None;
  bg_color = None;
  bold = None;
  italic = None;
  underline = None;
  negative = None;
  prefix = None;
  suffix = None;
}

let reset = "\027[0m"

let reset_style = {
  fg_color = Some `DEFAULT;
  bg_color = Some `DEFAULT;
  bold = Some false;
  italic = Some false;
  underline = Some false;
  negative = Some false;
  prefix = None;
  suffix = None;
}

let make ?fg_color ?bg_color ?bold ?italic ?underline ?negative ?style ?prefix ?suffix () =
  let st = match style with
  | None -> default
  | Some st -> st
  in
  {
    fg_color = set st.fg_color fg_color;
    bg_color = set st.bg_color bg_color;
    bold = set st.bold bold;
    italic = set st.italic italic;
    underline = set st.underline underline;
    negative = set st.negative negative;
    prefix = set st.prefix prefix;
    suffix = set st.suffix suffix;
  }

let merge s1 s2 =
  {
    fg_color = set s1.fg_color s2.fg_color;
    bg_color = set s1.bg_color s2.bg_color;
    bold = set s1.bold s2.bold;
    italic = set s1.italic s2.italic;
    underline = set s1.underline s2.underline;
    negative = set s1.negative s2.negative;
    prefix = set s1.prefix s2.prefix;
    suffix = set s1.suffix s2.suffix;
  }

let diff s1 s2 =
  let diff_op o1 o2 reset_val = match o1 with
  | None -> o2
  | Some _ ->
    match o2 with
    | None -> reset_val
    | Some _ -> if o1 = o2 then None else o2 in

  {
    fg_color = diff_op s1.fg_color s2.fg_color reset_style.fg_color;
    bg_color = diff_op s1.bg_color s2.bg_color reset_style.bg_color;
    bold = diff_op s1.bold s2.bold reset_style.bold;
    italic = diff_op s1.italic s2.italic reset_style.italic;
    underline = diff_op s1.underline s2.underline reset_style.underline;
    negative = diff_op s1.negative s2.negative reset_style.negative;
    prefix = diff_op s1.prefix s2.prefix reset_style.prefix;
    suffix = diff_op s1.suffix s2.suffix reset_style.suffix;
  }

let base_color = function
| `DEFAULT -> 9
| `BLACK -> 0
| `RED -> 1
| `GREEN -> 2
| `YELLOW -> 3
| `BLUE -> 4
| `MAGENTA -> 5
| `CYAN -> 6
| `WHITE -> 7
| `LIGHT_BLACK -> 0
| `LIGHT_RED -> 1
| `LIGHT_GREEN -> 2
| `LIGHT_YELLOW -> 3
| `LIGHT_BLUE -> 4
| `LIGHT_MAGENTA -> 5
| `LIGHT_CYAN -> 6
| `LIGHT_WHITE -> 7
| _ -> invalid_arg "base_color"

let extended_color off = function
| `INDEX i -> [off + 8; 5; i]
| `RGB (r, g, b) -> [off + 8; 2; r; g; b]
| _ -> invalid_arg "extended_color"

let is_light = function
| `LIGHT_BLACK
| `LIGHT_RED
| `LIGHT_GREEN
| `LIGHT_YELLOW
| `LIGHT_BLUE
| `LIGHT_MAGENTA
| `LIGHT_CYAN
| `LIGHT_WHITE -> true
| _ -> false

let is_extended = function
| `INDEX _ | `RGB _ -> true
| _ -> false

let repr st =
  let fg = match st.fg_color with
  | None -> []
  | Some c ->
    if is_light c then [90 + base_color c]
    else if is_extended c then extended_color 30 c
    else [30 + base_color c]
  in
  let bg = match st.bg_color with
  | None -> []
  | Some c ->
    if is_light c then [100 + base_color c]
    else if is_extended c then extended_color 40 c
    else [40 + base_color c]
  in
  let bold = match st.bold with
  | None -> []
  | Some true -> [1]
  | Some false -> [22]
  in
  let italic = match st.italic with
  | None -> []
  | Some true -> [3]
  | Some false -> [23]
  in
  let underline = match st.underline with
  | None -> []
  | Some true -> [4]
  | Some false -> [24]
  in
  let negative = match st.negative with
  | None -> []
  | Some true -> [7]
  | Some false -> [27]
  in
  fg @ bg @ bold @ italic @ underline @ negative

let eval st =
  let tags = repr st in
  let tags = List.map string_of_int tags in
  if List.length tags = 0 then "" else
    Printf.sprintf "\027[%sm" (String.concat ";" tags)

let has_style t =
  Unix.isatty t && Sys.os_type = "Unix"

let split c s =
  let len = String.length s in
  let rec split n =
    try
      let pos = String.index_from s n c in
      let dir = String.sub s n (pos-n) in
      dir :: split (succ pos)
    with
      | Not_found -> [String.sub s n (len-n)]
  in
  if len = 0 then [] else split 0

let check_char i = if i < 0 || i > 255 then invalid_arg "check_char"

let parse_color off rem = match off with
| 0 -> (`BLACK, rem)
| 1 -> (`RED, rem)
| 2 -> (`GREEN, rem)
| 3 -> (`YELLOW, rem)
| 4 -> (`BLUE, rem)
| 5 -> (`MAGENTA, rem)
| 6 -> (`CYAN, rem)
| 7 -> (`WHITE, rem)
| 9 -> (`DEFAULT, rem)
| 8 ->
  begin match rem with
  | 5 :: i :: rem ->
    check_char i;
    (`INDEX i, rem)
  | 2 :: r :: g :: b :: rem ->
    check_char r;
    check_char g;
    check_char b;
    (`RGB (r, g, b), rem)
  | _ -> invalid_arg "parse_color"
  end
| _ -> invalid_arg "parse_color"

let set_light = function
| `BLACK -> `LIGHT_BLACK
| `RED -> `LIGHT_RED
| `GREEN -> `LIGHT_GREEN
| `YELLOW -> `LIGHT_YELLOW
| `BLUE -> `LIGHT_BLUE
| `MAGENTA -> `LIGHT_MAGENTA
| `CYAN -> `LIGHT_CYAN
| `WHITE -> `LIGHT_WHITE
| _ -> invalid_arg "parse_color"

let rec parse_style style = function
| [] -> style
| 0 :: rem ->
  let style = merge style reset_style in
  parse_style style rem
| 1 :: rem ->
  let style = make ~style ~bold:true () in
  parse_style style rem
| 3 :: rem ->
  let style = make ~style ~italic:true () in
  parse_style style rem
| 4 :: rem ->
  let style = make ~style ~underline:true () in
  parse_style style rem
| 7 :: rem ->
  let style = make ~style ~negative:true () in
  parse_style style rem
| 22 :: rem ->
  let style = make ~style ~bold:false () in
  parse_style style rem
| 23 :: rem ->
  let style = make ~style ~italic:false () in
  parse_style style rem
| 24 :: rem ->
  let style = make ~style ~underline:false () in
  parse_style style rem
| 27 :: rem ->
  let style = make ~style ~negative:false () in
  parse_style style rem
| code :: rem when (30 <= code && code < 40) ->
  let color, rem = parse_color (code mod 10) rem in
  let style = make ~style ~fg_color:color () in
  parse_style style rem
| code :: rem when (40 <= code && code < 50) ->
  let color, rem = parse_color (code mod 10) rem in
  let style = make ~style ~bg_color:color () in
  parse_style style rem
| code :: rem when (90 <= code && code < 100) ->
  let color, rem = parse_color (code mod 10) rem in
  let style = make ~style ~fg_color:(set_light color) () in
  parse_style style rem
| code :: rem when (100 <= code && code < 110) ->
  let color, rem = parse_color (code mod 10) rem in
  let style = make ~style ~bg_color:(set_light color) () in
  parse_style style rem
| _ :: rem -> parse_style style rem

(** Parse LS_COLORS-like strings *)
let parse s =
  let defs = split ':' s in
  let fold accu s = match split '=' s with
  | [name; attrs] ->
    let attrs = split ';' attrs in
    let accu =
      try
        let attrs = List.map int_of_string attrs in
        let attrs = parse_style (make ()) attrs in
        (name, attrs) :: accu
      with _ -> accu
    in
    accu
  | _ -> accu
  in
  List.fold_left fold [] defs
