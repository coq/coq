(* camlp5r *)
(* ploc.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

type t =
  { fname : string;
    line_nb : int;
    bol_pos : int;
    line_nb_last : int;
    bol_pos_last : int;
    bp : int;
    ep : int;
    comm : string;
    ecomm : string }

let make_loc fname line_nb bol_pos (bp, ep) comm =
  {fname = fname; line_nb = line_nb; bol_pos = bol_pos;
   line_nb_last = line_nb; bol_pos_last = bol_pos; bp = bp; ep = ep;
   comm = comm; ecomm = ""}

let make_unlined (bp, ep) =
  {fname = ""; line_nb = 1; bol_pos = 0; line_nb_last = -1; bol_pos_last = 0;
   bp = bp; ep = ep; comm = ""; ecomm = ""}

let dummy =
  {fname = ""; line_nb = 1; bol_pos = 0; line_nb_last = -1; bol_pos_last = 0;
   bp = 0; ep = 0; comm = ""; ecomm = ""}

let file_name loc = loc.fname
let first_pos loc = loc.bp
let last_pos loc = loc.ep
let line_nb loc = loc.line_nb
let bol_pos loc = loc.bol_pos
let line_nb_last loc = loc.line_nb_last
let bol_pos_last loc = loc.bol_pos_last
let comment loc = loc.comm
let comment_last loc = loc.ecomm

(* *)

let encl loc1 loc2 =
  if loc1.bp < loc2.bp then
    if loc1.ep < loc2.ep then
      {fname = loc1.fname; line_nb = loc1.line_nb; bol_pos = loc1.bol_pos;
       line_nb_last = loc2.line_nb_last; bol_pos_last = loc2.bol_pos_last;
       bp = loc1.bp; ep = loc2.ep; comm = loc1.comm; ecomm = loc2.comm}
    else loc1
  else if loc2.ep < loc1.ep then
    {fname = loc2.fname; line_nb = loc2.line_nb; bol_pos = loc2.bol_pos;
     line_nb_last = loc1.line_nb_last; bol_pos_last = loc1.bol_pos_last;
     bp = loc2.bp; ep = loc1.ep; comm = loc2.comm; ecomm = loc1.comm}
  else loc2
let shift sh loc = {loc with bp = sh + loc.bp; ep = sh + loc.ep}
let sub loc sh len = {loc with bp = loc.bp + sh; ep = loc.bp + sh + len}
let after loc sh len = {loc with bp = loc.ep + sh; ep = loc.ep + sh + len}
let with_comment loc comm = {loc with comm = comm}

let name = ref "loc"

let from_file fname loc =
  let (bp, ep) = first_pos loc, last_pos loc in
  try
    let ic = open_in_bin fname in
    let strm = Stream.of_channel ic in
    let rec loop fname lin =
      let rec not_a_line_dir col (strm__ : _ Stream.t) =
        let cnt = Stream.count strm__ in
        match Stream.peek strm__ with
          Some c ->
            Stream.junk strm__;
            let s = strm__ in
            if cnt < bp then
              if c = '\n' then loop fname (lin + 1)
              else not_a_line_dir (col + 1) s
            else let col = col - (cnt - bp) in fname, lin, col, col + ep - bp
        | _ -> fname, lin, col, col + 1
      in
      let rec a_line_dir str n col (strm__ : _ Stream.t) =
        match Stream.peek strm__ with
          Some '\n' -> Stream.junk strm__; loop str n
        | Some _ -> Stream.junk strm__; a_line_dir str n (col + 1) strm__
        | _ -> raise Stream.Failure
      in
      let rec spaces col (strm__ : _ Stream.t) =
        match Stream.peek strm__ with
          Some ' ' -> Stream.junk strm__; spaces (col + 1) strm__
        | _ -> col
      in
      let rec check_string str n col (strm__ : _ Stream.t) =
        match Stream.peek strm__ with
          Some '"' ->
            Stream.junk strm__;
            let col =
              try spaces (col + 1) strm__ with
                Stream.Failure -> raise (Stream.Error "")
            in
            a_line_dir str n col strm__
        | Some c when c <> '\n' ->
            Stream.junk strm__;
            check_string (str ^ String.make 1 c) n (col + 1) strm__
        | _ -> not_a_line_dir col strm__
      in
      let check_quote n col (strm__ : _ Stream.t) =
        match Stream.peek strm__ with
          Some '"' -> Stream.junk strm__; check_string "" n (col + 1) strm__
        | _ -> not_a_line_dir col strm__
      in
      let rec check_num n col (strm__ : _ Stream.t) =
        match Stream.peek strm__ with
          Some ('0'..'9' as c) ->
            Stream.junk strm__;
            check_num (10 * n + Char.code c - Char.code '0') (col + 1) strm__
        | _ -> let col = spaces col strm__ in check_quote n col strm__
      in
      let begin_line (strm__ : _ Stream.t) =
        match Stream.peek strm__ with
          Some '#' ->
            Stream.junk strm__;
            let col =
              try spaces 1 strm__ with
                Stream.Failure -> raise (Stream.Error "")
            in
            check_num 0 col strm__
        | _ -> not_a_line_dir 0 strm__
      in
      begin_line strm
    in
    let r =
      try loop fname 1 with
        Stream.Failure ->
          let bol = bol_pos loc in fname, line_nb loc, bp - bol, ep - bol
    in
    close_in ic; r
  with Sys_error _ -> fname, 1, bp, ep

let second_line fname ep0 (line, bp) ep =
  let ic = open_in fname in
  seek_in ic bp;
  let rec loop line bol p =
    if p = ep then
      begin close_in ic; if bol = bp then line, ep0 else line, ep - bol end
    else
      let (line, bol) =
        match input_char ic with
          '\n' -> line + 1, p + 1
        | _ -> line, bol
      in
      loop line bol (p + 1)
  in
  loop line bp bp

let get loc =
  if loc.fname = "" || loc.fname = "-" then
    loc.line_nb, loc.bp - loc.bol_pos, loc.line_nb, loc.ep - loc.bol_pos,
    loc.ep - loc.bp
  else
    let (bl, bc, ec) =
      loc.line_nb, loc.bp - loc.bol_pos, loc.ep - loc.bol_pos
    in
    let (el, eep) = second_line loc.fname ec (bl, loc.bp) loc.ep in
    bl, bc, el, eep, ec - bc

let call_with r v f a =
  let saved = !r in
  try r := v; let b = f a in r := saved; b with e -> r := saved; raise e

exception Exc of t * exn

let raise loc exc =
  match exc with
    Exc (_, _) -> raise exc
  | _ -> raise (Exc (loc, exc))

type 'a vala =
    VaAnt of string
  | VaVal of 'a
