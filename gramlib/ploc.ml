(* camlp5r *)
(* ploc.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

#load "pa_macro.cmo";

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
;

value make_loc fname line_nb bol_pos (bp, ep) comm =
  {fname = fname; line_nb = line_nb; bol_pos = bol_pos;
   line_nb_last = line_nb; bol_pos_last = bol_pos;
   bp = bp; ep = ep; comm = comm; ecomm = ""}
;

value make_unlined (bp, ep) =
  {fname = ""; line_nb = 1; bol_pos = 0; line_nb_last = -1; bol_pos_last = 0;
   bp = bp; ep = ep; comm = ""; ecomm = ""}
;

value dummy =
  {fname = ""; line_nb = 1; bol_pos = 0; line_nb_last = -1; bol_pos_last = 0;
   bp = 0; ep = 0; comm = ""; ecomm = ""}
;

value file_name loc = loc.fname;
value first_pos loc = loc.bp;
value last_pos loc = loc.ep;
value line_nb loc = loc.line_nb;
value bol_pos loc = loc.bol_pos;
value line_nb_last loc = loc.line_nb_last;
value bol_pos_last loc = loc.bol_pos_last;
value comment loc = loc.comm;
value comment_last loc = loc.ecomm;

IFDEF OCAML_VERSION <= OCAML_1_07 OR COMPATIBLE_WITH_OLD_OCAML THEN
  value with_bp_ep l bp ep =
    {fname = l.fname; line_nb = l.line_nb; bol_pos = l.bol_pos;
     line_nb_last = l.line_nb_last; bol_pos_last = l.bol_pos_last; bp = bp;
     ep = ep; comm = l.comm; ecomm = l.ecomm}
  ;
  value with_comm l comm =
    {fname = l.fname; line_nb = l.line_nb; bol_pos = l.bol_pos;
     line_nb_last = l.line_nb_last; bol_pos_last = l.bol_pos_last; bp = l.bp;
     ep = l.ep; comm = comm; ecomm = l.ecomm}
  ;
END;

value encl loc1 loc2 =
  if loc1.bp < loc2.bp then
    if loc1.ep < loc2.ep then
      {fname = loc1.fname; line_nb = loc1.line_nb; bol_pos = loc1.bol_pos;
       line_nb_last = loc2.line_nb_last; bol_pos_last = loc2.bol_pos_last;
       bp = loc1.bp; ep = loc2.ep; comm = loc1.comm; ecomm = loc2.comm}
    else
      loc1
  else
    if loc2.ep < loc1.ep then
      {fname = loc2.fname; line_nb = loc2.line_nb; bol_pos = loc2.bol_pos;
       line_nb_last = loc1.line_nb_last; bol_pos_last = loc1.bol_pos_last;
       bp = loc2.bp; ep = loc1.ep; comm = loc2.comm; ecomm = loc1.comm}
    else
      loc2
;
value shift sh loc = {(loc) with bp = sh + loc.bp; ep = sh + loc.ep};
value sub loc sh len = {(loc) with bp = loc.bp + sh; ep = loc.bp + sh + len};
value after loc sh len =
  {(loc) with bp = loc.ep + sh; ep = loc.ep + sh + len}
;
value with_comment loc comm = {(loc) with comm = comm};

value name = ref "loc";

value from_file fname loc =
  let (bp, ep) = (first_pos loc, last_pos loc) in
  try
    let ic = open_in_bin fname in
    let strm = Stream.of_channel ic in
    let rec loop fname lin =
      let rec not_a_line_dir col =
        parser cnt
        [ [: `c; s :] ->
            if cnt < bp then
              if c = '\n' then loop fname (lin + 1)
              else not_a_line_dir (col + 1) s
            else
              let col = col - (cnt - bp) in
              (fname, lin, col, col + ep - bp)
        | [: :] ->
            (fname, lin, col, col + 1) ]
      in
      let rec a_line_dir str n col =
        parser
        [ [: `'\n' :] -> loop str n
        | [: `_; s :] -> a_line_dir str n (col + 1) s ]
      in
      let rec spaces col =
        parser
        [ [: `' '; s :] -> spaces (col + 1) s
        | [: :] -> col ]
      in
      let rec check_string str n col =
        parser
        [ [: `'"'; col = spaces (col + 1); s :] -> a_line_dir str n col s
        | [: `c when c <> '\n'; s :] ->
            check_string (str ^ String.make 1 c) n (col + 1) s
        | [: a = not_a_line_dir col :] -> a ]
      in
      let check_quote n col =
        parser
        [ [: `'"'; s :] -> check_string "" n (col + 1) s
        | [: a = not_a_line_dir col :] -> a ]
      in
      let rec check_num n col =
        parser
        [ [: `('0'..'9' as c); s :] ->
            check_num (10 * n + Char.code c - Char.code '0') (col + 1) s
        | [: col = spaces col; s :] -> check_quote n col s ]
      in
      let begin_line =
        parser
        [ [: `'#'; col = spaces 1; s :] -> check_num 0 col s
        | [: a = not_a_line_dir 0 :] -> a ]
      in
      begin_line strm
    in
    let r =
      try loop fname 1 with
      [ Stream.Failure ->
          let bol = bol_pos loc in
          (fname, line_nb loc, bp - bol, ep - bol) ]
    in
    do { close_in ic; r }
  with
  [ Sys_error _ -> (fname, 1, bp, ep) ]
;

value second_line fname ep0 (line, bp) ep = do {
  let ic = open_in fname in
  seek_in ic bp;
  loop line bp bp where rec loop line bol p =
    if p = ep then do {
      close_in ic;
      if bol = bp then (line, ep0)
      else (line, ep - bol)
    }
    else do {
      let (line, bol) =
        match input_char ic with
        [ '\n' -> (line + 1, p + 1)
        | _ -> (line, bol) ]
      in
      loop line bol (p + 1)
    }
};

value get loc = do {
  if loc.fname = "" || loc.fname = "-" then do {
    (loc.line_nb, loc.bp - loc.bol_pos, loc.line_nb, loc.ep - loc.bol_pos,
     loc.ep - loc.bp)
  }
  else do {
    let (bl, bc, ec) =
      (loc.line_nb, loc.bp - loc.bol_pos, loc.ep - loc.bol_pos)
    in
    let (el, eep) = second_line loc.fname ec (bl, loc.bp) loc.ep in
    (bl, bc, el, eep, ec - bc)
  }
};

value call_with r v f a =
  let saved = r.val in
  try do {
    r.val := v;
    let b = f a in
    r.val := saved;
    b
  }
  with e -> do { r.val := saved; raise e }
;

exception Exc of t and exn;

value raise loc exc =
  match exc with
  [ Exc _ _ -> raise exc
  | _ -> raise (Exc loc exc) ]
;

type vala 'a =
  [ VaAnt of string
  | VaVal of 'a ]
;

value warned = ref True;
value warning_deprecated_since_6_00 name =
  if not warned.val then do {
    Printf.eprintf "<W> %s deprecated since version 6.00" name;
    warned.val := True
  }
  else ()
;

value make line_nb bol_pos (bp, ep) =
  let _ = warning_deprecated_since_6_00 "Ploc.make" in
  {fname = ""; line_nb = line_nb; bol_pos = bol_pos; line_nb_last = line_nb;
   bol_pos_last = bol_pos; bp = bp; ep = ep; comm = ""; ecomm = ""}
;
