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

exception Exc of t * exn

let raise loc exc =
  match exc with
    Exc (_, _) -> raise exc
  | _ -> raise (Exc (loc, exc))
