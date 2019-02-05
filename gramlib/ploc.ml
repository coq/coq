(* camlp5r *)
(* ploc.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

open Loc

let make_unlined (bp, ep) =
  {fname = InFile ""; line_nb = 1; bol_pos = 0; line_nb_last = -1; bol_pos_last = 0;
   bp = bp; ep = ep; }

let dummy =
  {fname = InFile ""; line_nb = 1; bol_pos = 0; line_nb_last = -1; bol_pos_last = 0;
   bp = 0; ep = 0; }

(* *)

let sub loc sh len = {loc with bp = loc.bp + sh; ep = loc.bp + sh + len}
let after loc sh len = {loc with bp = loc.ep + sh; ep = loc.ep + sh + len}

exception Exc of Loc.t * exn

let raise loc exc =
  match exc with
    Exc (_, _) -> raise exc
  | _ -> raise (Exc (loc, exc))
