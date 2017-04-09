(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Locations management *)

type t = {
  fname : string; (** filename *)
  line_nb : int; (** start line number *)
  bol_pos : int; (** position of the beginning of start line *)
  line_nb_last : int; (** end line number *)
  bol_pos_last : int; (** position of the beginning of end line *)
  bp : int; (** start position *)
  ep : int; (** end position *)
}

let create fname line_nb bol_pos bp ep = {
  fname = fname; line_nb = line_nb; bol_pos = bol_pos;
  line_nb_last = line_nb; bol_pos_last = bol_pos; bp = bp; ep = ep; }

let make_loc (bp, ep) = {
  fname = ""; line_nb = -1; bol_pos = 0; line_nb_last = -1; bol_pos_last = 0;
  bp = bp; ep = ep; }

let merge loc1 loc2 =
  if loc1.bp < loc2.bp then
    if loc1.ep < loc2.ep then {
      fname = loc1.fname;
      line_nb = loc1.line_nb;
      bol_pos = loc1.bol_pos;
      line_nb_last = loc2.line_nb_last;
      bol_pos_last = loc2.bol_pos_last;
      bp = loc1.bp; ep = loc2.ep; }
    else loc1
  else if loc2.ep < loc1.ep then {
    fname = loc2.fname;
    line_nb = loc2.line_nb;
    bol_pos = loc2.bol_pos;
    line_nb_last = loc1.line_nb_last;
    bol_pos_last = loc1.bol_pos_last;
    bp = loc2.bp; ep = loc1.ep; }
  else loc2

let merge_opt l1 l2 = match l1, l2 with
  | None, None    -> None
  | Some l , None -> Some l
  | None, Some l  -> Some l
  | Some l1, Some l2 -> Some (merge l1 l2)

let unloc loc = (loc.bp, loc.ep)

(** Located type *)
type 'a located = t option * 'a

let tag ?loc x = loc, x
let map f (l,x) = (l, f x)

(** Exceptions *)

let location : t Exninfo.t = Exninfo.make ()

let add_loc e loc = Exninfo.add e location loc
let get_loc e = Exninfo.get e location

let raise ?loc e =
  match loc with
  | None     -> raise e
  | Some loc ->
    let info = Exninfo.add Exninfo.null location loc in
    Exninfo.iraise (e, info)

(** Deprecated *)
let located_fold_left f x (_,a) = f x a
let located_iter2 f (_,a) (_,b) = f a b
let down_located f (_,a) = f a


