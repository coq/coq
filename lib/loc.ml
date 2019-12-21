(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Locations management *)

type source =
  | InFile of string
  | ToplevelInput

type t = {
  fname : source; (** filename or toplevel input *)
  line_nb : int; (** start line number *)
  bol_pos : int; (** position of the beginning of start line *)
  line_nb_last : int; (** end line number *)
  bol_pos_last : int; (** position of the beginning of end line *)
  bp : int; (** start position *)
  ep : int; (** end position *)
}

let create fname line_nb bol_pos bp ep = {
  fname = fname; line_nb = line_nb; bol_pos = bol_pos;
  line_nb_last = line_nb; bol_pos_last = bol_pos; bp = bp; ep = ep;
}

let initial source = create source 1 0 0 0

let make_loc (bp, ep) = {
  fname = ToplevelInput; line_nb = -1; bol_pos = 0; line_nb_last = -1; bol_pos_last = 0;
  bp = bp; ep = ep;
}

let same_file loc1 loc2 =
  loc1.fname = loc2.fname

(* We merge locations, such that:
   - one includes the other:
     --------- or   ----
       ----       ---------
   - they overlap
     ------    or     ------
        ------    ------
   - they are disjoint
     ------    ------
*)

let merge loc1 loc2 =
  if not (same_file loc1 loc2) then
    failwith "Trying to merge unmergeable locations.";
  if loc1.bp < loc2.bp then
    if loc1.ep < loc2.ep then {
      fname = loc1.fname;
      line_nb = loc1.line_nb;
      bol_pos = loc1.bol_pos;
      line_nb_last = loc2.line_nb_last;
      bol_pos_last = loc2.bol_pos_last;
      bp = loc1.bp; ep = loc2.ep;
    }
    else loc1
  else if loc2.ep < loc1.ep then {
    fname = loc2.fname;
    line_nb = loc2.line_nb;
    bol_pos = loc2.bol_pos;
    line_nb_last = loc1.line_nb_last;
    bol_pos_last = loc1.bol_pos_last;
    bp = loc2.bp; ep = loc1.ep;
  }
  else loc2

(* We extend a location up to before another location:
   from  -----    -----
   gives ---------
*)

let subtract loc1 loc2 =
  if not (same_file loc1 loc2) then
    failwith "Trying to merge unmergeable locations.";
  if loc2.bp < loc1.ep then failwith "Non disjoint locations.";
  let line_nb_last,bol_pos_last =
    if loc2.bol_pos > 0 then loc2.line_nb, loc2.bol_pos - 1
    else (* No way to get the exact bol_pos of the previous line *)
      loc2.line_nb, loc2.bol_pos in
  let ep = loc2.bp - 1 in
  { loc1 with line_nb_last; bol_pos_last; ep }

let combine_opt f l1 l2 = match l1, l2 with
  | None, None    -> None
  | Some l , None -> Some l
  | None, Some l  -> Some l
  | Some l1, Some l2 -> Some (f l1 l2)

let subtract_opt = combine_opt subtract
let merge_opt = combine_opt merge

let finer l1 l2 = match l1, l2 with
  | None, _    -> false
  | Some l , None -> true
  | Some l1, Some l2 -> l1.fname = l2.fname && merge l1 l2 = l2

let unloc loc = (loc.bp, loc.ep)

let shift_loc kb kp loc = { loc with bp = loc.bp + kb ; ep = loc.ep + kp }

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

