(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pcoq
open Pcoq.Prim
open Vernacexpr

(* Vernaculars specific to the toplevel *)
type vernac_toplevel =
  | VernacBacktrack of int * int * int
  | VernacDrop
  | VernacQuit
  | VernacControl of vernac_control

module Toplevel_ : sig
  val vernac_toplevel : vernac_toplevel CAst.t Gram.entry
end = struct
  let gec_vernac s = Gram.entry_create ("toplevel:" ^ s)
  let vernac_toplevel = gec_vernac "vernac_toplevel"
end

open Toplevel_

GEXTEND Gram
  GLOBAL: vernac_toplevel;
  vernac_toplevel: FIRST
    [ [ IDENT "Drop"; "." -> CAst.make VernacDrop
      | IDENT "Quit"; "." -> CAst.make VernacQuit
      | IDENT "Backtrack"; n = natural ; m = natural ; p = natural; "." ->
        CAst.make (VernacBacktrack (n,m,p))
      | cmd = main_entry ->
              match cmd with
              | None -> raise Stm.End_of_input
              | Some (loc,c) -> CAst.make ~loc (VernacControl c)
      ]
    ]
  ;
END

let parse_toplevel pa = Pcoq.Gram.entry_parse vernac_toplevel pa
