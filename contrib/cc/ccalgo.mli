(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

val init_size : int

type term = Symb of Term.constr | Appli of term * term

module UF :
  sig
    type tag = Congr | Ax of Names.identifier
    and cl =
        Rep of int * int list
      | Eqto of int * (int * int * tag)
    and vertex = Leaf | Node of (int * int)
    and t = int ref * (int, cl * vertex * term) Hashtbl.t
    val empty : unit -> t
    val add_lst : int -> int -> t -> unit
    val find : t -> int -> int
    val list : t -> int -> int list
    val size : t -> int -> int
    val signature : t -> int -> int * int
    val nodes : t -> int list
    val add :
      term ->
      int ref * (int, cl * vertex * term) Hashtbl.t ->
      (term, int) Hashtbl.t -> int
    val union :
      t -> int -> int -> int * int * tag -> unit
  end

module ST :
  sig
    type t =
      (int * int, int) Hashtbl.t *
      (int, int * int) Hashtbl.t
    val empty :
      unit -> ('a, 'b) Hashtbl.t * ('c, 'd) Hashtbl.t
    val enter : int -> int * int -> t -> unit
    val query : int * int -> t -> int
    val delete : int -> t -> unit
    val delete_list : int list -> t -> unit
  end

val combine_rec :
  UF.t -> ST.t -> int list -> (int * int) list

val process_rec :
  UF.t -> ST.t -> (int * int) list -> int list

val cc_rec : UF.t -> ST.t -> int list -> unit

val cc : UF.t -> unit

val make_uf :
  (term, int) Hashtbl.t ->
  (Names.identifier * (term * term)) list -> UF.t

val decide_prb :
  (Names.identifier * (term * term)) list * (term * term) ->
  bool
