(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* $Id$ *)

open Names
open Vmvalues

module Label :
  sig
    type t = int
    val no : t
    val create : unit -> t
    val reset_label_counter : unit -> unit
  end

type instruction =
  | Klabel of Label.t
  | Kacc of int                         (** accu = sp[n] *)
  | Kenvacc of int                      (** accu = coq_env[n] *)
  | Koffsetclosure of int               (** accu = &coq_env[n] *)
  | Kpush                               (** sp = accu :: sp *)
  | Kpop of int                         (** sp = skipn n sp *)
  | Kpush_retaddr of Label.t            (** sp = pc :: coq_env :: coq_extra_args :: sp ; coq_extra_args = 0 *)
  | Kapply of int                       (** number of arguments (arguments on top of stack) *)
  | Kappterm of int * int               (** number of arguments, slot size *)
  | Kreturn of int                      (** slot size *)
  | Kjump
  | Krestart
  | Kgrab of int                        (** number of arguments *)
  | Kgrabrec of int                     (** rec arg *)
  | Kclosure of Label.t * int           (** label, number of free variables *)
  | Kclosurerec of int * int * Label.t array * Label.t array
                   (** nb fv, init, lbl types, lbl bodies *)
  | Kclosurecofix of int * int * Label.t array * Label.t array
                   (** nb fv, init, lbl types, lbl bodies *)
  | Kgetglobal of Constant.t
  | Kconst of structured_constant
  | Kmakeblock of (* size: *) int * tag (** allocate an ocaml block. Index 0
                                         ** is accu, all others are popped from
					 ** the top of the stack  *)
  | Kmakeprod
  | Kmakeswitchblock of Label.t * Label.t * annot_switch * int
  | Kswitch of Label.t array * Label.t array (** consts,blocks *)
  | Kpushfields of int
  | Kfield of int                       (** accu = accu[n] *)
  | Ksetfield of int                    (** accu[n] = sp[0] ; sp = pop sp *)
  | Kstop
  | Ksequence of bytecodes * bytecodes
  | Kproj of Projection.Repr.t
  | Kensurestackcapacity of int

(** spiwack: instructions concerning integers *)
  | Kbranch of Label.t                  (** jump to label, is it needed ? *)
  | Kaddint31                           (** adds the int31 in the accu
                                           and the one ontop of the stack *)
  | Kaddcint31                          (** makes the sum and keeps the carry *)
  | Kaddcarrycint31                     (** sum +1, keeps the carry *)
  | Ksubint31                           (** subtraction modulo *)
  | Ksubcint31                          (** subtraction, keeps the carry *)
  | Ksubcarrycint31                     (** subtraction -1, keeps the carry *)
  | Kmulint31                           (** multiplication modulo *)
  | Kmulcint31                          (** multiplication, result in two
					   int31, for exact computation *)
  | Kdiv21int31                         (** divides a double size integer
                                           (represented by an int31 in the
					   accumulator and one on the top of
					   the stack) by an int31. The result
					   is a pair of the quotient and the
					   rest.
					   If the divisor is 0, it returns
					   0. *)
  | Kdivint31                           (** euclidian division (returns a pair
					   quotient,rest) *)
  | Kaddmuldivint31                     (** generic operation for shifting and
					   cycling. Takes 3 int31 i j and s,
					   and returns x*2^s+y/(2^(31-s) *)
  | Kcompareint31                        (** unsigned comparison of int31
					   cf COMPAREINT31 in
					   kernel/byterun/coq_interp.c
					   for more info *)
  | Khead0int31                         (** Give the numbers of 0 in head of a in31*)
  | Ktail0int31                         (** Give the numbers of 0 in tail of a in31
                                           ie low bits *)
  | Kisconst of Label.t                 (** conditional jump *)
  | Kareconst of int*Label.t            (** conditional jump *)
  | Kcompint31                          (** dynamic compilation of int31 *)
  | Kdecompint31                        (** dynamix decompilation of int31 *)
  | Klorint31                           (** bitwise operations: or and xor *)
  | Klandint31
  | Klxorint31

and bytecodes = instruction list

type fv_elem =
  FVnamed of Id.t
| FVrel of int
| FVuniv_var of int
| FVevar of Evar.t

type fv = fv_elem array


(** spiwack: this exception is expected to be raised by function expecting
            closed terms. *)
exception NotClosed

module FvMap : Map.S with type key = fv_elem

(*spiwack: both type have been moved from Cbytegen because I needed them
  for the retroknowledge *)
type vm_env = {
    size : int;              (** length of the list [n] *)
    fv_rev : fv_elem list;   (** [fvn; ... ;fv1] *)
    fv_fwd : int FvMap.t;    (** reverse mapping *)
  }


type comp_env = {
    arity : int;                 (* arity of the current function, 0 if none *)
    nb_uni_stack : int ;         (** number of universes on the stack       *)
    nb_stack : int;              (** number of variables on the stack       *)
    in_stack : int list;         (** position in the stack                  *)
    nb_rec : int;                (** number of mutually recursive functions *)
                                 (** (= nbr)                                *)
    pos_rec  : instruction list; (** instruction d'acces pour les variables *)
                                 (**  de point fix ou de cofix              *)
    offset : int;
    in_env : vm_env ref          (** the variables that are accessed        *)
  }

val pp_bytecodes : bytecodes -> Pp.t
val pp_fv_elem : fv_elem -> Pp.t
