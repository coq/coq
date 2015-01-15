(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Names
open Term

type tag = int

val id_tag : tag
val iddef_tag : tag
val ind_tag : tag
val fix_tag : tag
val switch_tag : tag
val cofix_tag : tag
val cofix_evaluated_tag : tag

type structured_constant =
  | Const_sorts of sorts
  | Const_ind of pinductive
  | Const_b0 of tag
  | Const_bn of tag * structured_constant array

type reloc_table = (tag * int) array

type annot_switch =
   {ci : case_info; rtbl : reloc_table; tailcall : bool}

module Label :
  sig
    type t = int
    val no : t
    val create : unit -> t
    val reset_label_counter : unit -> unit
  end

type instruction =
  | Klabel of Label.t
  | Kacc of int
  | Kenvacc of int
  | Koffsetclosure of int
  | Kpush
  | Kpop of int
  | Kpush_retaddr of Label.t
  | Kapply of int                       (**  number of arguments *)
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
  | Kgetglobal of pconstant
  | Kconst of structured_constant
  | Kmakeblock of int * tag             (** size, tag *)
  | Kmakeprod
  | Kmakeswitchblock of Label.t * Label.t * annot_switch * int
  | Kswitch of Label.t array * Label.t array (** consts,blocks *)
  | Kpushfields of int
  | Kfield of int
  | Ksetfield of int
  | Kstop
  | Ksequence of bytecodes * bytecodes

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

type fv_elem = FVnamed of Id.t | FVrel of int

type fv = fv_elem array


(** spiwack: this exception is expected to be raised by function expecting
            closed terms. *)
exception NotClosed

(*spiwack: both type have been moved from Cbytegen because I needed then
  for the retroknowledge *)
type vm_env = {
    size : int;              (** longueur de la liste [n] *)
    fv_rev : fv_elem list    (** [fvn; ... ;fv1] *)
  }


type comp_env = {
    nb_stack : int;              (** nbre de variables sur la pile          *)
    in_stack : int list;         (** position dans la pile                  *)
    nb_rec : int;                (** nbre de fonctions mutuellement         *)
                                 (** recursives =  nbr                      *)
    pos_rec  : instruction list; (** instruction d'acces pour les variables *)
                                 (**  de point fix ou de cofix              *)
    offset : int;
    in_env : vm_env ref
  }

val draw_instr : bytecodes -> unit



(*spiwack: moved this here because I needed it for retroknowledge *)
type block =
  | Bconstr of constr
  | Bstrconst of structured_constant
  | Bmakeblock of int * block array
  | Bconstruct_app of int * int * int * block array
                  (** tag , nparams, arity *)
  | Bspecial of (comp_env -> block array -> int -> bytecodes -> bytecodes) * block array
                (** compilation function (see get_vm_constant_dynamic_info in
                   retroknowledge.mli for more info) , argument array  *)
