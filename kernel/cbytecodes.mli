(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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
  | Const_ind of inductive
  | Const_b0 of int
  | Const_val of Term.values

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
  | Kgetglobal of constant
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
  | Kbranch of Label.t                  (* jump to label *)

  | Kprim of Native.prim_op * constant option 
  | Kprim_const of Native.prim_op * constant option * int 
  | Kcamlprim of Native.caml_prim * Label.t 

  | Kareint of int

and bytecodes = instruction list

type fv_elem = FVnamed of identifier | FVrel of int

type fv = fv_elem array

(* rend le numero du constructeur correspondant au tag [tag],
   [cst] = true si c'est un constructeur constant *)
val invert_tag : bool -> tag -> reloc_table -> int

val draw_instr : bytecodes -> unit

val pp_struct_const : structured_constant -> Pp.std_ppcmds


