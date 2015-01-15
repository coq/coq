(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Bruno Barras for Benjamin Grégoire as part of the
   bytecode-based reduction machine, Oct 2004 *)
(* Support for native arithmetics by Arnaud Spiwack, May 2007 *)

(* This file defines the type of bytecode instructions *)

open Names
open Term

type tag = int

let id_tag = 0
let iddef_tag = 1
let ind_tag = 2
let fix_tag = 3
let switch_tag = 4
let cofix_tag = 5
let cofix_evaluated_tag = 6

type structured_constant =
  | Const_sorts of sorts
  | Const_ind of pinductive
  | Const_b0 of tag
  | Const_bn of tag * structured_constant array


type reloc_table = (tag * int) array

type annot_switch =
   {ci : case_info; rtbl : reloc_table; tailcall : bool}

module Label =
  struct
    type t = int
    let no = -1
    let counter = ref no
    let create () = incr counter; !counter
    let reset_label_counter () = counter := no
  end


type instruction =
  | Klabel of Label.t
  | Kacc of int
  | Kenvacc of int
  | Koffsetclosure of int
  | Kpush
  | Kpop of int
  | Kpush_retaddr of Label.t
  | Kapply of int                       (*  number of arguments *)
  | Kappterm of int * int               (* number of arguments, slot size *)
  | Kreturn of int                      (* slot size *)
  | Kjump
  | Krestart
  | Kgrab of int                        (* number of arguments *)
  | Kgrabrec of int                     (* rec arg *)
  | Kclosure of Label.t * int           (* label, number of free variables *)
  | Kclosurerec of int * int * Label.t array * Label.t array
                   (* nb fv, init, lbl types, lbl bodies *)
  | Kclosurecofix of int * int * Label.t array * Label.t array
                   (* nb fv, init, lbl types, lbl bodies *)
  | Kgetglobal of pconstant
  | Kconst of structured_constant
  | Kmakeblock of int * tag             (* size, tag *)
  | Kmakeprod
  | Kmakeswitchblock of Label.t * Label.t * annot_switch * int
  | Kswitch of Label.t array * Label.t array (* consts,blocks *)
  | Kpushfields of int
  | Kfield of int
  | Ksetfield of int
  | Kstop
  | Ksequence of bytecodes * bytecodes
(* spiwack: instructions concerning integers *)
  | Kbranch of Label.t                  (* jump to label *)
  | Kaddint31                           (* adds the int31 in the accu
                                           and the one ontop of the stack *)
  | Kaddcint31                          (* makes the sum and keeps the carry *)
  | Kaddcarrycint31                     (* sum +1, keeps the carry *)
  | Ksubint31                           (* subtraction modulo *)
  | Ksubcint31                          (* subtraction, keeps the carry *)
  | Ksubcarrycint31                      (* subtraction -1, keeps the carry *)
  | Kmulint31                           (* multiplication modulo *)
  | Kmulcint31                          (* multiplication, result in two
					   int31, for exact computation *)
  | Kdiv21int31                          (* divides a double size integer
                                           (represented by an int31 in the
					   accumulator and one on the top of
					   the stack) by an int31. The result
					   is a pair of the quotient and the
					   rest.
					   If the divisor is 0, it returns
					   0. *)
  | Kdivint31                           (* euclidian division (returns a pair
					   quotient,rest) *)
  | Kaddmuldivint31                     (* generic operation for shifting and
					   cycling. Takes 3 int31 i j and s,
					   and returns x*2^s+y/(2^(31-s) *)
  | Kcompareint31                       (* unsigned comparison of int31
					   cf COMPAREINT31 in
					   kernel/byterun/coq_interp.c
					   for more info *)
  | Khead0int31                         (* Give the numbers of 0 in head of a in31*)
  | Ktail0int31                         (* Give the numbers of 0 in tail of a in31
                                           ie low bits *)
  | Kisconst of Label.t                 (* conditional jump *)
  | Kareconst of int*Label.t            (* conditional jump *)
  | Kcompint31                          (* dynamic compilation of int31 *)
  | Kdecompint31                        (* dynamic decompilation of int31 *)
  | Klorint31                            (* bitwise operations: or and xor *)
  | Klandint31
  | Klxorint31
(* /spiwack *)

and bytecodes = instruction list

type fv_elem = FVnamed of Id.t | FVrel of int

type fv = fv_elem array

(* spiwack: this exception is expected to be raised by function expecting
            closed terms. *)
exception NotClosed


(*spiwack: both type have been moved from Cbytegen because I needed then
  for the retroknowledge *)
type vm_env = {
    size : int;              (* longueur de la liste [n] *)
    fv_rev : fv_elem list    (* [fvn; ... ;fv1] *)
  }


type comp_env = {
    nb_stack : int;              (* nbre de variables sur la pile          *)
    in_stack : int list;         (* position dans la pile                  *)
    nb_rec : int;                (* nbre de fonctions mutuellement         *)
                                 (* recursives =  nbr                      *)
    pos_rec  : instruction list; (* instruction d'acces pour les variables *)
                                 (*  de point fix ou de cofix              *)
    offset : int;
    in_env : vm_env ref
  }



(* --- Pretty print *)
open Format
let rec instruction ppf = function
  | Klabel lbl -> fprintf ppf "L%i:" lbl
  | Kacc n -> fprintf ppf "\tacc %i" n
  | Kenvacc n -> fprintf ppf "\tenvacc %i" n
  | Koffsetclosure n -> fprintf ppf "\toffsetclosure %i" n
  | Kpush -> fprintf ppf "\tpush"
  | Kpop n -> fprintf ppf "\tpop %i" n
  | Kpush_retaddr lbl -> fprintf ppf "\tpush_retaddr L%i" lbl
  | Kapply n -> fprintf ppf "\tapply %i" n
  | Kappterm(n, m) ->
      fprintf ppf "\tappterm %i, %i" n m
  | Kreturn n -> fprintf ppf "\treturn %i" n
  | Kjump -> fprintf ppf "\tjump"
  | Krestart -> fprintf ppf "\trestart"
  | Kgrab n -> fprintf ppf "\tgrab %i" n
  | Kgrabrec n -> fprintf ppf "\tgrabrec %i" n
  | Kclosure(lbl, n) ->
      fprintf ppf "\tclosure L%i, %i" lbl n
  | Kclosurerec(fv,init,lblt,lblb) ->
      fprintf ppf "\tclosurerec";
      fprintf ppf "%i , %i, " fv init;
      print_string "types = ";
      Array.iter (fun lbl -> fprintf ppf " %i" lbl) lblt;
      print_string " bodies = ";
      Array.iter (fun lbl -> fprintf ppf " %i" lbl) lblb;
  | Kclosurecofix (fv,init,lblt,lblb) ->
      fprintf ppf "\tclosurecofix";
      fprintf ppf " %i , %i, " fv init;
      print_string "types = ";
      Array.iter (fun lbl -> fprintf ppf " %i" lbl) lblt;
      print_string " bodies = ";
      Array.iter (fun lbl -> fprintf ppf " %i" lbl) lblb;
  | Kgetglobal (id,u) -> fprintf ppf "\tgetglobal %s" (Names.string_of_con id)
  | Kconst cst ->
      fprintf ppf "\tconst"
  | Kmakeblock(n, m) ->
      fprintf ppf "\tmakeblock %i, %i" n m
  | Kmakeprod -> fprintf ppf "\tmakeprod"
  | Kmakeswitchblock(lblt,lbls,_,sz) ->
      fprintf ppf "\tmakeswitchblock %i, %i, %i" lblt lbls sz
  | Kswitch(lblc,lblb) ->
      fprintf ppf "\tswitch";
      Array.iter (fun lbl -> fprintf ppf " %i" lbl) lblc;
      Array.iter (fun lbl -> fprintf ppf " %i" lbl) lblb;
  | Kpushfields n -> fprintf ppf "\tpushfields %i" n
  | Ksetfield n -> fprintf ppf "\tsetfield %i" n
  | Kfield  n -> fprintf ppf "\tgetfield %i" n
  | Kstop -> fprintf ppf "\tstop"
  | Ksequence (c1,c2) ->
      fprintf ppf "%a@ %a" instruction_list c1 instruction_list c2
(* spiwack *)
  | Kbranch lbl -> fprintf ppf "\tbranch %i" lbl
  | Kaddint31 -> fprintf ppf "\taddint31"
  | Kaddcint31 -> fprintf ppf "\taddcint31"
  | Kaddcarrycint31 -> fprintf ppf "\taddcarrycint31"
  | Ksubint31 -> fprintf ppf "\tsubint31"
  | Ksubcint31 -> fprintf ppf "\tsubcint31"
  | Ksubcarrycint31 -> fprintf ppf "\tsubcarrycint31"
  | Kmulint31 -> fprintf ppf "\tmulint31"
  | Kmulcint31 -> fprintf ppf "\tmulcint31"
  | Kdiv21int31 -> fprintf ppf "\tdiv21int31"
  | Kdivint31 -> fprintf ppf "\tdivint31"
  | Kcompareint31 -> fprintf ppf "\tcompareint31"
  | Khead0int31 -> fprintf ppf "\thead0int31"
  | Ktail0int31 -> fprintf ppf "\ttail0int31"
  | Kaddmuldivint31 -> fprintf ppf "\taddmuldivint31"
  | Kisconst lbl -> fprintf ppf "\tisconst %i" lbl
  | Kareconst(n,lbl) -> fprintf ppf "\tareconst %i %i" n lbl
  | Kcompint31 -> fprintf ppf "\tcompint31"
  | Kdecompint31 -> fprintf ppf "\tdecompint"
  | Klorint31 -> fprintf ppf "\tlorint31"
  | Klandint31 -> fprintf ppf "\tlandint31"
  | Klxorint31 -> fprintf ppf "\tlxorint31"

(* /spiwack *)


and instruction_list ppf = function
    [] -> ()
  | Klabel lbl :: il ->
      fprintf ppf "L%i:%a" lbl instruction_list il
  | instr :: il ->
      fprintf ppf "%a@ %a" instruction instr instruction_list il


(*spiwack: moved this type in this file  because I needed it for
  retroknowledge which can't depend from cbytegen *)
type block =
  | Bconstr of constr
  | Bstrconst of structured_constant
  | Bmakeblock of int * block array
  | Bconstruct_app of int * int * int * block array
                  (* tag , nparams, arity *)
  | Bspecial of (comp_env -> block array -> int -> bytecodes -> bytecodes) * block array
                (* spiwack: compilation given by a function *)
                (* compilation function (see get_vm_constant_dynamic_info in
                   retroknowledge.mli for more info) , argument array  *)



let draw_instr c =
  fprintf std_formatter "@[<v 0>%a@]" instruction_list c
