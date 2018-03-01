(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Bruno Barras for Benjamin Grégoire as part of the
   bytecode-based reduction machine, Oct 2004 *)
(* Support for native arithmetics by Arnaud Spiwack, May 2007 *)

(* This file defines the type of bytecode instructions *)

open Names
open Vmvalues

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
  | Kapply of int
  | Kappterm of int * int
  | Kreturn of int
  | Kjump
  | Krestart
  | Kgrab of int
  | Kgrabrec of int
  | Kclosure of Label.t * int
  | Kclosurerec of int * int * Label.t array * Label.t array
  | Kclosurecofix of int * int * Label.t array * Label.t array
                   (* nb fv, init, lbl types, lbl bodies *)
  | Kgetglobal of Constant.t
  | Kconst of structured_constant
  | Kmakeblock of int * tag
  | Kmakeprod
  | Kmakeswitchblock of Label.t * Label.t * annot_switch * int
  | Kswitch of Label.t array * Label.t array
  | Kpushfields of int
  | Kfield of int
  | Ksetfield of int
  | Kstop
  | Ksequence of bytecodes * bytecodes
  | Kproj of Projection.Repr.t
  | Kensurestackcapacity of int
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

type fv_elem =
  | FVnamed of Id.t
  | FVrel of int
  | FVuniv_var of int
  | FVevar of Evar.t

type fv = fv_elem array

(* spiwack: this exception is expected to be raised by function expecting
            closed terms. *)
exception NotClosed


module Fv_elem =
struct
type t = fv_elem

let compare e1 e2 = match e1, e2 with
| FVnamed id1, FVnamed id2 -> Id.compare id1 id2
| FVnamed _, (FVrel _ | FVuniv_var _ | FVevar _) -> -1
| FVrel _, FVnamed _ -> 1
| FVrel r1, FVrel r2 -> Int.compare r1 r2
| FVrel _, (FVuniv_var _ | FVevar _) -> -1
| FVuniv_var i1, FVuniv_var i2 -> Int.compare i1 i2
| FVuniv_var i1, (FVnamed _ | FVrel _) -> 1
| FVuniv_var i1, FVevar _ -> -1
| FVevar _, (FVnamed _ | FVrel _ | FVuniv_var _) -> 1
| FVevar e1, FVevar e2 -> Evar.compare e1 e2

end

module FvMap = Map.Make(Fv_elem)

(*spiwack: both type have been moved from Cbytegen because I needed then
  for the retroknowledge *)
type vm_env = {
    size : int;              (* longueur de la liste [n] *)
    fv_rev : fv_elem list;   (* [fvn; ... ;fv1] *)
    fv_fwd : int FvMap.t;    (* reverse mapping *)
  }


type comp_env = {
    arity : int;                 (* arity of the current function, 0 if none *)
    nb_uni_stack : int ;         (* number of universes on the stack,      *)
                                 (* universes are always at the bottom.    *)
    nb_stack : int;              (* number of variables on the stack       *)
    in_stack : int list;         (* position in the stack                  *)
    nb_rec : int;                (* number of mutually recursive functions *)
    pos_rec  : instruction list; (* instruction d'acces pour les variables *)
                                 (*  de point fix ou de cofix              *)
    offset : int;
    in_env : vm_env ref          (* The free variables of the expression   *)
  }

(* --- Pretty print *)
open Pp
open Util

let pp_lbl lbl = str "L" ++ int lbl

let pp_fv_elem = function
  | FVnamed id -> str "FVnamed(" ++ Id.print id ++ str ")"
  | FVrel i -> str "Rel(" ++ int i ++ str ")"
  | FVuniv_var v -> str "FVuniv(" ++ int v ++ str ")"
  | FVevar e -> str "FVevar(" ++ int (Evar.repr e) ++ str ")"

let rec pp_instr i =
  match i with
  | Klabel _   | Ksequence _ -> assert false
  | Kacc n -> str "acc " ++ int n
  | Kenvacc n -> str "envacc " ++ int n
  | Koffsetclosure n -> str "offsetclosure " ++ int n
  | Kpush -> str "push"
  | Kpop n -> str "pop " ++ int n
  | Kpush_retaddr lbl -> str "push_retaddr " ++ pp_lbl lbl
  | Kapply n -> str "apply " ++ int n
  | Kappterm(n, m) ->
      str "appterm " ++ int n ++ str ", " ++ int m
  | Kreturn n -> str "return " ++ int n
  | Kjump -> str "jump"
  | Krestart -> str "restart"
  | Kgrab n -> str "grab " ++ int n
  | Kgrabrec n -> str "grabrec " ++ int n
  | Kclosure(lbl, n) ->
      str "closure " ++ pp_lbl lbl ++ str ", " ++ int n
  | Kclosurerec(fv,init,lblt,lblb) ->
      h 1 (str "closurerec " ++
	     int fv ++ str ", " ++ int init ++
	     str " types = " ++
	     prlist_with_sep spc pp_lbl (Array.to_list lblt) ++
	     str " bodies = " ++
	     prlist_with_sep spc pp_lbl (Array.to_list lblb))
  | Kclosurecofix (fv,init,lblt,lblb) ->
      h 1 (str "closurecofix " ++
	     int fv ++ str ", " ++ int init ++
	     str " types = " ++
	     prlist_with_sep spc pp_lbl (Array.to_list lblt) ++
	     str " bodies = " ++
	     prlist_with_sep spc pp_lbl (Array.to_list lblb))
  | Kgetglobal idu -> str "getglobal " ++ Constant.print idu
  | Kconst sc ->
      str "const " ++ pp_struct_const sc
  | Kmakeblock(n, m) ->
      str "makeblock " ++ int n ++ str ", " ++ int m
  | Kmakeprod -> str "makeprod"
  | Kmakeswitchblock(lblt,lbls,_,sz) ->
      str "makeswitchblock " ++ pp_lbl lblt ++ str ", " ++
	pp_lbl lbls ++ str ", " ++ int sz
  | Kswitch(lblc,lblb) ->
      h 1 (str "switch " ++
	     prlist_with_sep spc pp_lbl (Array.to_list lblc) ++
	     str " | " ++
	     prlist_with_sep spc pp_lbl (Array.to_list lblb))
  | Kpushfields n -> str "pushfields " ++ int n
  | Kfield n -> str "field " ++ int n
  | Ksetfield n -> str "setfield " ++ int n

  | Kstop -> str "stop"

  | Kbranch lbl -> str "branch " ++ pp_lbl lbl

  | Kproj p -> str "proj " ++ Projection.Repr.print p

  | Kensurestackcapacity size -> str "growstack " ++ int size

  | Kaddint31 -> str "addint31"
  | Kaddcint31 -> str "addcint31"
  | Kaddcarrycint31 -> str "addcarrycint31"
  | Ksubint31 -> str "subint31"
  | Ksubcint31 -> str "subcint31"
  | Ksubcarrycint31 -> str "subcarrycint31"
  | Kmulint31 -> str "mulint31"
  | Kmulcint31 -> str "mulcint31"
  | Kdiv21int31 -> str "div21int31"
  | Kdivint31 -> str "divint31"
  | Kcompareint31 -> str "compareint31"
  | Khead0int31 -> str "head0int31"
  | Ktail0int31 -> str "tail0int31"
  | Kaddmuldivint31 -> str "addmuldivint31"
  | Kisconst lbl -> str "isconst " ++ int lbl
  | Kareconst(n,lbl) -> str "areconst " ++ int n ++ spc () ++ int lbl
  | Kcompint31 -> str "compint31"
  | Kdecompint31 -> str "decompint"
  | Klorint31 -> str "lorint31"
  | Klandint31 -> str "landint31"
  | Klxorint31 -> str "lxorint31"


and pp_bytecodes c =
  match c with
  | [] -> str ""
  | Klabel lbl :: c ->
	str "L" ++ int lbl ++ str ":" ++ fnl () ++
	pp_bytecodes c
  | Ksequence (l1, l2) :: c ->
      pp_bytecodes l1 ++ pp_bytecodes l2 ++  pp_bytecodes c
  | i :: c ->
      pp_instr i ++ fnl () ++ pp_bytecodes c
