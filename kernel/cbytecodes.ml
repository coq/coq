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
open Constr

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
  | Kbranch of Label.t                  (* jump to label *)
  | Kprim of CPrimitives.t * pconstant option
  | Kareint of int

and bytecodes = instruction list

type fv_elem =
  | FVnamed of Id.t
  | FVrel of int
  | FVuniv_var of int
  | FVevar of Evar.t

type fv = fv_elem array

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

  | Kprim (op, id) -> str (CPrimitives.to_string op) ++ str " " ++
        (match id with Some (id,_u) -> Constant.print id | None -> str "")

  | Kareint n -> str "areint " ++ int n

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
