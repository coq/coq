(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

type caml_prim =
| CAML_Arraymake
| CAML_Arrayget
| CAML_Arraydefault
| CAML_Arrayset
| CAML_Arraycopy
| CAML_Arraylength
| CAML_Stringmake
| CAML_Stringlength
| CAML_Stringget
| CAML_Stringsub
| CAML_Stringcat
| CAML_Stringcompare

type instruction =
  | Klabel of Label.t
  | Kacc of int
  | Kenvacc of int
  | Koffsetclosure of int
  | Kpush
  | Kpop of int
  | Kpush_retaddr of Label.t
  | Kshort_apply of int
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
  | Ksubstinstance of UVars.Instance.t
  | Kconst of structured_constant
  | Kmakeblock of int * tag
  | Kmakeswitchblock of Label.t * Label.t * annot_switch * int
  | Kswitch of Label.t array * Label.t array
  | Kpushfields of int
  | Kfield of int
  | Ksetfield of int
  | Kstop
  | Ksequence of bytecodes
  | Kproj of int
  | Kensurestackcapacity of int
  | Kbranch of Label.t                  (* jump to label *)
  | Kprim of CPrimitives.t * pconstant
  | Kcamlprim of caml_prim * Label.t

and bytecodes = instruction list

type fv_elem =
  | FVnamed of Id.t
  | FVrel of int

type fv = fv_elem array

(* --- Pretty print *)
open Pp
open Util

let caml_prim_to_prim = function
| CAML_Arraymake -> CPrimitives.Arraymake
| CAML_Arrayget -> CPrimitives.Arrayget
| CAML_Arraydefault -> CPrimitives.Arraydefault
| CAML_Arrayset -> CPrimitives.Arrayset
| CAML_Arraycopy -> CPrimitives.Arraycopy
| CAML_Arraylength -> CPrimitives.Arraylength
| CAML_Stringmake -> CPrimitives.Stringmake
| CAML_Stringlength -> CPrimitives.Stringlength
| CAML_Stringget -> CPrimitives.Stringget
| CAML_Stringsub -> CPrimitives.Stringsub
| CAML_Stringcat -> CPrimitives.Stringcat
| CAML_Stringcompare -> CPrimitives.Stringcompare

let pp_lbl lbl = str "L" ++ int lbl

let pp_fv_elem = function
  | FVnamed id -> str "FVnamed(" ++ Id.print id ++ str ")"
  | FVrel i -> str "Rel(" ++ int i ++ str ")"

let rec pp_instr i =
  match i with
  | Klabel _   | Ksequence _ -> assert false
  | Kacc n -> str "acc " ++ int n
  | Kenvacc n -> str "envacc " ++ int n
  | Koffsetclosure n -> str "offsetclosure " ++ int n
  | Kpush -> str "push"
  | Kpop n -> str "pop " ++ int n
  | Kpush_retaddr lbl -> str "push_retaddr " ++ pp_lbl lbl
  | Kshort_apply n -> str "short_apply " ++ int n
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
      hv 1 (str "closurerec " ++
             int fv ++ str ", " ++ int init ++
             str " types = " ++
             prlist_with_sep spc pp_lbl (Array.to_list lblt) ++
             str " bodies = " ++
             prlist_with_sep spc pp_lbl (Array.to_list lblb))
  | Kclosurecofix (fv,init,lblt,lblb) ->
      hv 1 (str "closurecofix " ++
             int fv ++ str ", " ++ int init ++
             str " types = " ++
             prlist_with_sep spc pp_lbl (Array.to_list lblt) ++
             str " bodies = " ++
             prlist_with_sep spc pp_lbl (Array.to_list lblb))
  | Kgetglobal idu -> str "getglobal " ++ Constant.print idu
  | Ksubstinstance u ->
    str "subst_instance " ++
    UVars.Instance.pr Sorts.QVar.raw_pr (Univ.Universe.pr Univ.Level.raw_pr) u
  | Kconst sc ->
      str "const " ++ pp_struct_const sc
  | Kmakeblock(n, m) ->
      str "makeblock " ++ int n ++ str ", " ++ int m
  | Kmakeswitchblock(lblt,lbls,_,sz) ->
      str "makeswitchblock " ++ pp_lbl lblt ++ str ", " ++
        pp_lbl lbls ++ str ", " ++ int sz
  | Kswitch(lblc,lblb) ->
      hv 1 (str "switch " ++
             prlist_with_sep spc pp_lbl (Array.to_list lblc) ++
             str " | " ++
             prlist_with_sep spc pp_lbl (Array.to_list lblb))
  | Kpushfields n -> str "pushfields " ++ int n
  | Kfield n -> str "field " ++ int n
  | Ksetfield n -> str "setfield " ++ int n

  | Kstop -> str "stop"

  | Kbranch lbl -> str "branch " ++ pp_lbl lbl

  | Kproj p -> str "proj " ++ int p

  | Kensurestackcapacity size -> str "growstack " ++ int size

  | Kprim (op, id) -> str (CPrimitives.to_string op) ++ str " " ++
        (Constant.print (fst id))

  | Kcamlprim (op, lbl) ->
    str "camlcall " ++ str (CPrimitives.to_string (caml_prim_to_prim op)) ++ str ", branch " ++
    pp_lbl lbl ++ str " on accu"

and pp_bytecodes c =
  match c with
  | [] -> str ""
  | Klabel lbl :: c ->
        str "L" ++ int lbl ++ str ":" ++ fnl () ++
        pp_bytecodes c
  | Ksequence l :: c ->
      pp_bytecodes l ++  pp_bytecodes c
  | i :: c ->
      pp_instr i ++ fnl () ++ pp_bytecodes c
