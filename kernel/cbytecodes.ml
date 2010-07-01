(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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
  | Const_ind of inductive
  | Const_b0 of int
  | Const_val of Term.values

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
  | Kgetglobal of constant
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

  | Kbranch of Label.t                  (* jump to label *)

  | Kprim of Native.prim_op * constant option 
  | Kprim_const of Native.prim_op * constant option * int 
  | Kcamlprim of Native.caml_prim * Label.t 
  | Kareint of int 



and bytecodes = instruction list

type fv_elem = FVnamed of identifier | FVrel of int

type fv = fv_elem array


exception Find_at of int

(* rend le numero du constructeur correspondant au tag [tag],
   [cst] = true si c'est un constructeur constant *)

let invert_tag cst tag reloc_tbl =
  try 
    for j = 0 to Array.length reloc_tbl - 1 do
      let tagj,arity = reloc_tbl.(j) in
      if tag = tagj && (cst && arity = 0 || not(cst || arity = 0)) then
	raise (Find_at j)
      else ()
    done;raise Not_found 
  with Find_at j -> (j+1)   
             (* Argggg, ces constructeurs de ... qui commencent a 1*)

(* --- Pretty print *)
open Pp
open Util

let pp_sort s = 
  match family_of_sort s with
  | InSet -> str "Set"
  | InProp -> str "Prop"
  | InType -> str "Type"

let pp_struct_const = function
  | Const_sorts s -> pp_sort s
  | Const_ind (mind, i) -> pr_mind mind ++ str"#" ++ int i
  | Const_b0 i -> int i
  | Const_val v -> str "values"

let pp_lbl lbl = str "L" ++ int lbl

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
  | Kgetglobal id -> str "getglobal " ++ pr_con id
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
  | Ksetfield n -> str "set field" ++ int n

  | Kstop -> str "stop"

  | Kbranch lbl -> str "branch " ++ pp_lbl lbl

  | Kprim (op, id) -> str (Native.prim_to_string op) ++ str " " ++
	(match id with Some id -> pr_con id | None -> str "")
  | Kprim_const (op, id, i) -> 
      str (Native.prim_to_string op) ++ str "_const " ++
	int i ++ str " " ++
	(match id with Some id -> pr_con id | None -> str "") 
  | Kcamlprim (p,lbl) -> 
      str "camlcall " ++ str (Native.caml_prim_to_string p) ++
	str " " ++ pp_lbl lbl
  | Kareint n -> str "areint " ++ int n

and pp_bytecodes c =
  match c with
  | [] -> str ""
  | Klabel lbl :: c ->
	str "L" ++ int lbl ++ str ":" ++ str "\n" ++
	pp_bytecodes c
  | Ksequence (l1, l2) :: c ->
      pp_bytecodes l1 ++ pp_bytecodes l2 ++  pp_bytecodes c
  | i :: c ->
      str "\t" ++ pp_instr i ++ str "\n" ++ pp_bytecodes c

let draw_instr c =
  pperrnl (pp_bytecodes c);
  flush_all()

