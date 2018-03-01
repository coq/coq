(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Vmvalues

external set_drawinstr : unit -> unit = "coq_set_drawinstr"

external mkPopStopCode : int -> tcode = "coq_pushpop"

let popstop_tbl =  ref (Array.init 30 mkPopStopCode)

let popstop_code i =
  let len = Array.length !popstop_tbl in
  if i < len then !popstop_tbl.(i)
  else
    begin
      popstop_tbl :=
	Array.init (i+10)
	  (fun j -> if j < len then !popstop_tbl.(j) else mkPopStopCode j);
      !popstop_tbl.(i)
    end

let stop = popstop_code 0

(************************************************)
(* Abstract machine *****************************)
(************************************************)

(* gestion de la pile *)
external push_ra : tcode -> unit = "coq_push_ra"
external push_val : values -> unit = "coq_push_val"
external push_arguments : arguments -> unit = "coq_push_arguments"
external push_vstack : vstack -> int -> unit = "coq_push_vstack"


(* interpreteur *)
external coq_interprete : tcode -> values -> atom array -> vm_global -> vm_env -> int -> values =
  "coq_interprete_byte" "coq_interprete_ml"

let interprete code v env k =
  coq_interprete code v (get_atom_rel ()) (Csymtable.get_global_data ()) env k

(* Functions over arguments *)

(* Apply a value to arguments contained in [vargs] *)
let apply_arguments vf vargs =
  let n = nargs vargs in
  if Int.equal n 0 then fun_val vf
  else
   begin
     push_ra stop;
     push_arguments vargs;
     interprete (fun_code vf) (fun_val vf) (fun_env vf) (n - 1)
   end

(* Apply value [vf] to an array of argument values [varray] *)
let apply_varray vf varray =
  let n = Array.length varray in
  if Int.equal n 0 then fun_val vf
  else
    begin
      push_ra stop;
      (* The fun code of [vf] will make sure we have enough stack, so we put 0
         here. *)
      push_vstack varray 0;
      interprete (fun_code vf) (fun_val vf) (fun_env vf) (n - 1)
    end

let mkrel_vstack k arity =
  let max = k + arity - 1 in
  Array.init arity (fun i -> val_of_rel (max - i))

let reduce_fun k vf =
  let vargs = mkrel_vstack k 1 in
  apply_varray vf vargs

let decompose_vfun2 k vf1 vf2 =
  let arity = min (closure_arity vf1) (closure_arity vf2) in
  assert (0 < arity && arity < Sys.max_array_length);
  let vargs = mkrel_vstack k arity in
  let v1 = apply_varray vf1 vargs in
  let v2 = apply_varray vf2 vargs in
  arity, v1, v2

(* Functions over vfix *)

let reduce_fix k vf =
  let fb = first_fix vf in
  (* computing types *)
  let fc_typ = fix_types fb in
  let ndef = Array.length fc_typ in
  let et = offset_closure_fix fb (2*(ndef - 1)) in
  let ftyp =
    Array.map
      (fun c -> interprete c crazy_val et 0) fc_typ in
  (* Construction of the environment of fix bodies *)
  (mk_fix_body k ndef fb, ftyp)

let reduce_cofix k vcf =
  let fc_typ = cofix_types vcf in
  let ndef = Array.length fc_typ in
  let ftyp =
    (* Evaluate types *)
    Array.map (fun c -> interprete c crazy_val (cofix_env vcf) 0) fc_typ in

  (* Construction of the environment of cofix bodies *)
  (mk_cofix_body apply_varray k ndef vcf, ftyp)

let type_of_switch sw =
  (* The fun code of types will make sure we have enough stack, so we put 0
  here. *)
  push_vstack sw.sw_stk 0;
  interprete sw.sw_type_code crazy_val sw.sw_env 0

let apply_switch sw arg =
  let tc = sw.sw_annot.tailcall in
  if tc then
    (push_ra stop;push_vstack sw.sw_stk sw.sw_annot.max_stack_size)
  else
    (push_vstack sw.sw_stk sw.sw_annot.max_stack_size;
     push_ra (popstop_code (Array.length sw.sw_stk)));
  interprete sw.sw_code arg sw.sw_env 0

let branch_of_switch k sw =
  let eval_branch (_,arity as ta) =
    let arg = branch_arg k ta in
    let v = apply_switch sw arg in
    (arity, v)
  in
  Array.map eval_branch sw.sw_annot.rtbl

(* Apply the term represented by a under stack stk to argument v *)
(* t = a stk --> t v *)
let rec apply_stack a stk v =
  match stk with
  | [] -> apply_varray (fun_of_val a) [|v|]
  | Zapp args :: stk -> apply_stack (apply_arguments (fun_of_val a) args) stk v
  | Zproj kn :: stk -> apply_stack (val_of_proj kn a) stk v
  | Zfix(f,args) :: stk ->
      let a,stk = 
	match stk with
	| Zapp args' :: stk ->
	    push_ra stop;
	    push_arguments args';
	    push_val a;
	    push_arguments args;
	    let a =
              interprete (fix_code f) (fix_val f) (fix_env f)
		(nargs args+ nargs args') in
	    a, stk
	| _ -> 
	    push_ra stop;
	    push_val a;
	    push_arguments args;
	    let a =
              interprete (fix_code f) (fix_val f) (fix_env f)
		(nargs args) in
	    a, stk in
      apply_stack a stk v
  | Zswitch sw :: stk ->
      apply_stack (apply_switch sw a) stk v

let apply_whd k whd =
  let v = val_of_rel k in
  match whd with
  | Vprod _ | Vconstr_const _ | Vconstr_block _ -> assert false
  | Vfun f -> reduce_fun k f
  | Vfix(f, None) -> 
      push_ra stop;
      push_val v;
      interprete (fix_code f) (fix_val f) (fix_env f) 0
  | Vfix(f, Some args) ->
      push_ra stop;
      push_val v;
      push_arguments args;
      interprete (fix_code f) (fix_val f) (fix_env f) (nargs args)
  | Vcofix(_,to_up,_) ->
      push_ra stop;
      push_val v;
      interprete (cofix_upd_code to_up) (cofix_upd_val to_up) (cofix_upd_env to_up) 0
  | Vatom_stk(a,stk) ->
      apply_stack (val_of_atom a) stk v
  | Vuniv_level lvl -> assert false

