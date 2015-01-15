(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Cbytecodes

external set_drawinstr : unit -> unit = "coq_set_drawinstr"

(******************************************)
(* Utility Functions about Obj ************)
(******************************************)

external offset_closure : Obj.t -> int -> Obj.t = "coq_offset_closure"
external offset : Obj.t -> int = "coq_offset"

let accu_tag = 0

(*******************************************)
(* Initalization of the abstract machine ***)
(*******************************************)

external init_vm : unit -> unit = "init_coq_vm"

let _ = init_vm ()

external transp_values : unit -> bool = "get_coq_transp_value"
external set_transp_values : bool -> unit = "coq_set_transp_value"

(*******************************************)
(* Machine code *** ************************)
(*******************************************)

type tcode
let tcode_of_obj v = ((Obj.obj v):tcode)
let fun_code v = tcode_of_obj (Obj.field (Obj.repr v) 0)

external mkAccuCode : int -> tcode = "coq_makeaccu"
external mkPopStopCode : int -> tcode = "coq_pushpop"

external offset_tcode : tcode -> int -> tcode = "coq_offset_tcode"
external int_tcode : tcode -> int -> int = "coq_int_tcode"

external accumulate : unit -> tcode = "accumulate_code"
let accumulate = accumulate ()

external is_accumulate : tcode -> bool = "coq_is_accumulate_code"

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

(******************************************************)
(* Abstract data types and utility functions **********)
(******************************************************)

(* Values of the abstract machine *)
let val_of_obj v = ((Obj.obj v):values)
let crazy_val = (val_of_obj (Obj.repr 0))

(* Abstract data *)
type vprod
type vfun
type vfix
type vcofix
type vblock
type arguments

type vm_env
type vstack = values array

type vswitch = {
    sw_type_code : tcode;
    sw_code : tcode;
    sw_annot : annot_switch;
    sw_stk : vstack;
    sw_env : vm_env
  }

(* Representation of values *)
(* + Products : *)
(*   -   vprod = 0_[ dom | codom]                                         *)
(*             dom : values, codom : vfun                                 *)
(*                                                                        *)
(* + Functions have two representations :                                 *)
(*   - unapplied fun :  vf = Ct_[ C | fv1 | ... | fvn]                    *)
(*                                       C:tcode, fvi : values            *)
(*     Remark : a function and its environment is the same value.         *)
(*   - partially applied fun : Ct_[Restart:C| vf | arg1 | ... argn]       *)
(*                                                                        *)
(* + Fixpoints :                                                          *)
(*   -        Ct_[C1|Infix_t|C2|...|Infix_t|Cn|fv1|...|fvn]               *)
(*     One single block to represent all of the fixpoints, each fixpoint  *)
(*     is the pointer to the field holding the pointer to its code, and   *)
(*     the infix tag is used to know where the block starts.              *)
(*   - Partial application follows the scheme of partially applied        *)
(*     functions. Note: only fixpoints not having been applied to its     *)
(*     recursive argument are coded this way. When the rec. arg. is       *)
(*     applied, either it's a constructor and the fix reduces, or it's    *)
(*     and the fix is coded as an accumulator.                            *)
(*                                                                        *)
(* + Cofixpoints : see cbytegen.ml                                        *)
(*                                                                        *)
(* + vblock's encode (non constant) constructors as in Ocaml, but         *)
(*   starting from 0 up. tag 0 ( = accu_tag) is reserved for              *)
(*   accumulators.                                                        *)
(*                                                                        *)
(* + vm_env is the type of the machine environments (i.e. a function or   *)
(*   a fixpoint)                                                          *)
(*                                                                        *)
(* + Accumulators : At_[accumulate| accu | arg1 | ... | argn ]            *)
(*   - representation of [accu] : tag_[....]                              *)
(*     -- tag <= 2 : encoding atom type (sorts, free vars, etc.)          *)
(*     -- 3_[accu|fix_app] : a fixpoint blocked by an accu                *)
(*     -- 4_[accu|vswitch] : a match blocked by an accu                   *)
(*     -- 5_[fcofix]       : a cofix function                             *)
(*     -- 6_[fcofix|val]   : a cofix function, val represent the value    *)
(*        of the function applied to arg1 ... argn                        *)
(* The [arguments] type, which is abstracted as an array, represents :    *)
(*          tag[ _ | _ |v1|... | vn]                                      *)
(* Generally the first field is a code pointer.                           *)

(* Do not edit this type without editing C code, especially "coq_values.h" *)

type atom =
  | Aid of Vars.id_key
  | Aiddef of Vars.id_key * values
  | Aind of pinductive

(* Zippers *)

type zipper =
  | Zapp of arguments
  | Zfix of vfix*arguments  (* Possibly empty *)
  | Zswitch of vswitch

type stack = zipper list

type to_up = values

type whd =
  | Vsort of sorts
  | Vprod of vprod
  | Vfun of vfun
  | Vfix of vfix * arguments option
  | Vcofix of vcofix * to_up * arguments option
  | Vconstr_const of int
  | Vconstr_block of vblock
  | Vatom_stk of atom * stack

(*************************************************)
(* Destructors ***********************************)
(*************************************************)

let rec whd_accu a stk =
  let stk =
    if Int.equal (Obj.size a) 2 then stk
    else Zapp (Obj.obj a) :: stk in
  let at = Obj.field a 1 in
  match Obj.tag at with
  | i when i <= 2 ->
      Vatom_stk(Obj.magic at, stk)
  | 3 (* fix_app tag *) ->
      let fa = Obj.field at 1 in
      let zfix  =
	Zfix (Obj.obj (Obj.field fa 1), Obj.obj fa) in
      whd_accu (Obj.field at 0) (zfix :: stk)
  | 4 (* switch tag  *) ->
      let zswitch = Zswitch (Obj.obj (Obj.field at 1)) in
      whd_accu (Obj.field at 0) (zswitch :: stk)
  | 5 (* cofix_tag *) ->
      let vcfx = Obj.obj (Obj.field at 0) in
      let to_up = Obj.obj a in
      begin match stk with
      | []          -> Vcofix(vcfx, to_up, None)
      | [Zapp args] -> Vcofix(vcfx, to_up, Some args)
      | _           -> assert false
      end
  | 6 (* cofix_evaluated_tag *) ->
      let vcofix = Obj.obj (Obj.field at 0) in
      let res = Obj.obj a in
      begin match stk with
      | []          -> Vcofix(vcofix, res, None)
      | [Zapp args] -> Vcofix(vcofix, res, Some args)
      | _           -> assert false
      end
  | _ -> assert false

external kind_of_closure : Obj.t -> int = "coq_kind_of_closure"

let whd_val : values -> whd =
  fun v ->
    let o = Obj.repr v in
    if Obj.is_int o then Vconstr_const (Obj.obj o)
    else
      let tag = Obj.tag o in
      if tag = accu_tag then
	(
	if Int.equal (Obj.size o) 1 then Obj.obj o (* sort *)
	else
	  if is_accumulate (fun_code o) then whd_accu o []
	  else (Vprod(Obj.obj o)))
      else
	if tag = Obj.closure_tag || tag = Obj.infix_tag then
	  (	   match kind_of_closure o with
	   | 0 -> Vfun(Obj.obj o)
	   | 1 -> Vfix(Obj.obj o, None)
	   | 2 -> Vfix(Obj.obj (Obj.field o 1), Some (Obj.obj o))
	   | 3 -> Vatom_stk(Aid(RelKey(int_tcode (fun_code o) 1)), [])
	   | _ -> Errors.anomaly ~label:"Vm.whd " (Pp.str "kind_of_closure does not work"))
	else Vconstr_block(Obj.obj o)



(************************************************)
(* Abstrct machine ******************************)
(************************************************)

(* gestion de la pile *)
external push_ra : tcode -> unit = "coq_push_ra"
external push_val : values -> unit = "coq_push_val"
external push_arguments : arguments -> unit = "coq_push_arguments"
external push_vstack : vstack -> unit = "coq_push_vstack"


(* interpreteur *)
external interprete : tcode -> values -> vm_env -> int -> values =
  "coq_interprete_ml"



(* Functions over arguments *)
let nargs : arguments -> int = fun args -> (Obj.size (Obj.repr args)) - 2
let arg args i =
  if  0 <= i && i < (nargs args) then
    val_of_obj (Obj.field (Obj.repr args) (i+2))
  else invalid_arg
		("Vm.arg size = "^(string_of_int (nargs args))^
		 " acces "^(string_of_int i))

let apply_arguments vf vargs =
  let n = nargs vargs in
  if Int.equal n 0 then vf
  else
   begin
     push_ra stop;
     push_arguments vargs;
     interprete (fun_code vf) vf (Obj.magic vf) (n - 1)
   end

let apply_vstack vf vstk =
  let n = Array.length vstk in
  if Int.equal n 0 then vf
  else
    begin
      push_ra stop;
      push_vstack vstk;
      interprete (fun_code vf) vf (Obj.magic vf) (n - 1)
    end

(**********************************************)
(* Constructors *******************************)
(**********************************************)

let obj_of_atom : atom -> Obj.t =
  fun a ->
    let res = Obj.new_block accu_tag 2 in
    Obj.set_field res 0 (Obj.repr accumulate);
    Obj.set_field res 1 (Obj.repr a);
    res

(* obj_of_str_const : structured_constant -> Obj.t *)
let rec obj_of_str_const str =
  match str with
  | Const_sorts s -> Obj.repr (Vsort s)
  | Const_ind ind -> obj_of_atom (Aind ind)
  | Const_b0 tag -> Obj.repr tag
  | Const_bn(tag, args) ->
      let len = Array.length args in
      let res = Obj.new_block tag len in
      for i = 0 to len - 1 do
	Obj.set_field res i (obj_of_str_const args.(i))
      done;
      res

let val_of_obj o = ((Obj.obj o) : values)

let val_of_str_const str = val_of_obj (obj_of_str_const str)

let val_of_atom a = val_of_obj (obj_of_atom a)

module IdKeyHash =
struct
  type t = pconstant tableKey
  let equal = Names.eq_table_key (Univ.eq_puniverses Constant.equal)
  open Hashset.Combine
  let hash = function
  | ConstKey (c,u) -> combinesmall 1 (Constant.hash c)
  | VarKey id -> combinesmall 2 (Id.hash id)
  | RelKey i -> combinesmall 3 (Int.hash i)
end

module KeyTable = Hashtbl.Make(IdKeyHash)

let idkey_tbl = KeyTable.create 31

let val_of_idkey key =
  try KeyTable.find idkey_tbl key
  with Not_found ->
    let v = val_of_atom (Aid key) in
    KeyTable.add idkey_tbl key v;
    v

let val_of_rel k = val_of_idkey (RelKey k)

let val_of_named id = val_of_idkey (VarKey id)

let val_of_constant c = val_of_idkey (ConstKey c)

external val_of_annot_switch : annot_switch -> values = "%identity"

let mkrel_vstack k arity =
  let max = k + arity - 1 in
  Array.init arity (fun i -> val_of_rel (max - i))


(*************************************************)
(** Operations manipulating data types ***********)
(*************************************************)

(* Functions over products *)

let dom : vprod -> values = fun p -> val_of_obj (Obj.field (Obj.repr p) 0)
let codom : vprod -> vfun = fun p -> (Obj.obj (Obj.field (Obj.repr p) 1))

(* Functions over vfun *)

external closure_arity : vfun -> int = "coq_closure_arity"

let body_of_vfun k vf =
  let vargs = mkrel_vstack k 1 in
  apply_vstack (Obj.magic vf) vargs

let decompose_vfun2 k vf1 vf2 =
  let arity = min (closure_arity vf1) (closure_arity vf2) in
  assert (0 < arity && arity < Sys.max_array_length);
  let vargs = mkrel_vstack k arity in
  let v1 = apply_vstack (Obj.magic vf1) vargs in
  let v2 = apply_vstack (Obj.magic vf2) vargs in
  arity, v1, v2

(* Functions over fixpoint *)

let first o = (offset_closure o (offset o))
let last o = (Obj.field o (Obj.size o - 1))

let current_fix vf = - (offset (Obj.repr vf) / 2)

let unsafe_fb_code fb i = tcode_of_obj (Obj.field (Obj.repr fb) (2 * i))

let unsafe_rec_arg fb i = int_tcode (unsafe_fb_code fb i) 1

let rec_args vf =
  let fb = first (Obj.repr vf) in
  let size = Obj.size (last fb) in
  Array.init size (unsafe_rec_arg fb)

exception FALSE

let check_fix f1 f2 =
  let i1, i2 = current_fix f1, current_fix f2 in
  (* Checking starting point *)
  if i1 = i2 then
    let fb1,fb2 = first (Obj.repr f1), first (Obj.repr f2) in
    let n = Obj.size (last fb1) in
    (* Checking number of definitions *)
    if n = Obj.size (last fb2) then
      (* Checking recursive arguments *)
      try
	for i = 0 to n - 1 do
	  if unsafe_rec_arg fb1 i <> unsafe_rec_arg fb2 i
	  then raise FALSE
	done;
	true
      with FALSE -> false
    else false
  else false

(* Functions over vfix *)
external atom_rel : unit -> atom array = "get_coq_atom_tbl"
external realloc_atom_rel : int -> unit = "realloc_coq_atom_tbl"

let relaccu_tbl =
  let atom_rel = atom_rel() in
  let len = Array.length atom_rel in
  for i = 0 to len - 1 do atom_rel.(i) <- Aid (RelKey i) done;
  ref (Array.init len mkAccuCode)

let relaccu_code i =
  let len = Array.length !relaccu_tbl in
  if i < len then !relaccu_tbl.(i)
  else
    begin
      realloc_atom_rel i;
      let atom_rel = atom_rel () in
      let nl = Array.length atom_rel in
      for j = len to nl - 1 do atom_rel.(j) <- Aid(RelKey j) done;
      relaccu_tbl :=
	Array.init nl
	  (fun j -> if j < len then !relaccu_tbl.(j) else mkAccuCode j);
      !relaccu_tbl.(i)
    end

let reduce_fix k vf =
  let fb = first (Obj.repr vf) in
  (* computing types *)
  let fc_typ = ((Obj.obj (last fb)) : tcode array) in
  let ndef = Array.length fc_typ in
  let et = offset_closure fb (2*(ndef - 1)) in
  let ftyp =
    Array.map
      (fun c -> interprete c crazy_val (Obj.magic et) 0) fc_typ in
  (* Construction of the environment of fix bodies *)
  let e = Obj.dup fb in
  for i = 0 to ndef - 1 do
    Obj.set_field e (2 * i) (Obj.repr (relaccu_code (k + i)))
  done;
  let fix_body i =
    let jump_grabrec c = offset_tcode c 2 in
    let c = jump_grabrec (unsafe_fb_code fb i)  in
    let res = Obj.new_block Obj.closure_tag 2 in
    Obj.set_field res 0 (Obj.repr c);
    Obj.set_field res 1 (offset_closure e (2*i));
    ((Obj.obj res) : vfun)  in
  (Array.init ndef fix_body, ftyp)

(* Functions over vcofix *)

let get_fcofix vcf i =
  match whd_val (Obj.obj (Obj.field (Obj.repr vcf) (i+1))) with
  | Vcofix(vcfi, _, _) -> vcfi
  | _ -> assert false

let current_cofix vcf =
  let ndef = Obj.size (last (Obj.repr vcf)) in
  let rec find_cofix pos =
    if pos < ndef then
      if get_fcofix vcf pos == vcf then pos
      else find_cofix (pos+1)
    else raise Not_found in
  try find_cofix 0
  with Not_found -> assert false

let check_cofix vcf1 vcf2 =
  (current_cofix vcf1 = current_cofix vcf2) &&
  (Obj.size (last (Obj.repr vcf1)) = Obj.size (last (Obj.repr vcf2)))

let reduce_cofix k vcf =
  let fc_typ = ((Obj.obj (last (Obj.repr vcf))) : tcode array) in
  let ndef = Array.length fc_typ in
  let ftyp =
    (* Evaluate types *)
    Array.map (fun c -> interprete c crazy_val (Obj.magic vcf) 0) fc_typ in

  (* Construction of the environment of cofix bodies *)
  let e = Obj.dup (Obj.repr vcf) in
  for i = 0 to ndef - 1 do
    Obj.set_field e (i+1) (Obj.repr (val_of_rel (k+i)))
  done;

  let cofix_body i =
    let vcfi = get_fcofix vcf i in
    let c = Obj.field (Obj.repr vcfi) 0 in
    Obj.set_field e 0 c;
    let atom = Obj.new_block cofix_tag 1 in
    let self = Obj.new_block accu_tag 2 in
    Obj.set_field self 0 (Obj.repr accumulate);
    Obj.set_field self 1 (Obj.repr atom);
    apply_vstack (Obj.obj e) [|Obj.obj self|] in
  (Array.init ndef cofix_body, ftyp)


(* Functions over vblock *)

let btag : vblock -> int = fun b -> Obj.tag (Obj.repr b)
let bsize : vblock -> int = fun b -> Obj.size (Obj.repr b)
let bfield b i =
  if 0 <= i && i < (bsize b) then val_of_obj (Obj.field (Obj.repr b) i)
  else invalid_arg "Vm.bfield"


(* Functions over vswitch *)

let check_switch sw1 sw2 = sw1.sw_annot.rtbl = sw2.sw_annot.rtbl

let case_info sw = sw.sw_annot.ci

let type_of_switch sw =
  push_vstack sw.sw_stk;
  interprete sw.sw_type_code crazy_val sw.sw_env 0

let branch_arg k (tag,arity) =
  if Int.equal arity 0 then  ((Obj.magic tag):values)
  else
    let b = Obj.new_block tag arity in
    for i = 0 to arity - 1 do
      Obj.set_field b i (Obj.repr (val_of_rel (k+i)))
    done;
    val_of_obj b

let apply_switch sw arg =
  let tc = sw.sw_annot.tailcall in
  if tc then
    (push_ra stop;push_vstack sw.sw_stk)
  else
    (push_vstack sw.sw_stk; push_ra (popstop_code (Array.length sw.sw_stk)));
  interprete sw.sw_code arg sw.sw_env 0

let branch_of_switch k sw =
  let eval_branch (_,arity as ta) =
    let arg = branch_arg k ta in
    let v = apply_switch sw arg in
    (arity, v)
  in
  Array.map eval_branch sw.sw_annot.rtbl



(* Evaluation *)

let rec whd_stack v stk =
  match stk with
  | [] -> whd_val v
  | Zapp args :: stkt -> whd_stack (apply_arguments v args) stkt
  | Zfix (f,args) :: stkt ->
      let o = Obj.repr v in
      if Obj.is_block o && Obj.tag o = accu_tag then
	whd_accu (Obj.repr v) stk
      else
	let v', stkt =
	  match stkt with
	  | Zapp args' :: stkt ->
	      push_ra stop;
	      push_arguments args';
	      push_val v;
	      push_arguments args;
	      let v' =
		interprete (fun_code f) (Obj.magic f) (Obj.magic f)
		  (nargs args+ nargs args') in
	      v', stkt
	  | _ ->
	      push_ra stop;
	      push_val v;
	      push_arguments args;
	      let v' =
		interprete (fun_code f) (Obj.magic f) (Obj.magic f)
		  (nargs args) in
	      v', stkt
	in
	whd_stack v' stkt
  | Zswitch sw :: stkt ->
      let o = Obj.repr v in
      if Obj.is_block o && Obj.tag o = accu_tag then
	if Obj.tag (Obj.field o 1) < cofix_tag then whd_accu (Obj.repr v) stk
	else
	  let to_up =
	    match whd_accu (Obj.repr v) [] with
	    | Vcofix (_, to_up, _) -> to_up
	    | _ -> assert false in
	  whd_stack (apply_switch sw to_up) stkt
      else whd_stack (apply_switch sw v) stkt

let rec force_whd v stk =
  match whd_stack v stk with
  | Vatom_stk(Aiddef(_,v),stk) -> force_whd v stk
  | res -> res


let rec eta_stack a stk v =
  match stk with
  | [] -> apply_vstack a [|v|]
  | Zapp args :: stk -> eta_stack (apply_arguments a args) stk v
  | Zfix(f,args) :: stk ->
      let a,stk = 
	match stk with
	| Zapp args' :: stk ->
	    push_ra stop;
	    push_arguments args';
	    push_val a;
	    push_arguments args;
	    let a =
	      interprete (fun_code f) (Obj.magic f) (Obj.magic f)
		(nargs args+ nargs args') in
	    a, stk
	| _ -> 
	    push_ra stop;
	    push_val a;
	    push_arguments args;
	    let a =
	      interprete (fun_code f) (Obj.magic f) (Obj.magic f)
		(nargs args) in
	    a, stk in
      eta_stack a stk v
  | Zswitch sw :: stk ->
      eta_stack (apply_switch sw a) stk v

let eta_whd k whd =
  let v = val_of_rel k in
  match whd with
  | Vsort _ | Vprod _ | Vconstr_const _ | Vconstr_block _ -> assert false
  | Vfun f -> body_of_vfun k f
  | Vfix(f, None) -> 
      push_ra stop;
      push_val v;
      interprete (fun_code f) (Obj.magic f) (Obj.magic f) 0
  | Vfix(f, Some args) ->
      push_ra stop;
      push_val v;
      push_arguments args;
      interprete (fun_code f) (Obj.magic f) (Obj.magic f) (nargs args) 
  | Vcofix(_,to_up,_) ->
      push_ra stop;
      push_val v;
      interprete (fun_code to_up) (Obj.magic to_up) (Obj.magic to_up) 0
  | Vatom_stk(a,stk) ->
      eta_stack (val_of_atom a) stk v 


      
      
