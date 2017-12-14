(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Cbytecodes
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
external interprete : tcode -> values -> vm_env -> int -> values =
  "coq_interprete_ml"

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

(*************************************************)
(* Destructors ***********************************)
(*************************************************)

let uni_lvl_val (v : values) : Univ.Level.t =
    let whd = Obj.magic v in
    match whd with
    | Vuniv_level lvl -> lvl
    | _ ->
      let pr =
        let open Pp in
        match whd with
        | Vsort _ -> str "Vsort"
        | Vprod _ -> str "Vprod"
        | Vfun _ -> str "Vfun"
        | Vfix _ -> str "Vfix"
        | Vcofix _ -> str "Vcofix"
        | Vconstr_const _i -> str "Vconstr_const"
        | Vconstr_block _b -> str "Vconstr_block"
        | Vatom_stk (_a,_stk) -> str "Vatom_stk"
        | _ -> assert false
      in
      CErrors.anomaly
        Pp.(   strbrk "Parsing virtual machine value expected universe level, got "
            ++ pr ++ str ".")

let rec whd_accu a stk =
  let stk =
    if Int.equal (Obj.size a) 2 then stk
    else Zapp (Obj.obj a) :: stk in
  let at = Obj.field a 1 in
  match Obj.tag at with
  | i when Int.equal i type_atom_tag ->
     begin match stk with
     | [Zapp args] ->
	let u = ref (Obj.obj (Obj.field at 0)) in
	for i = 0 to nargs args - 1 do
	  u := Univ.Universe.sup !u (Univ.Universe.make (uni_lvl_val (arg args i)))
	done;
	Vsort (Type !u)
     | _ -> assert false
     end
  | i when i <= max_atom_tag ->
      Vatom_stk(Obj.magic at, stk)
  | i when Int.equal i proj_tag ->
     let zproj = Zproj (Obj.obj (Obj.field at 0)) in
     whd_accu (Obj.field at 1) (zproj :: stk)
  | i when Int.equal i fix_app_tag ->
      let fa = Obj.field at 1 in
      let zfix  =
	Zfix (Obj.obj (Obj.field fa 1), Obj.obj fa) in
      whd_accu (Obj.field at 0) (zfix :: stk)
  | i when Int.equal i switch_tag ->
      let zswitch = Zswitch (Obj.obj (Obj.field at 1)) in
      whd_accu (Obj.field at 0) (zswitch :: stk)
  | i when Int.equal i cofix_tag ->
      let vcfx = Obj.obj (Obj.field at 0) in
      let to_up = Obj.obj a in
      begin match stk with
      | []          -> Vcofix(vcfx, to_up, None)
      | [Zapp args] -> Vcofix(vcfx, to_up, Some args)
      | _           -> assert false
      end
  | i when Int.equal i cofix_evaluated_tag ->
      let vcofix = Obj.obj (Obj.field at 0) in
      let res = Obj.obj a in
      begin match stk with
      | []          -> Vcofix(vcofix, res, None)
      | [Zapp args] -> Vcofix(vcofix, res, Some args)
      | _           -> assert false
      end
  | tg ->
    CErrors.anomaly
      Pp.(strbrk "Failed to parse VM value. Tag = " ++ int tg ++ str ".")

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
	  else Vprod(Obj.obj o))
      else
	if tag = Obj.closure_tag || tag = Obj.infix_tag then
	  (match kind_of_closure o with
	   | 0 -> Vfun(Obj.obj o)
	   | 1 -> Vfix(Obj.obj o, None)
	   | 2 -> Vfix(Obj.obj (Obj.field o 1), Some (Obj.obj o))
	   | 3 -> Vatom_stk(Aid(RelKey(int_tcode (fun_code o) 1)), [])
	   | _ -> CErrors.anomaly ~label:"Vm.whd " (Pp.str "kind_of_closure does not work."))
	else
           Vconstr_block(Obj.obj o)

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
  | Const_proj p -> Obj.repr p
  | Const_b0 tag -> Obj.repr tag
  | Const_bn(tag, args) ->
      let len = Array.length args in
      let res = Obj.new_block tag len in
      for i = 0 to len - 1 do
	Obj.set_field res i (obj_of_str_const args.(i))
      done;
      res
  | Const_univ_level l -> Obj.repr (Vuniv_level l)
  | Const_type u -> obj_of_atom (Atype u)

let val_of_obj o = ((Obj.obj o) : values)

let val_of_str_const str = val_of_obj (obj_of_str_const str)

let val_of_atom a = val_of_obj (obj_of_atom a)

let atom_of_proj kn v =
  let r = Obj.new_block proj_tag 2 in
  Obj.set_field r 0 (Obj.repr kn);
  Obj.set_field r 1 (Obj.repr v);
  ((Obj.obj r) : atom)

let val_of_proj kn v =
  val_of_atom (atom_of_proj kn v)

module IdKeyHash =
struct
  type t = Constant.t tableKey
  let equal = Names.eq_table_key Constant.equal
  open Hashset.Combine
  let hash = function
  | ConstKey c -> combinesmall 1 (Constant.hash c)
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
  | Vuniv_level _lvl -> assert false

let rec pr_atom a =
  Pp.(match a with
  | Aid c -> str "Aid(" ++ (match c with
                            | ConstKey c -> Constant.print c
			    | RelKey i -> str "#" ++ int i
			    | _ -> str "...") ++ str ")"
  | Aind (mi,i) -> str "Aind(" ++ MutInd.print mi ++ str "#" ++ int i ++ str ")"
  | Atype _ -> str "Atype(")
and pr_whd w =
  Pp.(match w with
  | Vsort _ -> str "Vsort"
  | Vprod _ -> str "Vprod"
  | Vfun _ -> str "Vfun"
  | Vfix _ -> str "Vfix"
  | Vcofix _ -> str "Vcofix"
  | Vconstr_const i -> str "Vconstr_const(" ++ int i ++ str ")"
  | Vconstr_block _b -> str "Vconstr_block"
  | Vatom_stk (a,stk) -> str "Vatom_stk(" ++ pr_atom a ++ str ", " ++ pr_stack stk ++ str ")"
  | Vuniv_level _ -> assert false)
and pr_stack stk =
  Pp.(match stk with
      | [] -> str "[]"
      | s :: stk -> pr_zipper s ++ str " :: " ++ pr_stack stk)
and pr_zipper z =
  Pp.(match z with
  | Zapp args -> str "Zapp(len = " ++ int (nargs args) ++ str ")"
  | Zfix (_f,args) -> str "Zfix(..., len=" ++ int (nargs args) ++ str ")"
  | Zswitch _s -> str "Zswitch(...)"
  | Zproj c -> str "Zproj(" ++ Constant.print c ++ str ")")
