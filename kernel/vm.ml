open Obj
open Names
open Term
open Conv_oracle
open Cbytecodes


external set_drawinstr : unit -> unit = "coq_set_drawinstr"

(******************************************)
(* Fonctions en plus du module Obj ********)
(******************************************)

external offset_closure : t -> int -> t = "coq_offset_closure"
external offset : t -> int = "coq_offset"
let first o = (offset_closure o (offset o))
let last o = (field o (size o - 1))

let accu_tag = 0

(*******************************************)
(* Initalisation de la machine abstraite ***)
(*******************************************)

external init_vm : unit -> unit = "init_coq_vm"

let _ = init_vm ()

external transp_values : unit -> bool = "get_coq_transp_value"
external set_transp_values : bool -> unit = "coq_set_transp_value"

(*******************************************)
(* Le code machine  ************************)
(*******************************************)

type tcode 
let tcode_of_obj v = ((obj v):tcode)
let fun_code v = tcode_of_obj (field (repr v) 0)

external mkAccuCode : int -> tcode = "coq_makeaccu"
external mkPopStopCode : int -> tcode = "coq_pushpop"
external mkAccuCond : int -> tcode = "coq_accucond"

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
(* Types de donnees abstraites et fonctions associees *)
(******************************************************)

(* Values of the abstract machine *)
let val_of_obj v = ((obj v):values)
let crasy_val = (val_of_obj (repr 0))


(* Functions *)
type vfun  
(* v = [Tc | c | fv1 | ... | fvn ] *)
(*                  ^                       *)
(* [Tc | (Restart : c) | v | a1 | ... an] *)
(*              ^                                  *)

(* Products *)
type vprod 
(* [0 | dom : codom] *) 
(*     ^              *)
let dom : vprod -> values = fun p -> val_of_obj (field (repr p) 0) 
let codom : vprod -> vfun = fun p -> (obj (field (repr p) 1))

(* Arguments *)
type arguments 
(* arguments = [_ | _ | _ | a1 | ... | an] *)
(*                ^                        *)
let nargs : arguments -> int = fun args -> (size (repr args)) - 2

let unsafe_arg : arguments -> int -> values =
     fun args i ->  val_of_obj (field (repr args) (i+2))

let arg args i = 
  if  0 <= i && i < (nargs args) then unsafe_arg args i 
  else raise (Invalid_argument 
		("Vm.arg size = "^(string_of_int (nargs args))^
		 " acces "^(string_of_int i)))

(* Fixpoints *)
type vfix

(* [Tc|c0|Ti|c1|...|Ti|cn|fv1|...|fvn| [ct0|...|ctn]] *)
(*          ^                                         *)
type vfix_block 

let fix_init : vfix -> int = fun vf -> (offset (repr vf)/2)

let block_of_fix : vfix -> vfix_block = fun vf -> obj (first (repr vf))

let fix_block_type : vfix_block -> tcode array =
  fun fb -> (obj (last (repr fb)))

let fix_block_ndef : vfix_block -> int = 
  fun fb -> size (last (repr fb))

let fix_ndef vf = fix_block_ndef (block_of_fix vf)

let unsafe_fb_code : vfix_block -> int -> tcode =
  fun fb i -> tcode_of_obj (field (repr fb) (2 * i))

let unsafe_rec_arg fb i = int_tcode (unsafe_fb_code fb i) 1
  
let rec_args vf =
  let fb = block_of_fix vf in
  let size = fix_block_ndef fb in
  Array.init size (unsafe_rec_arg fb)

exception FALSE

let check_fix f1 f2 = 
  let i1, i2 = fix_init f1, fix_init f2 in
  (* Verification du point de depart *)
    if i1 = i2 then
      let fb1,fb2 = block_of_fix f1, block_of_fix f2 in
      let n = fix_block_ndef fb1 in
    (* Verification du nombre de definition *)
      if n = fix_block_ndef fb2 then
      (* Verification des arguments recursifs *)
	try
	  for i = 0 to n - 1 do
	    if not (unsafe_rec_arg fb1 i = unsafe_rec_arg fb2 i) then
	      raise FALSE
	  done;
	  true
	with FALSE -> false
      else false 
    else false

(* Partials applications of Fixpoints *)
type vfix_app
let fix : vfix_app -> vfix = 
  fun vfa -> ((obj (field (repr vfa) 1)):vfix)
let args_of_fix : vfix_app -> arguments =
  fun vfa -> ((magic  vfa) : arguments)

(* CoFixpoints *)
type vcofix 
type vcofix_block
let cofix_init : vcofix -> int = fun vcf -> (offset (repr vcf)/2)

let block_of_cofix : vcofix -> vcofix_block = fun vcf -> obj (first (repr vcf))

let cofix_block_ndef : vcofix_block -> int = 
  fun fb -> size (last (repr fb))

let cofix_ndef vcf= cofix_block_ndef (block_of_cofix vcf)

let cofix_block_type : vcofix_block -> tcode array =
  fun cfb -> (obj (last (repr cfb)))

let check_cofix cf1 cf2 = 
  cofix_init cf1 = cofix_init cf2 &&
  cofix_ndef cf1 = cofix_ndef cf2 

let cofix_arity c = int_tcode c 1

let unsafe_cfb_code : vcofix_block -> int -> tcode =
  fun cfb i -> tcode_of_obj (field (repr cfb) (2 * i))

(* Partials applications of CoFixpoints *)
type vcofix_app 
let cofix : vcofix_app -> vcofix = 
  fun vcfa -> ((obj (field (repr vcfa) 1)):vcofix)
let args_of_cofix : vcofix_app -> arguments = 
  fun vcfa -> ((magic  vcfa) : arguments)

(* Blocks *)
type vblock (* la representation Ocaml *)
let btag : vblock -> int = fun b -> tag (repr b)
let bsize : vblock -> int = fun b -> size (repr b)
let bfield b i =
  if 0 <= i && i < (bsize b) then
    val_of_obj (field (repr b) i)
  else raise (Invalid_argument "Vm.bfield")

(* Accumulators and atoms *)

type accumulator 
(* [Ta | accumulate | at | a1 | ... | an ] *)

type inv_rel_key = int

type id_key = inv_rel_key tableKey

type vstack = values array

type vm_env 

type vswitch = {
    sw_type_code : tcode; 
    sw_code : tcode; 
    sw_annot : annot_switch;
    sw_stk : vstack;
    sw_env : vm_env
  } 

type atom = 
  | Aid of id_key
  | Aiddef of id_key * values
  | Aind of inductive
  | Afix_app of accumulator * vfix_app
  | Aswitch of accumulator * vswitch

let atom_of_accu : accumulator -> atom =
  fun a -> ((obj (field (repr a) 1)) : atom)

let args_of_accu : accumulator -> arguments = 
  fun a -> ((magic a) : arguments)

let nargs_of_accu a = nargs (args_of_accu a)

(* Les zippers *)

type zipper =
  | Zapp of arguments
  | Zfix of vfix_app
  | Zswitch of vswitch

type stack = zipper list

type whd =
  | Vsort of sorts
  | Vprod of vprod 
  | Vfun of vfun
  | Vfix of vfix
  | Vfix_app of vfix_app
  | Vcofix of vcofix
  | Vcofix_app of vcofix_app
  | Vconstr_const of int
  | Vconstr_block of vblock
  | Vatom_stk of atom * stack
(* Les atomes sont forcement Aid Aiddef Aind *)

(**********************************************)
(* Constructeurs ******************************)
(**********************************************)
(* obj_of_atom : atom -> t *)
let obj_of_atom : atom -> t =
  fun a -> 
    let res = Obj.new_block accu_tag 2 in
    set_field res 0 (repr accumulate);
    set_field res 1 (repr a);
    res 

(* obj_of_str_const : structured_constant -> t *)
let rec obj_of_str_const str =
  match str with 
  | Const_sorts s -> repr (Vsort s)
  | Const_ind ind -> obj_of_atom (Aind ind)
  | Const_b0 tag -> repr tag
  | Const_bn(tag, args) ->
      let len = Array.length args in
      let res = new_block tag len in
      for i = 0 to len - 1 do 
	set_field res i (obj_of_str_const args.(i)) 
      done;
      res

let val_of_obj o = ((obj o) : values)

let val_of_str_const str = val_of_obj (obj_of_str_const str)

let val_of_atom a = val_of_obj (obj_of_atom a)

let idkey_tbl = Hashtbl.create 31

let val_of_idkey key =
  try Hashtbl.find idkey_tbl key 
  with Not_found -> 
    let v = val_of_atom (Aid key) in
    Hashtbl.add idkey_tbl key v;
    v

let val_of_rel k = val_of_idkey (RelKey k)
let val_of_rel_def k v = val_of_atom(Aiddef(RelKey k, v))

let val_of_named id = val_of_idkey (VarKey id)
let val_of_named_def id v = val_of_atom(Aiddef(VarKey id, v))
  
let val_of_constant c = val_of_idkey (ConstKey c)
let val_of_constant_def n c v = 
  let res = Obj.new_block accu_tag 2 in
  set_field res 0 (repr (mkAccuCond n));
  set_field res 1 (repr (Aiddef(ConstKey c, v)));
  val_of_obj res 



(*************************************************)
(* Destructors ***********************************)
(*************************************************)


let rec whd_accu a stk =
  let n = nargs_of_accu a in
  let stk = 
    if nargs_of_accu a = 0 then stk
    else Zapp (args_of_accu a) :: stk in
  let at = atom_of_accu a in 
  match at with
  | Aid _ | Aiddef _ | Aind _ -> Vatom_stk(at, stk)
  | Afix_app(a,fa) -> whd_accu a (Zfix fa :: stk)
  | Aswitch(a,sw) -> whd_accu a (Zswitch sw :: stk)

external kind_of_closure : t -> int = "coq_kind_of_closure"

let whd_val : values -> whd =
  fun v -> 
    let o = repr v in 
    if is_int o then Vconstr_const (obj o)
    else 
      let tag = tag o in
      if tag = accu_tag then
	if is_accumulate (fun_code o) then whd_accu (obj o) []
	else 
	  if size o = 1 then Vsort(obj (field o 0))
	  else Vprod(obj o)
      else 
	if tag = closure_tag || tag = infix_tag then
	  match kind_of_closure o with
	  | 0 -> Vfun(obj o)
	  | 1 -> Vfix(obj o)
	  | 2 -> Vfix_app(obj o) 
	  | 3 -> Vcofix(obj o)
	  | 4 -> Vcofix_app(obj o)
	  | 5 -> Vatom_stk(Aid(RelKey(int_tcode (fun_code o) 1)), [])
	  | _ -> Util.anomaly "Vm.whd : kind_of_closure does not work"
	else Vconstr_block(obj o)
	


(************************************************)
(* La machine abstraite *************************)
(************************************************)


(* gestion de la pile *)
external push_ra : tcode -> unit = "coq_push_ra"
external push_val : values -> unit = "coq_push_val"
external push_arguments : arguments -> unit = "coq_push_arguments"
external push_vstack : vstack -> unit = "coq_push_vstack"


(* interpreteur *)
external interprete : tcode -> values -> vm_env -> int -> values =
  "coq_interprete_ml"

let apply_arguments vf vargs =
  let n = nargs vargs in
  if n = 0 then vf 
  else
   begin
     push_ra stop;
     push_arguments vargs;
     interprete (fun_code vf) vf (magic vf) (n - 1)
   end

let apply_vstack vf vstk =
  let n = Array.length vstk in
  if n = 0 then vf
  else 
    begin
      push_ra stop;
      push_vstack vstk;
      interprete (fun_code vf) vf (magic vf) (n - 1)
    end

let apply_fix_app vfa arg =
  let vf = fix vfa in
  let vargs = args_of_fix vfa in
  push_ra stop;
  push_val arg;
  push_arguments vargs;
  interprete (fun_code vf) (magic vf) (magic vf) (nargs vargs)

external set_forcable : unit -> unit = "coq_set_forcable"
let force_cofix v =
  match whd_val v with
  | Vcofix _    | Vcofix_app _ ->
      push_ra stop;
      set_forcable ();
      interprete (fun_code v) (magic v) (magic v) 0
  | _ -> v
  
let apply_switch sw arg =
  let arg = force_cofix arg in
  let tc = sw.sw_annot.tailcall in
  if tc then 
    (push_ra stop;push_vstack sw.sw_stk)
  else 
    (push_vstack sw.sw_stk; push_ra (popstop_code (Array.length sw.sw_stk)));
  interprete sw.sw_code arg sw.sw_env 0

let is_accu v = 
  is_block (repr v) && tag (repr v) = accu_tag && 
  fun_code v == accumulate 

let rec whd_stack v stk =  
  match stk with
  | [] -> whd_val v
  | Zapp a :: stkt -> whd_stack (apply_arguments v a) stkt
  | Zfix fa :: stkt -> 
      if is_accu v then whd_accu (magic v) stk
      else whd_stack (apply_fix_app fa v) stkt
  | Zswitch sw :: stkt -> 
      if is_accu v then whd_accu (magic v) stk 
      else whd_stack (apply_switch sw v) stkt 

let rec force_whd v stk =
  match whd_stack v stk with
  | Vatom_stk(Aiddef(_,v),stk) -> force_whd v stk
  | res -> res

	  

(* Function *)
external closure_arity : vfun -> int = "coq_closure_arity"

(* [apply_rel v k arity] applique la valeurs [v] aux arguments 
   [k],[k+1], ... , [k+arity-1] *)
let mkrel_vstack k arity =
  let max = k + arity - 1 in
  Array.init arity (fun i -> val_of_rel (max - i))

let body_of_vfun k vf =
  let vargs = mkrel_vstack k 1 in
  apply_vstack (magic vf) vargs

let decompose_vfun2 k vf1 vf2 =
  let arity = min (closure_arity vf1) (closure_arity vf2) in
  assert (0 <= arity && arity < Sys.max_array_length);
  let vargs = mkrel_vstack k arity in
  let v1 = apply_vstack (magic vf1) vargs in
  let v2 = apply_vstack (magic vf2) vargs in
  arity, v1, v2
    
  
(* Fix *)
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

let jump_grabrec c = offset_tcode c 2
let jump_grabrecrestart c = offset_tcode c 3

let bodies_of_fix k vf = 
  let fb = block_of_fix vf in
  let ndef = fix_block_ndef fb in
  (* Construction de l' environnement des corps des points fixes *)
  let e = dup (repr fb) in
  for i = 0 to ndef - 1 do
    set_field e (2 * i) (repr (relaccu_code (k + i)))
  done;
  let fix_body i =
    let c = jump_grabrec (unsafe_fb_code fb i)  in
    let res = Obj.new_block closure_tag 2 in
    set_field res 0 (repr c);
    set_field res 1 (offset_closure e (2*i));
    ((obj res) : vfun)
  in Array.init ndef fix_body
 
let types_of_fix vf =
  let fb = block_of_fix vf in
  let type_code = fix_block_type fb in
  let type_val c = interprete c crasy_val (magic fb) 0 in
  Array.map type_val type_code

 
(* CoFix *)
let jump_cograb c = offset_tcode c 2
let jump_cograbrestart c = offset_tcode c 3 

let bodies_of_cofix k vcf =
  let cfb = block_of_cofix vcf in
  let ndef = cofix_block_ndef cfb in
  (* Construction de l' environnement des corps des cofix *)
  let e = dup (repr cfb) in
  for i = 0 to ndef - 1 do
    set_field e (2 * i) (repr (relaccu_code (k + i)))
  done;
  let cofix_body i =
    let c = unsafe_cfb_code cfb i in 
    let arity = int_tcode c 1 in
    if arity = 0 then 
      begin
	push_ra stop;
	interprete (jump_cograbrestart c) crasy_val 
	  (obj (offset_closure e (2*i))) 0
      end
    else 
      let res = Obj.new_block closure_tag 2 in
      set_field res 0 (repr (jump_cograb c));
      set_field res 1 (offset_closure e (2*i));
      ((obj res) : values)
  in Array.init ndef cofix_body

let types_of_cofix vcf =
  let cfb = block_of_cofix vcf in
  let type_code = cofix_block_type cfb in
  let type_val c = interprete c crasy_val (magic cfb) 0 in
  Array.map type_val type_code

(* Switch *)
      
let eq_tbl sw1 sw2 = sw1.sw_annot.rtbl = sw2.sw_annot.rtbl 
    
let case_info sw = sw.sw_annot.ci
    
let type_of_switch sw = 
  push_vstack sw.sw_stk;
  interprete sw.sw_type_code crasy_val sw.sw_env 0 
    
let branch_arg k (tag,arity) = 
  if arity = 0 then  ((magic tag):values)
  else
    let b = new_block tag arity in
    for i = 0 to arity - 1 do
      set_field b i (repr (val_of_rel (k+i)))
    done;
    val_of_obj b
  
      
let branch_of_switch k sw =
  let eval_branch (_,arity as ta) =
    let arg = branch_arg k ta in
    let v = apply_switch sw arg in
    (arity, v)
  in 
  Array.map eval_branch sw.sw_annot.rtbl
    

    























