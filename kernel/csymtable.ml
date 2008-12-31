open Names
open Term
open Vm
open Cemitcodes
open Cbytecodes
open Declarations
open Pre_env
open Cbytegen


external tcode_of_code : emitcodes -> int -> tcode = "coq_tcode_of_code"
external free_tcode : tcode -> unit = "coq_static_free"
external eval_tcode : tcode -> values array -> values = "coq_eval_tcode"
 
(*******************)
(* Linkage du code *)
(*******************)

(* Table des globaux *)

(* [global_data] contient les valeurs des constantes globales 
   (axiomes,definitions), les annotations des switch et les structured 
   constant *)
external global_data : unit -> values array = "get_coq_global_data"

(* [realloc_global_data n] augmente de n la taille de [global_data] *)
external realloc_global_data : int -> unit = "realloc_coq_global_data"

let check_global_data n =
  if n >= Array.length (global_data()) then realloc_global_data n
  
let num_global = ref 0

let set_global v = 
  let n = !num_global in
  check_global_data n;
  (global_data()).(n) <- v;
  incr num_global;
  n

(* [global_transp],[global_boxed] contiennent les valeurs des 
   definitions gelees. Les deux versions sont maintenues en //. 
   [global_transp] contient la version transparente.
   [global_boxed] contient la version gelees. *)

external global_boxed : unit -> bool array = "get_coq_global_boxed"

(* [realloc_global_data n] augmente de n la taille de [global_data] *)
external realloc_global_boxed : int -> unit = "realloc_coq_global_boxed"

let check_global_boxed n =
  if n >= Array.length (global_boxed()) then realloc_global_boxed n
  
let num_boxed = ref 0

let boxed_tbl = Hashtbl.create 53

let cst_opaque = ref Cpred.full

let is_opaque kn = Cpred.mem kn !cst_opaque

let set_global_boxed kn v = 
  let n = !num_boxed in
  check_global_boxed n;
  (global_boxed()).(n) <- (is_opaque kn);
  Hashtbl.add boxed_tbl kn n ;
  incr num_boxed;
  set_global (val_of_constant_def n kn v)

(* table pour les structured_constant et les annotations des switchs *)

let str_cst_tbl = Hashtbl.create 31
    (* (structured_constant * int) Hashtbl.t*)

let annot_tbl = Hashtbl.create 31
    (* (annot_switch * int) Hashtbl.t  *)

(*************************************************************)
(*** Mise a jour des valeurs des variables et des constantes *)
(*************************************************************)

exception NotEvaluated

let key rk =
  match !rk with
  | Some k -> k
  | _ -> raise NotEvaluated

(************************)
(* traduction des patch *)

(* slot_for_*, calcul la valeur de l'objet, la place
   dans la table global, rend sa position dans la table *)
 
let slot_for_str_cst key =
  try Hashtbl.find str_cst_tbl key 
  with Not_found -> 
    let n = set_global (val_of_str_const key) in
    Hashtbl.add str_cst_tbl key n;
    n

let slot_for_annot key =
  try Hashtbl.find annot_tbl key 
  with Not_found -> 
    let n =  set_global (Obj.magic key) in
    Hashtbl.add annot_tbl key n;
    n

let rec slot_for_getglobal env kn =
  let (cb,rk) = lookup_constant_key kn env in
  try key rk
  with NotEvaluated ->
    let pos =
      match Cemitcodes.force cb.const_body_code with
      | BCdefined(boxed,(code,pl,fv)) -> 
	let v = eval_to_patch env (code,pl,fv) in
  	if boxed then set_global_boxed kn v 
	else set_global v 
    | BCallias kn' -> slot_for_getglobal env kn' 
    | BCconstant -> set_global (val_of_constant kn) in
    rk := Some pos;
    pos

and slot_for_fv env fv =
  match fv with
  | FVnamed id -> 
      let nv = Pre_env.lookup_named_val id env in
      begin
	match !nv with
	| VKvalue (v,_) -> v
	| VKnone -> 
	    let (_, b, _) = Sign.lookup_named id env.env_named_context in
	    let v,d = 
	      match b with
		| None -> (val_of_named id, Idset.empty)
		| Some c -> (val_of_constr env c, Environ.global_vars_set (Environ.env_of_pre_env env) c)
	    in
	      nv := VKvalue (v,d); v
      end
  | FVrel i ->
      let rv = Pre_env.lookup_rel_val i env in
      begin
	match !rv with
	| VKvalue (v, _) -> v
	| VKnone -> 
	    let (_, b, _) = lookup_rel i env.env_rel_context in
	    let (v, d) =
	      match b with 
		| None -> (val_of_rel i, Idset.empty)
		| Some c -> let renv =  env_of_rel i env in
			      (val_of_constr renv c, Environ.global_vars_set (Environ.env_of_pre_env renv) c)
	    in
	      rv := VKvalue (v,d); v
      end
 
and eval_to_patch env (buff,pl,fv) = 
  let patch = function
    | Reloc_annot a, pos -> patch_int buff pos (slot_for_annot a)
    | Reloc_const sc, pos -> patch_int buff pos (slot_for_str_cst sc)
    | Reloc_getglobal kn, pos -> 
	patch_int buff pos (slot_for_getglobal env kn)
  in 
  List.iter patch pl;
  let vm_env = Array.map (slot_for_fv env) fv in 
  let tc = tcode_of_code buff (length buff) in
  eval_tcode tc vm_env

and val_of_constr env c = 
  let (_,fun_code,_ as ccfv) = 
    try compile env c 
    with e -> print_string "can not compile \n";Format.print_flush();raise e in
  eval_to_patch env (to_memory ccfv)
 
let set_transparent_const kn =
  cst_opaque := Cpred.remove kn !cst_opaque;
  List.iter (fun n -> (global_boxed()).(n) <- false) 
    (Hashtbl.find_all boxed_tbl kn)

let set_opaque_const kn =
  cst_opaque := Cpred.add kn !cst_opaque;
  List.iter (fun n -> (global_boxed()).(n) <- true) 
    (Hashtbl.find_all boxed_tbl kn)


