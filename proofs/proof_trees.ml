
(* $Id$ *)

open Util
open Names
open Term
open Sign
open Evd
open Stamps

type bindOcc = 
  | Dep of identifier
  | NoDep of int
  | Com

type 'a substitution = (bindOcc * 'a) list

type tactic_arg =
  | Command       of Coqast.t
  | Constr        of constr
  | Identifier    of identifier
  | Integer       of int
  | Clause        of identifier list
  | Bindings      of Coqast.t substitution
  | Cbindings     of constr   substitution 
  | Quoted_string of string
  | Tacexp        of Coqast.t
  | Redexp        of string * Coqast.t list
  | Fixexp        of identifier * int * Coqast.t
  | Cofixexp      of identifier * Coqast.t
  | Letpatterns   of int list option * (identifier * int list) list
  | Intropattern  of intro_pattern

and intro_pattern =
  | IdPat   of identifier
  | DisjPat of intro_pattern list
  | ConjPat of intro_pattern list
  | ListPat of intro_pattern list  

and tactic_expression = string * tactic_arg list


type pf_status = Complete_proof | Incomplete_proof

type prim_rule_name = 
  | Intro
  | Intro_after
  | Intro_replacing
  | Fix
  | Cofix
  | Refine 
  | Convert_concl
  | Convert_hyp
  | Thin
  | Move of bool

type prim_rule = {
  name : prim_rule_name;
  hypspecs : identifier list;
  newids : identifier list;
  params : Coqast.t list;
  terms : constr list }

type local_constraints = Intset.t

type proof_tree = {
  status : pf_status;
  goal : goal;
  ref : (rule * proof_tree list) option; 
  subproof : proof_tree option }

and goal = ctxtty evar_info

and rule =
  | Prim of prim_rule
  | Tactic of tactic_expression
  | Context of ctxtty
  | Local_constraints of local_constraints

and ctxtty = {
  pgm    : constr option;
  mimick : proof_tree option;
  lc     : local_constraints } 

type evar_declarations = ctxtty evar_map


let is_bind = function
  | Bindings _ -> true
  | _ -> false

let lc_toList lc = Intset.elements lc

(* Functions on goals *)

let mk_goal ctxt sign cl = 
  { evar_hyps = sign; evar_concl = cl; evar_body = Evar_empty;
    evar_info = ctxt }

(* Functions on the information associated with existential variables  *)

let mt_ctxt lc = { pgm = None; mimick = None; lc = lc }

let get_ctxt gl = gl.evar_info

let get_pgm gl = gl.evar_info.pgm

let set_pgm pgm ctxt = { ctxt with pgm = pgm }

let get_mimick gl = gl.evar_info.mimick

let set_mimick mimick ctxt = { mimick = mimick; pgm = ctxt.pgm; lc = ctxt.lc }

let get_lc gl = gl.evar_info.lc

(* Functions on proof trees *)

let ref_of_proof pf =
  match pf.ref with
    | None -> failwith "rule_of_proof"
    | Some r -> r

let rule_of_proof pf =
  let (r,_) = ref_of_proof pf in r

let children_of_proof pf = 
  let (_,cl) = ref_of_proof pf in cl
				    
let goal_of_proof pf = pf.goal

let subproof_of_proof pf =
  match pf.subproof with
    | None -> failwith "subproof_of_proof"
    | Some pf -> pf

let status_of_proof pf = pf.status

let is_complete_proof pf = pf.status = Complete_proof

let is_leaf_proof pf =
  match pf.ref with
    | None -> true
    | Some _ -> false

let is_tactic_proof pf =
  match pf.subproof with
    | Some _ -> true
    | None -> false


(*******************************************************************)
(*            Constraints for existential variables                *)
(*******************************************************************)

(* A local constraint is just a set of section_paths *)

(* recall : type local_constraints = Intset.t *)

(* A global constraint is a mappings of existential variables
   with some extra information for the program and mimick
   tactics. *)

type global_constraints  = evar_declarations timestamped

(* A readable constraint is a global constraint plus a focus set
   of existential variables and a signature. *)

type evar_recordty = {
  focus : local_constraints;
  sign  : typed_type signature;
  decls : evar_declarations }

and readable_constraints = evar_recordty timestamped

(* Functions on readable constraints *)
			     
let mt_evcty lc gc = 
  ts_mk { focus = lc; sign = nil_sign; decls = gc }

let evc_of_evds evds gl = 
  ts_mk { focus = (get_lc gl); sign = gl.evar_hyps ; decls = evds }

let rc_of_gc gc gl = evc_of_evds (ts_it gc) gl
		       
let rc_add evc (k,v) = 
  ts_mod
    (fun evc -> { focus = (Intset.add k evc.focus);
                  sign  = evc.sign;
                  decls = Evd.add evc.decls k v })
    evc

let get_hyps  evc = (ts_it evc).sign
let get_focus evc = (ts_it evc).focus
let get_decls evc = (ts_it evc).decls
let get_gc    evc = (ts_mk (ts_it evc).decls)

let remap evc (k,v) = 
  ts_mod
    (fun evc -> { focus = evc.focus;
                  sign  = evc.sign;
                  decls = Evd.add evc.decls k v })
    evc

let lc_exists f lc = Intset.fold (fun e b -> (f e) or b) lc false

(* [mentions sigma sp loc] is true exactly when [loc] is defined, and [sp] is
 * on [loc]'s access list, or an evar on [loc]'s access list mentions [sp]. *)

let rec mentions sigma sp loc =
  let loc_evd = Evd.map (ts_it sigma).decls loc in 
  match loc_evd.evar_body with 
    | Evar_defined _ -> (Intset.mem sp (get_lc loc_evd) 
			 or lc_exists (mentions sigma sp) (get_lc loc_evd))
    | _ -> false

(* ACCESSIBLE SIGMA SP LOC is true exactly when SP is on LOC's access list,
 * or there exists a LOC' on LOC's access list such that
 * MENTIONS SIGMA SP LOC' is true. *)

let rec accessible sigma sp loc =
  let loc_evd = Evd.map (ts_it sigma).decls loc in 
  lc_exists (fun loc' -> sp = loc' or mentions sigma sp loc') (get_lc loc_evd)


(* [ctxt_access sigma sp] is true when SIGMA is accessing a current
 * accessibility list ACCL, and SP is either on ACCL, or is mentioned
 * in the body of one of the ACCL. *)

let ctxt_access sigma sp =
  lc_exists (fun sp' -> sp' = sp or mentions sigma sp sp') (ts_it sigma).focus

