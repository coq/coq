
(* $Id$ *)

(*i*)
open Util
open Stamps
open Names
open Term
open Sign
open Evd
(*i*)

(* This module declares the structure of proof trees, global and
   readable constraints, and a few utilities on these types *)

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

(* [ref] = [None] if the goal has still to be proved, 
   and [Some (r,l)] if the rule [r] was applied to the goal
   and gave [l] as subproofs to be completed. 

   [subproof] = [(Some p)] if [ref = (Some(Tactic t,l))]; 
   [p] is then the proof that the goal can be proven if the goals
   in [l] are solved *)

type proof_tree = {
  status : pf_status;
  goal : goal;
  ref : (rule * proof_tree list) option; 
  subproof : proof_tree option }

and goal = {
  goal_ev : evar_info;
  goal_ctxtty : ctxtty }

and rule =
  | Prim of prim_rule
  | Tactic of tactic_expression
  | Context of ctxtty
  | Local_constraints of local_constraints

and ctxtty = {
  pgm    : constr option;
  mimick : proof_tree option;
  lc     : local_constraints } 

type evar_declarations = goal Intmap.t


val mk_goal : ctxtty -> typed_type signature -> constr -> goal

val mt_ctxt    : local_constraints -> ctxtty
val get_ctxt   : goal  -> ctxtty
val get_pgm    : goal -> constr option
val set_pgm    : constr option -> ctxtty -> ctxtty
val get_mimick : goal ->  proof_tree option
val set_mimick : proof_tree option ->  ctxtty -> ctxtty
val get_lc     : goal -> local_constraints

val rule_of_proof     : proof_tree -> rule
val ref_of_proof      : proof_tree -> (rule * proof_tree list)
val children_of_proof : proof_tree -> proof_tree list
val goal_of_proof     : proof_tree -> goal
val subproof_of_proof : proof_tree -> proof_tree
val status_of_proof   : proof_tree -> pf_status
val is_complete_proof : proof_tree -> bool
val is_leaf_proof     : proof_tree -> bool
val is_tactic_proof   : proof_tree -> bool


(* A global constraint is a mappings of existential variables
   with some extra information for the program and mimick tactics. *)

type global_constraints = evar_declarations timestamped

(* A readable constraint is a global constraint plus a focus set
   of existential variables and a signature. *)

type evar_recordty = {
  focus : local_constraints;
  sign  : typed_type signature;
  decls : evar_declarations }

and readable_constraints = evar_recordty timestamped

val rc_of_gc  : global_constraints -> goal -> readable_constraints
val rc_add    : readable_constraints -> int * goal -> readable_constraints
val get_hyps  : readable_constraints -> typed_type signature
val get_focus : readable_constraints -> local_constraints
val get_decls : readable_constraints -> evar_declarations
val get_gc    : readable_constraints -> global_constraints
val remap     : readable_constraints -> int * goal -> readable_constraints
val ctxt_access : readable_constraints -> int -> bool
