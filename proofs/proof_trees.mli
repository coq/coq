
(* $Id$ *)

(*i*)
open Names
open Term
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

type local_constraints = Spset.t

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

and evar_declarations = ctxtty evar_map
