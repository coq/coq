
(*i $Id$ i*)

(*i*)
open Environ
open Evd
open Names
open Stamps
open Term
open Util
(*i*)

(* This module defines the structure of proof tree and the tactic type. So, it
   is used by [Proof_tree] and [Refiner] *)

type bindOcc = 
  | Dep of identifier
  | NoDep of int
  | Com

type 'a substitution = (bindOcc * 'a) list

type pf_status =
  | Complete_proof
  | Incomplete_proof

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

type ctxtty = {
  pgm    : constr option;
  lc     : local_constraints } 

type enamed_declarations = ctxtty evar_map

(* A global constraint is a mappings of existential variables
   with some extra information for the program tactic *)
type global_constraints  = enamed_declarations timestamped

(* The type [goal sigma] is the type of subgoal. It has the following form
\begin{verbatim}
   it    = { evar_concl = [the conclusion of the subgoal]
             evar_hyps = [the hypotheses of the subgoal]
             evar_body = Evar_Empty;
             evar_info = { pgm    : [The Realizer pgm if any]
                           lc     : [Set of evar num occurring in subgoal] }}
   sigma = { stamp = [an int characterizing the ed field, for quick compare]
             ed : [A set of existential variables depending in the subgoal]
               number of first evar,
               it = { evar_concl = [the type of first evar]
                      evar_hyps = [the context of the evar]
                      evar_body = [the body of the Evar if any]
                      evar_info = { pgm    : [Useless ??]
                                    lc     : [Set of evars occurring
                                              in the type of evar] } };
               ...
               number of last evar, 
               it = { evar_concl = [the type of evar]
                      evar_hyps = [the context of the evar]
                      evar_body = [the body of the Evar if any]
                      evar_info = { pgm    : [Useless ??]
                                    lc     : [Set of evars occurring
                                              in the type of evar] } } }
   }
\end{verbatim}
*)

(* The type constructor ['a sigma] adds an evar map to an object of
  type ['a] (see below the form of a [goal sigma] *)
type 'a sigma = { 
  it : 'a ; 
  sigma : global_constraints }

(*s Proof trees. 
  [ref] = [None] if the goal has still to be proved, 
  and [Some (r,l)] if the rule [r] was applied to the goal
  and gave [l] as subproofs to be completed. 
  [subproof] = [(Some p)] if [ref = (Some(Tactic t,l))]; 
  [p] is then the proof that the goal can be proven if the goals
  in [l] are solved. *)
type proof_tree = {
  status : pf_status;
  goal : goal;
  ref : (rule * proof_tree list) option; 
  subproof : proof_tree option }

and rule =
  | Prim of prim_rule
  | Tactic of tactic_expression
  | Context of ctxtty
  | Local_constraints of local_constraints

and goal = ctxtty evar_info

and tactic = goal sigma -> (goal list sigma * validation)

and validation = (proof_tree list -> proof_tree)

and tactic_arg =
  | Command        of Coqast.t
  | Constr         of constr
  | OpenConstr     of ((int * constr) list * constr) (* constr with holes *)
  | Constr_context of constr
  | Identifier     of identifier
  | Qualid         of qualid
  | Integer        of int
  | Clause         of identifier list
  | Bindings       of Coqast.t substitution
  | Cbindings      of constr   substitution 
  | Quoted_string  of string
  | Tacexp         of Coqast.t
  | Tac            of tactic * Coqast.t
  | Redexp         of Tacred.red_expr
  | Fixexp         of identifier * int * Coqast.t
  | Cofixexp       of identifier * Coqast.t
  | Letpatterns    of (int list option * (identifier * int list) list)
  | Intropattern   of intro_pattern

and intro_pattern =
  | IdPat   of identifier
  | DisjPat of intro_pattern list
  | ConjPat of intro_pattern list
  | ListPat of intro_pattern list  

and tactic_expression = string * tactic_arg list
