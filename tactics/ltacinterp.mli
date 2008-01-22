(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(*arnaud: commenter le module en général aussi *)


(* arnaud: peut-être faut-il considérer l'idée d'avoir un type des refine-step
   soit un constr et un environement d'evar, qui pourrait se passer en argument de tactique, plutôt que bêtement raw-constr... *)

open Term


(* arnaud: à commenter un peu plus dans le sens de ce que c'est vraiment. A savoir les valeurs qui peuvent être dans des variables de tactique *)
(* Values for interpretation *)
type value =
  | VTactic of Util.loc * Subproof.tactic  (* For mixed ML/Ltac tactics (e.g. Tauto) *)
  | VFun of (Names.identifier * value) list * Names.identifier option list * Tacexpr.glob_tactic_expr
  | VVoid
  | VInteger of int
  | VIntroPattern of Genarg.intro_pattern_expr
  | VConstr of constr (* arnaud: constr ou rawconstr ? *)
  | VConstr_context of constr (* arnaud: contrs ou rawconstr ? *)
  | VList of value list
  | VRec of value ref



(*** ***)
(* arnaud: partie pas certaine  *)

(* arnaud: dans un premier temps supposons que tout s'évalue en une tactique. *)

(* arnaud: plutôt "contexte de généralisation je suppose" *)
(* Interpretation of extra generic arguments *)
type glob_sign = { 
  ltacvars : Names.identifier list * Names.identifier list;
     (* ltac variables and the subset of vars introduced by Intro/Let/... *)
  ltacrecvars : (Names.identifier * Nametab.ltac_constant) list;
     (* ltac recursive names *)
  gsigma : Evd.evar_map;
     (* arnaud: environnement pour typer les evars, pourquoi pas un defs ? *)
  genv : Environ.env }
     (* environement pour typer le reste, normal *)

val intern_tactic : 
  glob_sign -> Tacexpr.raw_tactic_expr -> Tacexpr.glob_tactic_expr

val eval_tactic : Tacexpr.glob_tactic_expr -> Subproof.tactic


(* arnaud: fonction très temporaire *)
val hide_interp : 'a Proof.proof -> Tacexpr.raw_tactic_expr -> 'a option -> Subproof.tactic
