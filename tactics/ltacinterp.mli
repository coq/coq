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
  | VTactic of Util.loc * unit Proofview.tactic  (* For mixed ML/Ltac tactics (e.g. Tauto) *)
  | VFun of (Names.identifier * value) list * Names.identifier option list * Tacexpr.glob_tactic_expr
  | VVoid
  | VInteger of int
  | VIntroPattern of Genarg.intro_pattern_expr
  | VConstr of constr (* arnaud: constr ou rawconstr ? *)
  | VConstr_context of constr (* arnaud: contrs ou rawconstr ? *)
  | VList of value list
  | VRec of value ref




(* Tactic extensions *)
val add_tactic :
  string -> ((Genarg.argument_type *
	      Tacexpr.typed_generic_argument Goal.sensitive) list 
	     -> unit Proofview.tactic) -> unit
val out_gen_expr : ('a,'l) Genarg.abstract_argument_type 
                      -> 'l Genarg.generic_argument Goal.sensitive
                      -> 'a Goal.sensitive

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

(* Signature for interpretation: val_interp and interpretation functions *)
type interp_sign =
    { lfun : (Names.identifier * value) list;
      avoid_ids : Names.identifier list; (* ids inherited from the call context
				      (needed to get fresh ids) *)
      debug : Tactic_debug.debug_info;
      last_loc : Util.loc }


(* To embed several objects in Coqast.t *)
val tacticIn : (interp_sign -> Tacexpr.raw_tactic_expr) -> Tacexpr.raw_tactic_expr
val tacticOut : Tacexpr.raw_tactic_expr -> (interp_sign -> Tacexpr.raw_tactic_expr)
val valueIn : value -> Tacexpr.raw_tactic_arg
val valueOut: Tacexpr.raw_tactic_arg -> value
val constrIn : constr -> Topconstr.constr_expr
val constrOut : Topconstr.constr_expr -> constr


val intern_tactic : 
  glob_sign -> Tacexpr.raw_tactic_expr -> Tacexpr.glob_tactic_expr

val eval_tactic : Tacexpr.glob_tactic_expr -> unit Proofview.tactic

val interp : Tacexpr.raw_tactic_expr -> unit Proofview.tactic


(* arnaud: fonction très temporaire *)
val hide_interp : Proof.proof -> Tacexpr.raw_tactic_expr -> 'a option -> unit Proofview.tactic
