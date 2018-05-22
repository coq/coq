(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Printers for the ocaml toplevel. *)

val pp : Pp.t -> unit
val pP : Pp.t -> unit (* with surrounding box *)

val ppfuture : 'a Future.computation -> unit

val ppid : Names.Id.t -> unit
val pplab : Names.Label.t -> unit
val ppmbid : Names.MBId.t -> unit
val ppdir : Names.DirPath.t -> unit
val ppmp : Names.ModPath.t -> unit
val ppcon : Names.Constant.t -> unit
val ppproj : Names.Projection.t -> unit
val ppkn : Names.KerName.t -> unit
val ppmind : Names.MutInd.t -> unit
val ppind : Names.inductive -> unit

val ppsp : Libnames.full_path -> unit
val ppqualid : Libnames.qualid -> unit

val ppclindex : Classops.cl_index -> unit

val ppscheme : 'a Ind_tables.scheme_kind -> unit

val prrecarg : Declarations.recarg -> Pp.t
val ppwf_paths : Declarations.recarg Rtree.t -> unit

val pr_evar : Evar.t -> Pp.t
val ppevar : Evar.t -> unit

(* Multiple printers for Constr.t *)
val ppconstr : Constr.t -> unit (* by Termops printer *)
val ppconstr_univ : Constr.t -> unit

(* Extern as type *)
val pptype : Constr.types -> unit

val ppsconstr : Constr.constr Mod_subst.substituted -> unit
val ppeconstr : EConstr.constr -> unit (* Termops printer *)
val ppconstr_expr : Constrexpr.constr_expr -> unit
val ppglob_constr : 'a Glob_term.glob_constr_g -> unit
val pppattern : Pattern.constr_pattern -> unit
val ppfconstr : CClosure.fconstr -> unit

val ppbigint : Bigint.bigint -> unit

val ppintset : Int.Set.t -> unit
val ppidset : Names.Id.Set.t -> unit

val pridmap : (Names.Id.Map.key -> 'a -> Pp.t) -> 'a Names.Id.Map.t -> Pp.t
val ppidmap : (Names.Id.Map.key -> 'a -> Pp.t) -> 'a Names.Id.Map.t -> unit

val pridmapgen : 'a Names.Id.Map.t -> Pp.t
val ppidmapgen : 'a Names.Id.Map.t -> unit

val prididmap : Names.Id.t Names.Id.Map.t -> Pp.t
val ppididmap : Names.Id.t Names.Id.Map.t -> unit

val prconstrunderbindersidmap :
  (Names.Id.t list * EConstr.constr) Names.Id.Map.t -> Pp.t
val ppconstrunderbindersidmap :
  (Names.Id.t list * EConstr.constr) Names.Id.Map.t -> unit

val ppevarsubst :
  (Constr.t * Constr.t option * Names.Id.Map.key) list Names.Id.Map.t -> unit

val ppunbound_ltac_var_map :
  'a Genarg.generic_argument Names.Id.Map.t -> unit

val pr_closure : Ltac_pretype.closure -> Pp.t
val pr_closed_glob_constr_idmap :
  Ltac_pretype.closed_glob_constr Names.Id.Map.t -> Pp.t
val pr_closed_glob_constr : Ltac_pretype.closed_glob_constr -> Pp.t
val ppclosure : Ltac_pretype.closure -> unit
val ppclosedglobconstr : Ltac_pretype.closed_glob_constr -> unit
val ppclosedglobconstridmap :
  Ltac_pretype.closed_glob_constr Names.Id.Map.t -> unit

val ppglobal : Names.GlobRef.t -> unit

val ppconst :
  Names.KerName.t * (Constr.constr, 'a) Environ.punsafe_judgment -> unit
val ppvar : Names.Id.t * Constr.constr -> unit

val genppj : ('a -> Pp.t * Pp.t) -> 'a -> Pp.t
val ppj : EConstr.unsafe_judgment -> unit

val ppsubst : Mod_subst.substitution -> unit
val ppdelta : Mod_subst.delta_resolver -> unit

val pp_idpred : Names.Id.Pred.t -> unit
val pp_cpred : Names.Cpred.t -> unit
val pp_transparent_state : Names.transparent_state -> unit

val pp_stack_t : Constr.t Reductionops.Stack.t -> unit
val pp_cst_stack_t : Reductionops.Cst_stack.t -> unit
val pp_state_t : Reductionops.state -> unit

val ppmetas : Evd.Metaset.t -> unit
val ppevm : Evd.evar_map -> unit
val ppevmall : Evd.evar_map -> unit

val pr_existentialset : Evar.Set.t -> Pp.t
val ppexistentialset : Evar.Set.t -> unit

val ppexistentialfilter : Evd.Filter.t -> unit

val ppclenv : Clenv.clausenv -> unit

val ppgoalgoal : Goal.goal -> unit

val ppgoal : Proof_type.goal Evd.sigma -> unit
(* also print evar map *)
val ppgoalsigma : Proof_type.goal Evd.sigma -> unit

val pphintdb : Hints.Hint_db.t -> unit
val ppproofview : Proofview.proofview -> unit
val ppopenconstr : Evd.open_constr -> unit

val pproof : Proof.t -> unit

(* Universes *)
val ppuni : Univ.Universe.t -> unit
val ppuni_level : Univ.Level.t -> unit (* raw *)
val prlev : Univ.Level.t -> Pp.t (* with global names (does this work?) *)
val ppuniverse_set : Univ.LSet.t -> unit
val ppuniverse_instance : Univ.Instance.t -> unit
val ppuniverse_context : Univ.UContext.t -> unit
val ppuniverse_context_set : Univ.ContextSet.t -> unit
val ppuniverse_subst : Univ.universe_subst -> unit
val ppuniverse_opt_subst : UnivSubst.universe_opt_subst -> unit
val ppuniverse_level_subst : Univ.universe_level_subst -> unit
val ppevar_universe_context : UState.t -> unit
val ppconstraints : Univ.Constraint.t -> unit
val ppuniverseconstraints : UnivProblem.Set.t -> unit
val ppuniverse_context_future : Univ.UContext.t Future.computation -> unit
val ppcumulativity_info : Univ.CumulativityInfo.t -> unit
val ppabstract_cumulativity_info : Univ.ACumulativityInfo.t -> unit
val ppuniverses : UGraph.t -> unit

val ppnamedcontextval : Environ.named_context_val -> unit
val ppenv : Environ.env -> unit
val ppenvwithcst : Environ.env -> unit

val pptac : Ltac_plugin.Tacexpr.glob_tactic_expr -> unit

val ppobj : Libobject.obj -> unit

(* Some super raw printers *)
val cast_kind_display : Constr.cast_kind -> string
val constr_display : Constr.constr -> unit
val print_pure_constr : Constr.types -> unit

val pploc : Loc.t -> unit

val pp_argument_type : Genarg.argument_type -> unit
val pp_generic_argument : 'a Genarg.generic_argument -> unit

val prgenarginfo : Geninterp.Val.t -> Pp.t
val ppgenarginfo : Geninterp.Val.t -> unit

val ppgenargargt : ('a, 'b, 'c) Genarg.ArgT.tag -> unit

val ppist : Geninterp.interp_sign -> unit
