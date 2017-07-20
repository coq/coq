(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Warning, this file should respect the dependency order established
   in Coq. To see such order issue the comand:

   ```
   bash -c 'for i in kernel intf library engine pretyping interp proofs parsing printing tactics vernac stm toplevel; do echo -e "\n## $i files" && cat ${i}/${i}.mllib; done && echo -e "\n## highparsing files" && cat parsing/highparsing.mllib' > API/link
   ```

   Note however that files in intf/ are located manually now as their
   conceptual linking order in the Coq codebase is incorrect (but it
   works due to these files being implementation-free.

   See below in the file for their concrete position.
*)

(************************************************************************)
(* Modules from printing/                                               *)
(************************************************************************)

module Genprint :
sig
  type 'a printer = 'a -> Pp.std_ppcmds
  val generic_top_print : Genarg.tlevel Genarg.generic_argument printer
  val register_print0 : ('raw, 'glb, 'top) Genarg.genarg_type ->
                        'raw printer -> 'glb printer -> 'top printer -> unit
end

module Pputils :
sig
  val pr_with_occurrences : ('a -> Pp.std_ppcmds) -> (string -> Pp.std_ppcmds) -> 'a Locus.with_occurrences -> Pp.std_ppcmds
  val pr_red_expr :
    ('a -> Pp.std_ppcmds) * ('a -> Pp.std_ppcmds) * ('b -> Pp.std_ppcmds) * ('c -> Pp.std_ppcmds) ->
    (string -> Pp.std_ppcmds) ->
    ('a,'b,'c) Genredexpr.red_expr_gen -> Pp.std_ppcmds
  val pr_raw_generic : Environ.env -> Genarg.rlevel Genarg.generic_argument -> Pp.std_ppcmds
  val pr_glb_generic : Environ.env -> Genarg.glevel Genarg.generic_argument -> Pp.std_ppcmds
  val pr_or_var : ('a -> Pp.std_ppcmds) -> 'a Misctypes.or_var -> Pp.std_ppcmds
  val pr_or_by_notation : ('a -> Pp.std_ppcmds) -> 'a Misctypes.or_by_notation -> Pp.std_ppcmds
end

module Ppconstr :
sig
  val pr_name : Names.Name.t -> Pp.std_ppcmds
  [@@ocaml.deprecated "alias of API.Names.Name.print"]

  val pr_id : Names.Id.t -> Pp.std_ppcmds
  val pr_or_var : ('a -> Pp.std_ppcmds) -> 'a Misctypes.or_var -> Pp.std_ppcmds
  val pr_with_comments : ?loc:Loc.t -> Pp.std_ppcmds -> Pp.std_ppcmds
  val pr_lident : Names.Id.t Loc.located -> Pp.std_ppcmds
  val pr_lname : Names.Name.t Loc.located -> Pp.std_ppcmds
  val prec_less : int -> int * Ppextend.parenRelation -> bool
  val pr_constr_expr : Constrexpr.constr_expr -> Pp.std_ppcmds
  val pr_lconstr_expr : Constrexpr.constr_expr -> Pp.std_ppcmds
  val pr_constr_pattern_expr : Constrexpr.constr_pattern_expr -> Pp.std_ppcmds
  val pr_lconstr_pattern_expr : Constrexpr.constr_pattern_expr -> Pp.std_ppcmds
  val pr_binders : Constrexpr.local_binder_expr list -> Pp.std_ppcmds
  val pr_glob_sort : Misctypes.glob_sort -> Pp.std_ppcmds
end

module Printer :
sig
  val pr_named_context : Environ.env -> Evd.evar_map -> Context.Named.t -> Pp.std_ppcmds
  val pr_rel_context : Environ.env -> Evd.evar_map -> Context.Rel.t -> Pp.std_ppcmds
  val pr_goal : Goal.goal Evd.sigma -> Pp.std_ppcmds

  val pr_constr_env : Environ.env -> Evd.evar_map -> Constr.t -> Pp.std_ppcmds
  val pr_lconstr_env : Environ.env -> Evd.evar_map -> Constr.t -> Pp.std_ppcmds

  val pr_constr : Constr.t -> Pp.std_ppcmds

  val pr_lconstr : Constr.t -> Pp.std_ppcmds

  val pr_econstr : EConstr.constr -> Pp.std_ppcmds
  val pr_glob_constr : Glob_term.glob_constr -> Pp.std_ppcmds
  val pr_constr_pattern : Pattern.constr_pattern -> Pp.std_ppcmds
  val pr_glob_constr_env : Environ.env -> Glob_term.glob_constr -> Pp.std_ppcmds
  val pr_lglob_constr_env : Environ.env -> Glob_term.glob_constr -> Pp.std_ppcmds
  val pr_econstr_env : Environ.env -> Evd.evar_map -> EConstr.constr -> Pp.std_ppcmds
  val pr_constr_pattern_env : Environ.env -> Evd.evar_map -> Pattern.constr_pattern -> Pp.std_ppcmds
  val pr_lconstr_pattern_env : Environ.env -> Evd.evar_map -> Pattern.constr_pattern -> Pp.std_ppcmds
  val pr_closed_glob : Glob_term.closed_glob_constr -> Pp.std_ppcmds
  val pr_lglob_constr : Glob_term.glob_constr -> Pp.std_ppcmds
  val pr_leconstr_env : Environ.env -> Evd.evar_map -> EConstr.constr -> Pp.std_ppcmds
  val pr_leconstr : EConstr.constr -> Pp.std_ppcmds
  val pr_global : Globnames.global_reference -> Pp.std_ppcmds
  val pr_lconstr_under_binders : Pattern.constr_under_binders -> Pp.std_ppcmds
  val pr_lconstr_under_binders_env : Environ.env -> Evd.evar_map -> Pattern.constr_under_binders -> Pp.std_ppcmds

  val pr_constr_under_binders_env : Environ.env -> Evd.evar_map -> Pattern.constr_under_binders -> Pp.std_ppcmds
  val pr_closed_glob_env : Environ.env -> Evd.evar_map -> Glob_term.closed_glob_constr -> Pp.std_ppcmds
  val pr_rel_context_of : Environ.env -> Evd.evar_map -> Pp.std_ppcmds
  val pr_named_context_of : Environ.env -> Evd.evar_map -> Pp.std_ppcmds
  val pr_ltype : Term.types -> Pp.std_ppcmds
  val pr_ljudge : EConstr.unsafe_judgment -> Pp.std_ppcmds * Pp.std_ppcmds
  val pr_idpred : Names.Id.Pred.t -> Pp.std_ppcmds
  val pr_cpred : Names.Cpred.t -> Pp.std_ppcmds
  val pr_transparent_state : Names.transparent_state -> Pp.std_ppcmds
end

(************************************************************************)
(* End of modules from printing/                                        *)
(************************************************************************)
