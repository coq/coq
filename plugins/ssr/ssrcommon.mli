(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Tacmach
open Names
open Environ
open Evd
open Constrexpr
open Ssrast

open Ltac_plugin
open Genarg

open Ssrmatching_plugin

val allocc : ssrocc

(******************************** hyps ************************************)

val hyp_id : ssrhyp -> Id.t
val hyps_ids : ssrhyps -> Id.t list
val check_hyp_exists : ('a, 'b) Context.Named.pt -> ssrhyp -> unit
val test_hypname_exists : ('a, 'b) Context.Named.pt -> Id.t -> bool
val check_hyps_uniq : Id.t list -> ssrhyps -> unit
val not_section_id : Id.t -> bool
val hyp_err : ?loc:Loc.t -> string -> Id.t -> 'a
val hoik : (ssrhyp -> 'a) -> ssrhyp_or_id -> 'a
val hoi_id : ssrhyp_or_id -> Id.t

(******************************* hints ***********************************)

val mk_hint : 'a -> 'a ssrhint 
val mk_orhint : 'a -> bool * 'a
val nullhint : bool * 'a list
val nohint : 'a ssrhint

(******************************** misc ************************************)

val errorstrm : Pp.t -> 'a
val anomaly : string -> 'a

val array_app_tl : 'a array -> 'a list -> 'a list
val array_list_of_tl : 'a array -> 'a list
val array_fold_right_from : int -> ('a -> 'b -> 'b) -> 'a array -> 'b -> 'b

val option_assert_get : 'a option -> Pp.t -> 'a

(**************************** lifted tactics ******************************)

(* tactics with extra data attached to each goals, e.g. the list of
 * temporary variables to be cleared *)
type 'a tac_a = (goal * 'a) sigma -> (goal * 'a) list sigma

(* Thread around names to be cleared or generalized back, and the speed *)
type tac_ctx = {
  tmp_ids : (Id.t * Name.t ref) list;
  wild_ids : Id.t list;
  (* List of variables to be cleared at the end of the sentence *)
  delayed_clears : Id.t list;
}

val new_ctx : unit -> tac_ctx (* REMOVE *)
val pull_ctxs : ('a * tac_ctx) list  sigma -> 'a list sigma * tac_ctx list (* REMOVE *)

val with_fresh_ctx : tac_ctx tac_a -> tactic

val pull_ctx : ('a * tac_ctx) sigma -> 'a sigma * tac_ctx
val push_ctx : tac_ctx -> 'a sigma -> ('a * tac_ctx) sigma
val push_ctxs : tac_ctx -> 'a list sigma -> ('a * tac_ctx) list sigma
val tac_ctx : tactic -> tac_ctx tac_a
val with_ctx :
  (tac_ctx -> 'b * tac_ctx) -> ('a * tac_ctx) sigma -> 'b * ('a * tac_ctx) sigma
val without_ctx : ('a sigma -> 'b) -> ('a * tac_ctx) sigma -> 'b

(* Standard tacticals lifted to the tac_a type *)
val tclTHENLIST_a : tac_ctx tac_a list -> tac_ctx tac_a
val tclTHEN_i_max :
  tac_ctx tac_a -> (int -> int -> tac_ctx tac_a) -> tac_ctx tac_a
val tclTHEN_a : tac_ctx tac_a -> tac_ctx tac_a -> tac_ctx tac_a
val tclTHENS_a : tac_ctx tac_a -> tac_ctx tac_a list -> tac_ctx tac_a

val tac_on_all :
  (goal * tac_ctx) list sigma -> tac_ctx tac_a -> (goal * tac_ctx) list sigma
(************************ ssr tactic arguments ******************************)


(*********************** Misc helpers *****************************)
val mkRHole : Glob_term.glob_constr
val mkRHoles : int -> Glob_term.glob_constr list
val isRHoles : Glob_term.glob_constr list -> bool
val mkRApp : Glob_term.glob_constr -> Glob_term.glob_constr list -> Glob_term.glob_constr
val mkRVar : Id.t -> Glob_term.glob_constr
val mkRltacVar : Id.t -> Glob_term.glob_constr
val mkRCast : Glob_term.glob_constr ->  Glob_term.glob_constr ->  Glob_term.glob_constr
val mkRType : Glob_term.glob_constr
val mkRProp : Glob_term.glob_constr
val mkRArrow : Glob_term.glob_constr ->  Glob_term.glob_constr ->  Glob_term.glob_constr
val mkRConstruct : Names.constructor -> Glob_term.glob_constr
val mkRInd : Names.inductive -> Glob_term.glob_constr
val mkRLambda : Name.t -> Glob_term.glob_constr ->  Glob_term.glob_constr ->  Glob_term.glob_constr
val mkRnat : int -> Glob_term.glob_constr


val mkCHole : Loc.t option -> constr_expr
val mkCHoles : ?loc:Loc.t -> int -> constr_expr list
val mkCVar : ?loc:Loc.t -> Id.t -> constr_expr
val mkCCast : ?loc:Loc.t -> constr_expr ->  constr_expr ->  constr_expr
val mkCType : Loc.t option -> constr_expr
val mkCProp : Loc.t option -> constr_expr
val mkCArrow : ?loc:Loc.t -> constr_expr ->  constr_expr ->  constr_expr
val mkCLambda : ?loc:Loc.t -> Name.t -> constr_expr ->  constr_expr ->  constr_expr

val isCHoles : constr_expr list -> bool
val isCxHoles : (constr_expr * 'a option) list -> bool

val intern_term : 
  Tacinterp.interp_sign -> env ->
    ssrterm -> Glob_term.glob_constr

val pf_intern_term :
  Tacinterp.interp_sign -> Goal.goal Evd.sigma ->
    ssrterm -> Glob_term.glob_constr

val interp_term :
  Tacinterp.interp_sign -> Goal.goal Evd.sigma ->
    ssrterm -> evar_map * EConstr.t

val interp_wit :
  ('a, 'b, 'c) genarg_type -> ist -> goal sigma -> 'b -> evar_map * 'c

val interp_hyp : ist -> goal sigma -> ssrhyp -> evar_map * ssrhyp
val interp_hyps : ist -> goal sigma -> ssrhyps -> evar_map * ssrhyps

val interp_refine :
  Tacinterp.interp_sign -> Goal.goal Evd.sigma ->
    Glob_term.glob_constr -> evar_map * (evar_map * EConstr.constr)

val interp_open_constr :
  Tacinterp.interp_sign -> Goal.goal Evd.sigma ->
    Tacexpr.glob_constr_and_expr -> evar_map * (evar_map * EConstr.t)

val pf_e_type_of :
  Goal.goal Evd.sigma ->
  EConstr.constr -> Goal.goal Evd.sigma * EConstr.types

val splay_open_constr : 
           Goal.goal Evd.sigma ->
           evar_map * EConstr.t ->
           (Names.Name.t * EConstr.t) list * EConstr.t
val isAppInd : Environ.env -> Evd.evar_map -> EConstr.types -> bool

val mk_term : ssrtermkind -> constr_expr -> ssrterm
val mk_lterm : constr_expr -> ssrterm

val mk_ast_closure_term :
  [ `None | `Parens | `DoubleParens | `At ] ->
  Constrexpr.constr_expr -> ast_closure_term
val interp_ast_closure_term : Geninterp.interp_sign -> Proof_type.goal
Evd.sigma -> ast_closure_term -> Evd.evar_map * ast_closure_term
val subst_ast_closure_term : Mod_subst.substitution -> ast_closure_term -> ast_closure_term
val glob_ast_closure_term : Genintern.glob_sign -> ast_closure_term -> ast_closure_term
val ssrterm_of_ast_closure_term : ast_closure_term -> ssrterm

val ssrdgens_of_parsed_dgens :
  (ssrdocc * Ssrmatching.cpattern) list list * ssrclear -> ssrdgens

val is_internal_name : string -> bool
val add_internal_name : (string -> bool) -> unit
val mk_internal_id : string -> Id.t
val mk_tagged_id : string -> int -> Id.t
val mk_evar_name : int -> Name.t
val ssr_anon_hyp : string
val pf_type_id :  Goal.goal Evd.sigma -> EConstr.types -> Id.t

val pf_abs_evars : 
           Goal.goal Evd.sigma ->
           evar_map * EConstr.t ->
           int * EConstr.t * Evar.t list *
           UState.t
val pf_abs_evars2 : (* ssr2 *)
           Goal.goal Evd.sigma -> Evar.t list ->
           evar_map * EConstr.t ->
           int * EConstr.t * Evar.t list *
           UState.t
val pf_abs_cterm :
           Goal.goal Evd.sigma -> int -> EConstr.t -> EConstr.t

val pf_merge_uc :
           UState.t -> 'a Evd.sigma -> 'a Evd.sigma
val pf_merge_uc_of :
           evar_map -> 'a Evd.sigma -> 'a Evd.sigma
val constr_name : evar_map -> EConstr.t -> Name.t
val pf_type_of :
           Goal.goal Evd.sigma ->
           Constr.constr -> Goal.goal Evd.sigma * Constr.types
val pfe_type_of :
           Goal.goal Evd.sigma ->
           EConstr.t -> Goal.goal Evd.sigma * EConstr.types
val pf_abs_prod :
           Name.t ->
           Goal.goal Evd.sigma ->
           EConstr.t ->
           EConstr.t -> Goal.goal Evd.sigma * EConstr.types

val mkSsrRRef : string -> Glob_term.glob_constr * 'a option
val mkSsrRef : string -> GlobRef.t
val mkSsrConst : 
           string ->
           env -> evar_map -> evar_map * EConstr.t
val pf_mkSsrConst :
           string ->
           Goal.goal Evd.sigma ->
           EConstr.t * Goal.goal Evd.sigma
val new_wild_id : tac_ctx -> Names.Id.t * tac_ctx


val pf_fresh_global :
           GlobRef.t ->
           Goal.goal Evd.sigma ->
           Constr.constr * Goal.goal Evd.sigma

val is_discharged_id : Id.t -> bool
val mk_discharged_id : Id.t -> Id.t
val is_tagged : string -> string -> bool
val has_discharged_tag : string -> bool
val ssrqid : string -> Libnames.qualid 
val new_tmp_id :
  tac_ctx -> (Names.Id.t * Name.t ref) * tac_ctx
val mk_anon_id : string -> Id.t list -> Id.t
val pf_abs_evars_pirrel :
           Goal.goal Evd.sigma ->
           evar_map * Constr.constr -> int * Constr.constr
val nbargs_open_constr : Goal.goal Evd.sigma -> Evd.evar_map * EConstr.t -> int
val pf_nbargs : Goal.goal Evd.sigma -> EConstr.t -> int
val gen_tmp_ids : 
           ?ist:Geninterp.interp_sign ->
           (Goal.goal * tac_ctx) Evd.sigma ->
           (Goal.goal * tac_ctx) list Evd.sigma

val ssrevaltac :
  Tacinterp.interp_sign -> Tacinterp.Value.t -> unit Proofview.tactic

val convert_concl_no_check : EConstr.t -> unit Proofview.tactic
val convert_concl : EConstr.t -> unit Proofview.tactic

val red_safe :
  Reductionops.reduction_function ->
  env -> evar_map -> EConstr.t -> EConstr.t

val red_product_skip_id :
  env -> evar_map -> EConstr.t -> EConstr.t

val ssrautoprop_tac :
           (Evar.t Evd.sigma -> Evar.t list Evd.sigma) ref

val mkProt :
  EConstr.t ->
  EConstr.t ->
  Goal.goal Evd.sigma ->
  EConstr.t * Goal.goal Evd.sigma

val mkEtaApp : EConstr.t -> int -> int -> EConstr.t

val mkRefl :
  EConstr.t ->
  EConstr.t ->
  Goal.goal Evd.sigma -> EConstr.t * Goal.goal Evd.sigma

val discharge_hyp :
           Id.t * (Id.t * string) ->
           Goal.goal Evd.sigma -> Evar.t list Evd.sigma

val clear_wilds_and_tmp_and_delayed_ids :
           (Goal.goal * tac_ctx) Evd.sigma ->
           (Goal.goal * tac_ctx) list Evd.sigma

val view_error : string -> ssrterm -> 'a


val top_id : Id.t

val pf_abs_ssrterm :
           ?resolve_typeclasses:bool ->
           ist ->
           Goal.goal Evd.sigma ->
           ssrterm ->
           evar_map * EConstr.t * UState.t * int

val pf_interp_ty :
           ?resolve_typeclasses:bool ->
           Tacinterp.interp_sign ->
           Goal.goal Evd.sigma ->
           Ssrast.ssrtermkind *
           (Glob_term.glob_constr * Constrexpr.constr_expr option) ->
           int * EConstr.t * EConstr.t * UState.t

val ssr_n_tac : string -> int -> v82tac
val donetac : int -> v82tac

val applyn :
           with_evars:bool ->
           ?beta:bool ->
           ?with_shelve:bool ->
           int ->
           EConstr.t -> v82tac
exception NotEnoughProducts
val pf_saturate :
           ?beta:bool ->
           ?bi_types:bool ->
           Goal.goal Evd.sigma ->
           EConstr.constr ->
           ?ty:EConstr.types ->
           int ->
           EConstr.constr * EConstr.types * (int * EConstr.constr) list *
           Goal.goal Evd.sigma
val saturate :
           ?beta:bool ->
           ?bi_types:bool ->
           env ->
           evar_map ->
           EConstr.constr ->
           ?ty:EConstr.types ->
           int ->
           EConstr.constr * EConstr.types * (int * EConstr.constr) list * evar_map
val refine_with :
           ?first_goes_last:bool ->
           ?beta:bool ->
           ?with_evars:bool ->
           evar_map * EConstr.t -> v82tac
(*********************** Wrapped Coq  tactics *****************************)

val rewritetac : ssrdir -> EConstr.t -> tactic

type name_hint = (int * EConstr.types array) option ref

val gentac :
   Ssrast.ssrdocc * Ssrmatching.cpattern -> v82tac

val genstac :
  ((Ssrast.ssrhyp list option * Ssrmatching.occ) *
     Ssrmatching.cpattern)
    list * Ssrast.ssrhyp list ->
  Tacmach.tactic

val pf_interp_gen :
  Goal.goal Evd.sigma ->
  bool ->
  (Ssrast.ssrhyp list option * Ssrmatching.occ) *
    Ssrmatching.cpattern ->
  EConstr.t * EConstr.t * Ssrast.ssrhyp list *
    Goal.goal Evd.sigma

val pf_interp_gen_aux :
  Goal.goal Evd.sigma ->
  bool ->
  (Ssrast.ssrhyp list option * Ssrmatching.occ) *
    Ssrmatching.cpattern ->
  bool * Ssrmatching.pattern * EConstr.t *
    EConstr.t * Ssrast.ssrhyp list * UState.t *
      Goal.goal Evd.sigma

val is_name_in_ipats :
           Id.t -> ssripats -> bool

type profiler = { 
  profile : 'a 'b. ('a -> 'b) -> 'a -> 'b;
  reset : unit -> unit;
  print : unit -> unit }

val mk_profiler : string -> profiler

(** Basic tactics *)

val introid : ?orig:Name.t ref -> Id.t -> v82tac
val intro_anon : v82tac

val interp_clr :
  evar_map -> ssrhyps option * (ssrtermkind * EConstr.t) -> ssrhyps

val genclrtac :
  EConstr.constr ->
  EConstr.constr list -> Ssrast.ssrhyp list -> Tacmach.tactic
val old_cleartac : ssrhyps -> v82tac
val cleartac : ssrhyps -> unit Proofview.tactic

val tclMULT : int * ssrmmod -> Tacmach.tactic -> Tacmach.tactic

val unprotecttac : Goal.goal Evd.sigma -> Goal.goal list Evd.sigma
val is_protect : EConstr.t -> Environ.env -> Evd.evar_map -> bool

val abs_wgen :
  bool ->
  (Id.t -> Id.t) ->
  'a *
    ((Ssrast.ssrhyp_or_id * string) *
       Ssrmatching.cpattern option)
      option ->
  Goal.goal Evd.sigma * EConstr.t list * EConstr.t ->
  Goal.goal Evd.sigma * EConstr.t list * EConstr.t

val clr_of_wgen :
  ssrhyps * ((ssrhyp_or_id * 'a) * 'b option) option ->
  Proofview.V82.tac list -> Proofview.V82.tac list


val unfold : EConstr.t list -> unit Proofview.tactic

val apply_type : EConstr.types -> EConstr.t list -> Proofview.V82.tac

(* New code ****************************************************************)

(* To call old code *)
val tacSIGMA : Goal.goal Evd.sigma Proofview.tactic

val tclINTERP_AST_CLOSURE_TERM_AS_CONSTR :
  ast_closure_term -> EConstr.t list Proofview.tactic

val tacREDUCE_TO_QUANTIFIED_IND :
  EConstr.types ->
    ((Names.inductive * EConstr.EInstance.t) * EConstr.types) Proofview.tactic

val tacTYPEOF : EConstr.t -> EConstr.types Proofview.tactic

val tclINTRO_ID : Id.t -> unit Proofview.tactic
val tclINTRO_ANON : unit Proofview.tactic

(* Lower level API, calls conclusion with the name taken from the prod *)
val tclINTRO :
  id:Id.t option ->
  conclusion:(orig_name:Name.t -> new_name:Id.t -> unit Proofview.tactic) ->
  unit Proofview.tactic

val tclRENAME_HD_PROD : Name.t -> unit Proofview.tactic

(* calls the tactic only if there are more than 0 goals *)
val tcl0G : unit Proofview.tactic -> unit Proofview.tactic

(* like tclFIRST but with 'a tactic *)
val tclFIRSTa : 'a Proofview.tactic list -> 'a Proofview.tactic
val tclFIRSTi : (int -> 'a Proofview.tactic) -> int -> 'a Proofview.tactic

val tacCONSTR_NAME : ?name:Name.t -> EConstr.t -> Name.t Proofview.tactic

(* [tacMKPROD t name ctx] (where ctx is a term possibly containing an unbound
 * Rel 1) builds [forall name : ty_t, ctx] *)
val tacMKPROD :
  EConstr.t -> ?name:Name.t -> EConstr.types -> EConstr.types Proofview.tactic

val tacINTERP_CPATTERN : Ssrmatching.cpattern -> Ssrmatching.pattern Proofview.tactic
val tacUNIFY : EConstr.t -> EConstr.t -> unit Proofview.tactic

(* if [(t : eq _ _ _)] then we can inject it *)
val tacIS_INJECTION_CASE : ?ty:EConstr.types -> EConstr.t -> bool Proofview.tactic

(** 1 shot, hands-on the top of the stack, eg for [=> ->] *)
val tclWITHTOP : (EConstr.t -> unit Proofview.tactic) -> unit Proofview.tactic

val tacMK_SSR_CONST : string -> EConstr.t Proofview.tactic

module type StateType = sig
  type state
  val init : state
end

module MakeState(S : StateType) : sig

  val tclGET : (S.state -> unit Proofview.tactic) -> unit Proofview.tactic
  val tclSET : S.state -> unit Proofview.tactic
  val tacUPDATE : (S.state -> S.state Proofview.tactic) -> unit Proofview.tactic

  val get : Proofview.Goal.t -> S.state

end
