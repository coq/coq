(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Names
open Environ
open Evd
open Constrexpr
open Ssrast

open Ltac_plugin

open Ssrmatching_plugin

val allocc : ssrocc

(******************************** hyps ************************************)

val hyp_id : ssrhyp -> Id.t
val hyps_ids : ssrhyps -> Id.t list
val check_hyp_exists : ('a, 'b) Context.Named.pt -> ssrhyp -> unit
val test_hyp_exists : ('a, 'b) Context.Named.pt -> ssrhyp -> bool
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

val interp_term :
  Environ.env -> Evd.evar_map ->
  Tacinterp.interp_sign ->
    ssrterm -> evar_map * EConstr.t

val interp_hyp : ist -> env -> evar_map -> ssrhyp -> ssrhyp
val interp_hyps : ist -> env -> evar_map -> ssrhyps -> ssrhyps

val interp_refine :
  Environ.env -> Evd.evar_map -> Tacinterp.interp_sign -> concl:EConstr.constr ->
    Glob_term.glob_constr -> evar_map * EConstr.constr

val interp_open_constr :
  Environ.env -> Evd.evar_map ->
  Tacinterp.interp_sign ->
    Genintern.glob_constr_and_expr -> evar_map * EConstr.t

val splay_open_constr :
           Environ.env ->
           evar_map * EConstr.t ->
           (Names.Name.t Context.binder_annot * EConstr.t) list * EConstr.t
val isAppInd : Environ.env -> Evd.evar_map -> EConstr.types -> bool

val mk_term : ssrtermkind -> constr_expr -> ssrterm
val mk_lterm : constr_expr -> ssrterm

val mk_ast_closure_term :
  [ `None | `Parens | `DoubleParens | `At ] ->
  Constrexpr.constr_expr -> ast_closure_term
val interp_ast_closure_term : Geninterp.interp_sign -> env -> evar_map -> ast_closure_term -> ast_closure_term
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
val type_id : Environ.env -> Evd.evar_map -> EConstr.types -> Id.t

val abs_evars :
           Environ.env -> Evd.evar_map -> ?rigid:Evar.t list ->
           evar_map * EConstr.t ->
           EConstr.t * Evar.t list *
           UState.t
val abs_cterm :
           Environ.env -> Evd.evar_map -> int -> EConstr.t -> EConstr.t

val constr_name : evar_map -> EConstr.t -> Name.t

val mkSsrRef : string -> GlobRef.t
val mkSsrRRef : string -> Glob_term.glob_constr * 'a option
val mkSsrConst : Environ.env -> Evd.evar_map -> string -> Evd.evar_map * EConstr.t

val is_discharged_id : Id.t -> bool
val mk_discharged_id : Id.t -> Id.t
val is_tagged : string -> string -> bool
val has_discharged_tag : string -> bool
val ssrqid : string -> Libnames.qualid
val mk_anon_id : string -> Id.t list -> Id.t
val nbargs_open_constr : Environ.env -> Evd.evar_map * EConstr.t -> int
val pf_nbargs : Environ.env -> Evd.evar_map -> EConstr.t -> int

val ssrevaltac :
  Tacinterp.interp_sign -> Tacinterp.Value.t -> unit Proofview.tactic

val convert_concl_no_check : EConstr.t -> unit Proofview.tactic
val convert_concl : check:bool -> EConstr.t -> unit Proofview.tactic

val red_safe :
  Reductionops.reduction_function ->
  env -> evar_map -> EConstr.t -> EConstr.t

val red_product_skip_id :
  env -> evar_map -> EConstr.t -> EConstr.t

val ssrautoprop_tac :
           unit Proofview.tactic ref

val mkProt :
  Environ.env ->
  Evd.evar_map ->
  EConstr.t ->
  EConstr.t ->
  Evd.evar_map * EConstr.t

val mkEtaApp : EConstr.t -> int -> int -> EConstr.t

val mkRefl :
  Environ.env ->
  Evd.evar_map ->
  EConstr.t ->
  EConstr.t ->
  Evd.evar_map * EConstr.t

val discharge_hyp :
           Id.t * (Id.t * string) -> unit Proofview.tactic

val view_error : string -> ssrterm -> 'a Proofview.tactic


val top_id : Id.t

val abs_ssrterm :
           ?resolve_typeclasses:bool ->
           ist ->
           Environ.env -> Evd.evar_map ->
           ssrterm ->
           Evd.evar_map * EConstr.t * int

val pf_interp_ty :
           ?resolve_typeclasses:bool ->
           Environ.env ->
           Evd.evar_map ->
           Tacinterp.interp_sign ->
           Ssrast.ssrtermkind *
           (Glob_term.glob_constr * Constrexpr.constr_expr option) ->
           Evd.evar_map * int * EConstr.t * EConstr.t

val ssr_n_tac : string -> int -> unit Proofview.tactic
val donetac : int -> unit Proofview.tactic

val applyn :
           with_evars:bool ->
           ?beta:bool ->
           ?with_shelve:bool ->
           ?first_goes_last:bool ->
           int ->
           EConstr.t -> unit Proofview.tactic
exception NotEnoughProducts
val saturate :
           ?beta:bool ->
           ?bi_types:bool ->
           env ->
           evar_map ->
           EConstr.constr ->
           ?ty:EConstr.types ->
           int ->
           EConstr.constr * EConstr.types * (int * EConstr.constr * EConstr.types) list * evar_map
val refine_with :
           ?first_goes_last:bool ->
           ?beta:bool ->
           ?with_evars:bool ->
           evar_map * EConstr.t -> unit Proofview.tactic

val resolve_typeclasses :
  Environ.env -> Evd.evar_map ->
  where:EConstr.t ->
  fail:bool -> Evd.evar_map

(*********************** Wrapped Coq  tactics *****************************)

val rewritetac : ?under:bool -> ssrdir -> EConstr.t -> unit Proofview.tactic

type name_hint = (int * EConstr.types array) option ref

val gentac :
   Ssrast.ssrdocc * Ssrmatching.cpattern -> unit Proofview.tactic

val genstac :
  ((Ssrast.ssrhyp list option * Ssrmatching.occ) *
     Ssrmatching.cpattern)
    list * Ssrast.ssrhyp list ->
  unit Proofview.tactic

val interp_gen :
  Environ.env ->
  Evd.evar_map ->
  concl:EConstr.t ->
  bool ->
  (Ssrast.ssrhyp list option * Ssrmatching.occ) *
    Ssrmatching.cpattern ->
  Evd.evar_map * (EConstr.t * EConstr.t * Ssrast.ssrhyp list)

(** Basic tactics *)

val introid : ?orig:Name.t ref -> Id.t -> unit Proofview.tactic
val intro_anon : unit Proofview.tactic

val interp_clr :
  evar_map -> ssrhyps option * (ssrtermkind * EConstr.t) -> ssrhyps

val genclrtac :
  EConstr.constr ->
  EConstr.constr list -> Ssrast.ssrhyp list -> unit Proofview.tactic
val cleartac : ssrhyps -> unit Proofview.tactic

val tclMULT : int * ssrmmod -> unit Proofview.tactic -> unit Proofview.tactic

val unprotecttac : unit Proofview.tactic
val is_protect : EConstr.t -> Environ.env -> Evd.evar_map -> bool

val abs_wgen :
  Environ.env ->
  Evd.evar_map ->
  bool ->
  (Id.t -> Id.t) ->
  'a *
    ((Ssrast.ssrhyp_or_id * string) *
       Ssrmatching.cpattern option)
      option ->
  EConstr.t list * EConstr.t ->
  Evd.evar_map * EConstr.t list * EConstr.t

val clr_of_wgen :
  ssrhyps * ((ssrhyp_or_id * 'a) * 'b option) option ->
  unit Proofview.tactic list -> unit Proofview.tactic list


val unfold : EConstr.t list -> unit Proofview.tactic

(* New code ****************************************************************)

val tclINTERP_AST_CLOSURE_TERM_AS_CONSTR :
  ast_closure_term -> EConstr.t list Proofview.tactic

val tacREDUCE_TO_QUANTIFIED_IND :
  EConstr.types ->
    ((Names.inductive * EConstr.EInstance.t) * EConstr.types) Proofview.tactic

val tacTYPEOF : EConstr.t -> EConstr.types Proofview.tactic

val tclINTRO_ID : Id.t -> unit Proofview.tactic
val tclINTRO_ANON : ?seed:string -> unit -> unit Proofview.tactic

(* Lower level API, calls conclusion with the name taken from the prod *)
type intro_id =
  | Anon
  | Id of Id.t
  | Seed of string

val tclINTRO :
  id:intro_id ->
  conclusion:(orig_name:Name.t -> new_name:Id.t -> unit Proofview.tactic) ->
  unit Proofview.tactic

val tclRENAME_HD_PROD : Name.t -> unit Proofview.tactic

(* calls the tactic only if there are more than 0 goals *)
val tcl0G : default:'a -> 'a Proofview.tactic -> 'a Proofview.tactic

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
  val tclGET1 : (S.state -> 'a Proofview.tactic) -> 'a Proofview.tactic
  val tclSET : S.state -> unit Proofview.tactic
  val tacUPDATE : (S.state -> S.state Proofview.tactic) -> unit Proofview.tactic

  val get : Proofview.Goal.t -> S.state

end

val is_ind_ref : Evd.evar_map -> EConstr.t -> Names.GlobRef.t -> bool
val is_construct_ref : Evd.evar_map -> EConstr.t -> Names.GlobRef.t -> bool
val is_const_ref : Evd.evar_map -> EConstr.t -> Names.GlobRef.t -> bool
