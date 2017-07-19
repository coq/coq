(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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

val errorstrm : Pp.std_ppcmds -> 'a
val anomaly : string -> 'a

val array_app_tl : 'a array -> 'a list -> 'a list
val array_list_of_tl : 'a array -> 'a list
val array_fold_right_from : int -> ('a -> 'b -> 'b) -> 'a array -> 'b -> 'b

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
val isAppInd : Goal.goal Evd.sigma -> EConstr.types -> bool
val interp_view_nbimps :
           Tacinterp.interp_sign ->
           Goal.goal Evd.sigma -> Glob_term.glob_constr -> int
val interp_nbargs :
           Tacinterp.interp_sign ->
           Goal.goal Evd.sigma -> Glob_term.glob_constr -> int


val mk_term : ssrtermkind -> 'b -> ssrtermkind * (Glob_term.glob_constr * 'b option)
val mk_lterm : 'a -> ssrtermkind * (Glob_term.glob_constr * 'a option)

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
           Term.constr -> Goal.goal Evd.sigma * Term.types
val pfe_type_of :
           Goal.goal Evd.sigma ->
           EConstr.t -> Goal.goal Evd.sigma * EConstr.types
val pf_abs_prod :
           Name.t ->
           Goal.goal Evd.sigma ->
           EConstr.t ->
           EConstr.t -> Goal.goal Evd.sigma * EConstr.types
val pf_mkprod :
           Goal.goal Evd.sigma ->
           EConstr.t ->
           ?name:Name.t ->
           EConstr.t -> Goal.goal Evd.sigma * EConstr.types

val mkSsrRRef : string -> Glob_term.glob_constr * 'a option
val mkSsrRef : string -> Globnames.global_reference
val mkSsrConst : 
           string ->
           env -> evar_map -> evar_map * EConstr.t
val pf_mkSsrConst :
           string ->
           Goal.goal Evd.sigma ->
           EConstr.t * Goal.goal Evd.sigma
val new_wild_id : tac_ctx -> Names.Id.t * tac_ctx


val pf_fresh_global :
           Globnames.global_reference ->
           Goal.goal Evd.sigma ->
           Term.constr * Goal.goal Evd.sigma

val is_discharged_id : Id.t -> bool
val mk_discharged_id : Id.t -> Id.t
val is_tagged : string -> string -> bool
val has_discharged_tag : string -> bool
val ssrqid : string -> Libnames.qualid 
val new_tmp_id :
  tac_ctx -> (Names.Id.t * Name.t ref) * tac_ctx
val mk_anon_id : string -> Goal.goal Evd.sigma -> Id.t
val pf_abs_evars_pirrel :
           Goal.goal Evd.sigma ->
           evar_map * Term.constr -> int * Term.constr
val pf_nbargs : Goal.goal Evd.sigma -> EConstr.t -> int
val gen_tmp_ids : 
           ?ist:Geninterp.interp_sign ->
           (Goal.goal * tac_ctx) Evd.sigma ->
           (Goal.goal * tac_ctx) list Evd.sigma

val ssrevaltac : Tacinterp.interp_sign -> Tacinterp.Value.t -> Proofview.V82.tac

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
  (Geninterp.interp_sign ->
   (Ssrast.ssrdocc) *
     Ssrmatching_plugin.Ssrmatching.cpattern -> Tacmach.tactic)

val genstac :
  ((Ssrast.ssrhyp list option * Ssrmatching_plugin.Ssrmatching.occ) *
     Ssrmatching_plugin.Ssrmatching.cpattern)
    list * Ssrast.ssrhyp list ->
  Tacinterp.interp_sign -> Tacmach.tactic

val pf_interp_gen :
  Tacinterp.interp_sign ->
  Goal.goal Evd.sigma ->
  bool ->
  (Ssrast.ssrhyp list option * Ssrmatching_plugin.Ssrmatching.occ) *
    Ssrmatching_plugin.Ssrmatching.cpattern ->
  EConstr.t * EConstr.t * Ssrast.ssrhyp list *
    Goal.goal Evd.sigma

val pf_interp_gen_aux :
  Tacinterp.interp_sign ->
  Goal.goal Evd.sigma ->
  bool ->
  (Ssrast.ssrhyp list option * Ssrmatching_plugin.Ssrmatching.occ) *
    Ssrmatching_plugin.Ssrmatching.cpattern ->
  bool * Ssrmatching_plugin.Ssrmatching.pattern * EConstr.t *
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
val intro_all : v82tac

val interp_clr :
  evar_map -> ssrhyps option * (ssrtermkind * EConstr.t) -> ssrhyps

val genclrtac :
  EConstr.constr ->
  EConstr.constr list -> Ssrast.ssrhyp list -> Tacmach.tactic
val cleartac : ssrhyps -> v82tac

val tclMULT : int * ssrmmod -> Tacmach.tactic -> Tacmach.tactic

val unprotecttac : Goal.goal Evd.sigma -> Goal.goal list Evd.sigma

val abs_wgen :
  bool ->
  Tacinterp.interp_sign ->
  (Id.t -> Id.t) ->
  'a *
    ((Ssrast.ssrhyp_or_id * string) *
       Ssrmatching_plugin.Ssrmatching.cpattern option)
      option ->
  Goal.goal Evd.sigma * EConstr.t list * EConstr.t ->
  Goal.goal Evd.sigma * EConstr.t list * EConstr.t

val clr_of_wgen :
  ssrhyps * ((ssrhyp_or_id * 'a) * 'b option) option ->
  Proofview.V82.tac list -> Proofview.V82.tac list


