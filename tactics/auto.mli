(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Term
open Sign
open Proof_type
open Tacmach
open Clenv
open Pattern
open Environ
open Evd
open Libnames
open Vernacexpr
(*i*)
  
type auto_tactic = 
  | Res_pf     of constr * unit clausenv    (* Hint Apply *)
  | ERes_pf    of constr * unit clausenv    (* Hint EApply *)
  | Give_exact of constr                  
  | Res_pf_THEN_trivial_fail of constr * unit clausenv (* Hint Immediate *)
  | Unfold_nth of global_reference          (* Hint Unfold *)
  | Extern     of Tacexpr.glob_tactic_expr   (* Hint Extern *)

open Rawterm

type pri_auto_tactic = { 
  hname : identifier;     (* name of the hint *)
  pri   : int;            (* A number between 0 and 4, 4 = lower priority *)
  pat   : constr_pattern option; (* A pattern for the concl of the Goal *)
  code  : auto_tactic;    (* the tactic to apply when the concl matches pat *)
}

type stored_data = pri_auto_tactic 

type search_entry = stored_data list * stored_data list * stored_data Btermdn.t

module Hint_db :
  sig
    type t
    val empty : t
    val find : constr_label -> t -> search_entry
    val map_all : constr_label -> t -> pri_auto_tactic list
    val map_auto : constr_label * constr -> t -> pri_auto_tactic list
    val add_one : constr_label * pri_auto_tactic -> t -> t
    val add_list : (constr_label * pri_auto_tactic) list -> t -> t
    val iter : (constr_label -> stored_data list -> unit) -> t -> unit
  end

type frozen_hint_db_table = Hint_db.t Stringmap.t

type hint_db_table = Hint_db.t Stringmap.t ref

type hint_db_name = string

val add_hints : locality_flag -> hint_db_name list -> hints -> unit

val print_searchtable : unit -> unit

val print_applicable_hint : unit -> unit

val print_hint_ref : global_reference -> unit

val print_hint_db_by_name : hint_db_name -> unit

val searchtable : hint_db_table

(* [make_exact_entry hint_name (c, ctyp)]. 
   [hint_name] is the name of then hint;
   [c] is the term given as an exact proof to solve the goal;
   [ctyp] is the type of [hc]. *)

val make_exact_entry :
  identifier -> constr * constr -> constr_label * pri_auto_tactic

(* [make_apply_entry (eapply,verbose) name (c,cty)].
   [eapply] is true if this hint will be used only with EApply;
   [name] is the name of then hint;
   [c] is the term given as an exact proof to solve the goal;
   [cty] is the type of [hc]. *)

val make_apply_entry :
  env -> evar_map -> bool * bool -> identifier -> constr * constr
      -> constr_label * pri_auto_tactic

(* A constr which is Hint'ed will be:
   (1) used as an Exact, if it does not start with a product
   (2) used as an Apply, if its HNF starts with a product, and
       has no missing arguments.
   (3) used as an EApply, if its HNF starts with a product, and
       has missing arguments. *)

val make_resolves :
  env -> evar_map -> identifier -> bool * bool -> constr * constr -> 
    (constr_label * pri_auto_tactic) list

(* [make_resolve_hyp hname htyp].
   used to add an hypothesis to the local hint database;
   Never raises an User_exception;
   If the hyp cannot be used as a Hint, the empty list is returned. *)

val make_resolve_hyp : 
  env -> evar_map -> named_declaration ->
      (constr_label * pri_auto_tactic) list

(* [make_extern name pri pattern tactic_expr] *)

val make_extern :
  identifier -> int -> constr_pattern -> Tacexpr.glob_tactic_expr
      -> constr_label * pri_auto_tactic

val set_extern_interp :
  (patvar_map -> Tacexpr.glob_tactic_expr -> tactic) -> unit

val set_extern_intern_tac :
  (patvar list -> Tacexpr.raw_tactic_expr -> Tacexpr.glob_tactic_expr)
  -> unit

val set_extern_subst_tactic :
  (Names.substitution -> Tacexpr.glob_tactic_expr -> Tacexpr.glob_tactic_expr)
  -> unit

(* Create a Hint database from the pairs (name, constr).
   Useful to take the current goal hypotheses as hints *)

val make_local_hint_db : goal sigma -> Hint_db.t

val priority : (int * 'a) list -> 'a list

val default_search_depth : int ref

(* Try unification with the precompiled clause, then use registered Apply *)
val unify_resolve : (constr * unit clausenv) -> tactic

(* [ConclPattern concl pat tacast]:
   if the term concl matches the pattern pat, (in sense of 
   [Pattern.somatches], then replace [?1] [?2] metavars in tacast by the
   right values to build a tactic *)

val conclPattern : constr -> constr_pattern -> Tacexpr.glob_tactic_expr -> tactic

(* The Auto tactic *)

val auto : int -> hint_db_name list -> tactic

(* auto with default search depth and with the hint database "core" *)
val default_auto : tactic

(* auto with all hint databases except the "v62" compatibility database *)
val full_auto : int -> tactic

(* auto with default search depth and with all hint databases 
   except the "v62" compatibility database *)
val default_full_auto : tactic

(* The generic form of auto (second arg [None] means all bases) *)
val gen_auto : int option -> hint_db_name list option -> tactic

(* The hidden version of auto *)
val h_auto   : int option -> hint_db_name list option -> tactic

(* Trivial *)
val trivial : hint_db_name list -> tactic
val gen_trivial : hint_db_name list option -> tactic
val full_trivial : tactic
val h_trivial : hint_db_name list option -> tactic

val fmt_autotactic : auto_tactic -> Pp.std_ppcmds

(*s The following is not yet up to date -- Papageno. *)

(* DAuto *)
val dauto : int option * int option -> tactic
val default_search_decomp : int ref
val default_dauto : tactic

val h_dauto : int option * int option -> tactic
(* SuperAuto *)

type autoArguments =
  | UsingTDB       
  | Destructing   

(*
val superauto : int -> (identifier * constr) list -> autoArguments list -> tactic
*)

val h_superauto : int option -> reference list -> bool -> bool -> tactic
