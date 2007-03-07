(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(************************************************************************)
(*                                                                      *)
(* Representation of mini-ML terms                                      *)
(*                                                                      *)
(* Originally by Zaynah Dargaye (CompCert project, INRIA Rocquencourt)  *)
(*                                                                      *)
(************************************************************************)

(* $Id$ *)

(** premiere langage intermediaire Pml :
      les constructeur de type concrets sont representes par des numeros **)
Require Import List.

(** version de PMml en indice de de Bruijn **)
(** nous ajoutons les types concrets  numerote**)
Inductive term : Set :=
  | TDummy : term
  | TVar : nat -> term
  | TLet : term -> term -> term
  | TFun : term -> term
  | TLetrec : term -> term -> term
  | TApply : term -> term -> term
  | TConstr : nat -> list term -> term
  | TMatch : term -> list pat -> term
with pat : Set :=
  | Patc : nat -> term -> pat.
(** un programme Pml est un terme **)

(**Semantique de Pml **)

(** les valeurs **)
Inductive value : Set:=
  | VDummy : value
  | VClos : list value -> term -> value  (** env corps **)
  | VClos_rec : list value -> term -> value
  | VConstr : nat -> list value -> value (** num, param**)
.

(** predicat d'evaluation d'un terme dans un environnement : list de value**)

Inductive Peval : list value -> term -> value -> Prop:=
  | Peval_V : forall n e v,
                       nth_error e n = (Some v)-> Peval e (TVar n) v
  | Peval_Fun : forall e t , Peval e (TFun t) (VClos e t)
  | Peval_let : forall e t1 t2 v1 v ,
                           Peval e t1 v1 ->
                           Peval (v1::e)  t2 v ->
                           Peval e (TLet t1 t2) v
  | Peval_letrec : forall e t1 t2 v,
                           Peval ((VClos_rec e t1)::e) t2 v ->
                           Peval e (TLetrec t1 t2) v
  | Peval_app : forall e e' t t1 t2 v v2,
                            Peval e t1 (VClos e' t) ->
                            Peval e t2 v2 ->
                            Peval (v2::e') t v ->
                            Peval e (TApply t1 t2) v
  | Peval_appr : forall e e' t t1 t2 v v2,
                            Peval e t1 (VClos_rec e' t) ->
                            Peval e t2 v2 ->
                            Peval (v2::(VClos_rec e' t)::e') t v ->
                            Peval e (TApply t1 t2) v
  | Peval_constr : forall e tl vl n ,
                            Peval_list e tl vl -> Peval e (TConstr n tl) (VConstr n vl)
  | Peval_match : forall e t n pl vl m tn v,
                            Peval e t (VConstr n vl) ->
                            nth_error pl n = Some (Patc m tn) ->
                            length vl = m ->
                            Peval ((rev vl)++e) tn v ->
                            Peval e (TMatch t pl) v
with
Peval_list : list value->list term-> list value ->Prop:=
   | Peval_nil : forall e , Peval_list e nil nil
   | Peval_cons : forall e t lt v lv , Peval e t v -> Peval_list e lt lv ->
                                          Peval_list e (t::lt) (v::lv)
.

Scheme peval_term_ind6 := Minimality for Peval Sort Prop
 with peval_terml_ind6 := Minimality for Peval_list Sort Prop.
