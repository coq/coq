(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
(*i*)

(*s Signatures of ordered named declarations *)

type named_context = named_declaration list
type section_context = named_context

val empty_named_context : named_context
val add_named_decl : named_declaration -> named_context -> named_context
val vars_of_named_context : named_context -> identifier list

val lookup_named : identifier -> named_context -> named_declaration

(* number of declarations *)
val named_context_length : named_context -> int

(*s Recurrence on [named_context]: older declarations processed first *)
val fold_named_context :
  (named_declaration -> 'a -> 'a) -> named_context -> init:'a -> 'a
(* newer declarations first *)
val fold_named_context_reverse :
  ('a -> named_declaration -> 'a) -> init:'a -> named_context -> 'a

(*s Section-related auxiliary functions *)
val instance_from_named_context : named_context -> constr array

(*s Signatures of ordered optionally named variables, intended to be
   accessed by de Bruijn indices *)

(* In [rel_context], more recent declaration is on top *)
type rel_context = rel_declaration list

val empty_rel_context : rel_context
val add_rel_decl : rel_declaration -> rel_context -> rel_context

val lookup_rel : int -> rel_context -> rel_declaration
val rel_context_length : rel_context -> int
val rel_context_nhyps : rel_context -> int

val push_named_to_rel_context : named_context -> rel_context -> rel_context

(*s Recurrence on [rel_context]: older declarations processed first *)
val fold_rel_context :
  (rel_declaration -> 'a -> 'a) -> rel_context -> init:'a -> 'a
(* newer declarations first *)
val fold_rel_context_reverse :
  ('a -> rel_declaration -> 'a) -> init:'a -> rel_context -> 'a

(*s Map function of [rel_context] *)
val map_rel_context : (constr -> constr) -> rel_context -> rel_context

(*s Map function of [named_context] *)
val map_named_context : (constr -> constr) -> named_context -> named_context

(*s Map function of [rel_context] *)
val iter_rel_context : (constr -> unit) -> rel_context -> unit

(*s Map function of [named_context] *)
val iter_named_context : (constr -> unit) -> named_context -> unit

(*s Term constructors *)

val it_mkLambda_or_LetIn : constr -> rel_context -> constr
val it_mkProd_or_LetIn : types -> rel_context -> types

(*s Term destructors *)

(* Destructs a term of the form $(x_1:T_1)..(x_n:T_n)s$ into the pair *)
type arity = rel_context * sorts
val destArity : types -> arity
val mkArity : arity -> types
val isArity : types -> bool

(* Transforms a product term $(x_1:T_1)..(x_n:T_n)T$ including letins
   into the pair $([(x_n,T_n);...;(x_1,T_1)],T)$, where $T$ is not a
   product nor a let. *)
val decompose_prod_assum : types -> rel_context * types

(* Transforms a lambda term $[x_1:T_1]..[x_n:T_n]T$ including letins
   into the pair $([(x_n,T_n);...;(x_1,T_1)],T)$, where $T$ is not a
   lambda nor a let. *)
val decompose_lam_assum : constr -> rel_context * constr

(* Given a positive integer n, transforms a product term 
   $(x_1:T_1)..(x_n:T_n)T$
   into the pair $([(xn,Tn);...;(x1,T1)],T)$. *)
val decompose_prod_n_assum : int -> types -> rel_context * types

(* Given a positive integer $n$, transforms a lambda term 
   $[x_1:T_1]..[x_n:T_n]T$ into the pair $([(x_n,T_n);...;(x_1,T_1)],T)$ *)
val decompose_lam_n_assum : int -> constr -> rel_context * constr
