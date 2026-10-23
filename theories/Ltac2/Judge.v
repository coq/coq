(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Ltac2 Require Import Init.
From Ltac2 Require Constr.

(** Judgements provide safe APIs to handle terms in environments which
    are not the implicit goal environment. *)

(** A judgement [Γ ⊢ c : t]. *)
Ltac2 Type termj.

(** A type judgement [Γ ⊢ t : s] ([s] is a sort). *)
Ltac2 Type typej.

(** From argument [Γ ⊢ c : t] return [Γ]. *)
Ltac2 @external env_of_termj : termj -> env
  := "rocq-runtime.plugins.ltac2" "env_of_termj".

(** From argument [Γ ⊢ t : s] return [Γ]. *)
Ltac2 @external env_of_typej : typej -> env
  := "rocq-runtime.plugins.ltac2" "env_of_typej".

(** Returns the idents bound in argument [Γ]. *)
Ltac2 @external env_hyps : env -> ident list
  := "rocq-runtime.plugins.ltac2" "env_hyps".

(** From [id] and [Γ], if [id : t ∈ Γ] or [id := v : t ∈ Γ] return [Γ ⊢ id : t].
    If [id ∉ Γ], [Err]. *)
Ltac2 @external hypj : ident -> env -> termj result
  := "rocq-runtime.plugins.ltac2" "hypj".

(** From [id] and [Γ], if [id := v : t ∈ Γ] return [Val (Some (Γ ⊢ v : t))].
    If [id : t ∈ Γ] without a body, return [Val None].
    If [id ∉ Γ], [Err]. *)
Ltac2 @external hyp_valuej : ident -> env -> termj option result
  := "rocq-runtime.plugins.ltac2" "hyp_valuej".

(** From arguments [Γ] and [c],
    check that [c] is well typed in [Γ] inferring type [t]
    and return [Γ ⊢ c : t]. *)
Ltac2 @external infer_termj : env -> constr -> termj result
  := "rocq-runtime.plugins.ltac2" "infer_termj".

(* XXX version which doesn't define evars? *)
(** If the given judgement is [Γ ⊢ t : s] where [s] is a sort
    (or evar which can be defined to a fresh sort),
    return type judgement [Γ ⊢ t : s].
    Not to be confused with [typej_of_termj]. *)
Ltac2 @external termj_is_typej : termj -> typej result
  := "rocq-runtime.plugins.ltac2" "termj_is_typej".

(** From type judgement [Γ ⊢ t : s] return term judgement [Γ ⊢ t : s]. *)
Ltac2 @external typej_is_termj : typej -> termj
  := "rocq-runtime.plugins.ltac2" "typej_is_termj".

(** From argument [Γ ⊢ c : t], return [Γ ⊢ t : s].
    Must retype [t] to get its sort [s]. *)
Ltac2 @external typej_of_termj : termj -> typej
  := "rocq-runtime.plugins.ltac2" "typej_of_termj".

(** From argument [Γ ⊢ t : s], return [s] *)
Ltac2 @external sort_of_typej : typej -> sort
  := "rocq-runtime.plugins.ltac2" "sort_of_typej".

(** From [Γ] and [s] produce [Γ ⊢ s : s+1].
    Using this may cause inconvenient errors until algebraic universe
    support improves in Rocq. *)
Ltac2 @external typej_of_sort : env -> sort -> typej
  := "rocq-runtime.plugins.ltac2" "typej_of_sort".

(** From arguments [id] and [Γ ⊢ t : s], produce [Γ, id : t].
    [id] must be fresh in [Γ]. [t] must not contain local (Rel) variables. *)
Ltac2 @external push_named_assum : ident -> typej -> env
  := "rocq-runtime.plugins.ltac2" "push_named_assum".

(** From arguments [id] and [Γ ⊢ c : t], produce [Γ, id := c : t].
    [id] must be fresh in [Γ]. [c] and [t] must not contain local (Rel) variables.
    The relevance is obtained by examining the term
    (faster than retyping but not quite constant time). *)
Ltac2 @external push_named_def : ident -> termj -> env
  := "rocq-runtime.plugins.ltac2" "push_named_def".

(** Infer a term judgement from a preterm in a given environment. *)
Ltac2 @external pretype_judge : Constr.Pretype.Flags.t -> env -> preterm -> termj result
  := "rocq-runtime.plugins.ltac2" "pretype_judge".

(** Infer a type judgement from a preterm in a given environment. *)
Ltac2 @external pretype_type_judge : Constr.Pretype.Flags.t -> env -> preterm -> typej result
  := "rocq-runtime.plugins.ltac2" "pretype_type_judge".

(** Infer a term judgement from a preterm at a given expected type
    (the judgement for the expected type contains the environment). *)
Ltac2 @external pretype_in_expecting : Constr.Pretype.Flags.t -> preterm -> typej -> termj result
  := "rocq-runtime.plugins.ltac2" "pretype_in_expecting".

(** Print the given environment. Named and local variables are not distinguished. *)
Ltac2 @external message_of_env : env -> message
  := "rocq-runtime.plugins.ltac2" "message_of_env".

Module UnsafeEnv.
(** Functions in this module may be unsafe in two ways:
    - The function expects invariants on the arguments to be true but does not check them.
      Typically [termj] does not check that its arguments are related.
    - Calling the function is safe, but combining it with safe functions is not.
      Typically [term_of_termj] is safe, but calling [Std.eval_cbv] on the result is not safe.
 *)

  (** From argument [Γ ⊢ c : t] return [c]. *)
  Ltac2 @external term_of_termj : termj -> constr
    := "rocq-runtime.plugins.ltac2" "term_of_termj".

  (** From argument [Γ ⊢ t : s] return [t]. *)
  Ltac2 @external type_of_typej : typej -> constr
    := "rocq-runtime.plugins.ltac2" "type_of_typej".

  (** From arguments [Γ] [t] and [s] return [Γ ⊢ t : s] without checking anything. *)
  Ltac2 @external typej : env -> constr -> sort -> typej
    := "rocq-runtime.plugins.ltac2" "unsafe_typej".

  (** From arguments [c] and [Γ ⊢ t : s] return [Γ ⊢ c : t] without checking anything. *)
  Ltac2 @external termj : constr -> typej -> termj
    := "rocq-runtime.plugins.ltac2" "unsafe_termj".

  (** From arguments [Γ] [id] [t] and [r], produces [Γ, id : t]
      assuming [t] has relevance [r].
      Throws if [id] is already bound in [Γ].
      Does not check anything else (e.g. that [t] is valid or has relevance [r] in [Γ]). *)
  Ltac2 @external push_named_assum : env -> ident -> constr -> Constr.Relevance.t -> env
    := "rocq-runtime.plugins.ltac2" "unsafe_push_named_assum".

  (** From arguments [Γ] [id] [c] [t] and [r], produces [Γ, id := c : t]
      assuming [t] has relevance [r].
      Throws if [id] is already bound in [Γ].
      Does not check anything else. *)
  Ltac2 @external push_named_def : env -> ident -> constr -> constr -> Constr.Relevance.t -> env
    := "rocq-runtime.plugins.ltac2" "unsafe_push_named_def".

  (** Produces the [binder] corresponding to a type judgement and a name.

      Safe to call, but [binder] does not retain context information
      so using the resulting value with safe APIs
      (eg [Std.eval_hnf (Constr.Binder.type (of_typej ...))])
      is not safe. *)
  Ltac2 binder_of_typej (na : ident option) (j : typej) : binder :=
    Constr.Binder.unsafe_make na (Constr.Relevance.of_sort (sort_of_typej j)) (type_of_typej j).


End UnsafeEnv.
