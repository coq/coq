open Names
open Constr
open Vmvalues
open Environ

type case_annot = case_info * reloc_table * Declarations.recursivity_kind

type lambda =
  | Lrel          of Name.t * int
  | Lvar          of Id.t
  | Lmeta         of metavariable * lambda (* type *)
  | Levar         of Evar.t * lambda array
  | Lprod         of lambda * lambda
  | Llam          of Name.t Context.binder_annot array * lambda
  | Llet          of Name.t Context.binder_annot * lambda * lambda
  | Lapp          of lambda * lambda array
  | Lconst        of pconstant
  | Lproj         of Projection.Repr.t * lambda
  | Lprim         of pconstant * CPrimitives.t * lambda array
  | Lcase         of case_annot * lambda * lambda * lam_branches
  | Lfix          of (int array * inductive array * int) * fix_decl
  | Lcofix        of int * fix_decl
  | Lint          of int
  | Lparray       of lambda array * lambda
  | Lmakeblock    of inductive * int * lambda array
  | Luint         of Uint63.t
  | Lfloat        of Float64.t
  | Lval          of structured_values
  | Lsort         of Sorts.t
  | Lind          of pinductive
  | Lforce

and lam_branches =
  { constant_branches : lambda array;
    nonconstant_branches : (Name.t Context.binder_annot array * lambda) array }

and fix_decl =  Name.t Context.binder_annot array * lambda array * lambda array

exception TooLargeInductive of Pp.t

type evars =
    { evars_val : constr evar_handler;
      evars_metas : metavariable -> types }

val empty_evars : evars

val lambda_of_constr : optimize:bool -> env -> evars -> Constr.t -> lambda

val decompose_Llam : lambda -> Name.t Context.binder_annot array * lambda

val get_alias : env -> Constant.t -> Constant.t

(** Dump the VM lambda code after compilation (for debugging purposes) *)
val dump_lambda : bool ref
