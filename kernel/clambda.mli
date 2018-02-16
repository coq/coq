open Names
open Constr
open Vmvalues
open Environ

type lambda =
  | Lrel          of Name.t * int
  | Lvar          of Id.t
  | Levar         of Evar.t * lambda array
  | Lprod         of lambda * lambda
  | Llam          of Name.t array * lambda
  | Llet          of Name.t * lambda * lambda
  | Lapp          of lambda * lambda array
  | Lconst        of pconstant
  | Lprim         of pconstant option * CPrimitives.t * lambda array
        (* No check if None *)
  | Lcase         of case_info * reloc_table * lambda * lambda * lam_branches
  | Lif           of lambda * lambda * lambda
  | Lfix          of (int array * int) * fix_decl
  | Lcofix        of int * fix_decl
  | Lint          of int
  | Lmakeblock    of int * lambda array
  | Luint         of Uint63.t
  | Lval          of structured_values
  | Lsort         of Sorts.t
  | Lind          of pinductive
  | Lproj         of Projection.Repr.t * lambda

and lam_branches =
  { constant_branches : lambda array;
    nonconstant_branches : (Name.t array * lambda) array }

and fix_decl =  Name.t array * lambda array * lambda array

exception TooLargeInductive of Pp.t

val lambda_of_constr : optimize:bool -> env -> Constr.t -> lambda

val decompose_Llam : lambda -> Name.t array * lambda

val get_alias : env -> Constant.t -> Constant.t

(** Dump the VM lambda code after compilation (for debugging purposes) *)
val dump_lambda : bool ref
