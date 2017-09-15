(* File reduced by coq-bug-finder from original input, then from 1549 lines to  298 lines, then from 277 lines to 133 lines, then from 985 lines to 138 lines,  then from 206 lines to 139 lines, then from 203 lines to 142 lines, then from  262 lines to 152 lines, then from 567 lines to 151 lines, then from 3746 lines  to 151 lines, then from 577 lines to 151 lines, then from 187 lines to 151  lines, thenfrom 981 lines to 940 lines, then from 938 lines to 175 lines, then  from 589 lines to 205 lines, then from 3797 lines to 205 lines, then from 628  lines to 206 lines, then from 238 lines to 205 lines, then from 1346 lines to  213 lines, then from 633 lines to 214 lines, then from 243 lines to 213 lines,  then from 5656 lines to 245 lines, then from 661 lines to 272 lines, then from  3856 lines to 352 lines, then from 1266 lines to 407 lines, then from 421 lines  to 406 lines, then from 424 lines to 91 lines, then from 105 lines to 91 lines,  then from 85 lines to 55 lines, then from 69 lines to 55 lines *)
(* coqc version trunk (May 2017) compiled on May 30 2017 13:28:59 with OCaml 
4.02.3
   coqtop version jgross-Leopard-WS:/home/jgross/Downloads/coq/coq-trunk,trunk  (fd36c0451c26e44b1b7e93299d3367ad2d35fee3) *)

Class Proper {A} (R : A -> A -> Prop) (m : A) := mkp : R m m.
Definition respectful {A B} (R : A -> A -> Prop) (R' : B -> B -> Prop) (f g : A  -> B) := forall x y, R x y -> R' (f x) (g y).
Set Implicit Arguments.

Class EqDec (A : Set) := {
  eqb : A -> A -> bool ;
  eqb_leibniz : forall x y, eqb x y = true <-> x = y
}.

Infix "?=" := eqb (at level 70) : eq_scope.

Inductive Comp : Set -> Type :=
| Bind : forall (A B : Set), Comp B -> (B -> Comp A) -> Comp A.

Open Scope eq_scope.

Goal forall (Rat : Set) (PositiveMap_t : Set -> Set)
            type (t : type) (interp_type_list_message interp_type_rand  interp_type_message : nat -> Set),
    (forall eta : nat, PositiveMap_t (interp_type_rand eta) ->  interp_type_list_message eta -> interp_type_message eta) ->
    ((nat -> Rat) -> Prop) ->
    forall (interp_type_sbool : nat -> Set) (interp_type0 : type -> nat -> Set),
      (forall eta : nat,
          (interp_type_list_message eta -> interp_type_message eta) ->  PositiveMap_t (interp_type_rand eta) -> interp_type0 t eta)
      -> (forall (t0 : type) (eta : nat), EqDec (interp_type0 t0 eta))
      -> (bool -> Comp bool) -> False.
  clear.
  intros Rat PositiveMap_t type t interp_type_list_message interp_type_rand  interp_type_message adv negligible interp_type_sbool
         interp_type interp_term_fixed_t_x
         EqDec_interp_type ret_bool.
  assert (forall f adv' k
                 (lem : forall (eta : nat) (evil_rands rands : PositiveMap_t 
(interp_type_rand eta)),
                     (interp_term_fixed_t_x eta (adv eta evil_rands) rands
                                            ?= interp_term_fixed_t_x eta (adv  eta evil_rands) rands) = true),
             (forall (eta : nat), Proper (respectful eq eq) (f eta))
             -> negligible
                  (fun eta : nat =>
                     f eta (
                         (Bind (k eta) (fun rands =>
                          ret_bool (interp_term_fixed_t_x eta (adv' eta) rands  ?= interp_term_fixed_t_x eta (adv' eta) rands)))))).
  Undo.
  assert (forall f adv' k
                 (lem : forall (eta : nat) (rands : PositiveMap_t 
(interp_type_rand eta)),
                     (interp_term_fixed_t_x eta (adv' eta) rands ?=  interp_term_fixed_t_x eta (adv' eta) rands) = true),
             (forall (eta : nat), Proper (respectful eq eq) (f eta))
             -> negligible
                  (fun eta : nat =>
                     f eta (
                         (Bind (k eta) (fun rands =>
                          ret_bool (interp_term_fixed_t_x eta (adv' eta) rands  ?= interp_term_fixed_t_x eta (adv' eta) rands)))))).
 (* Error: Anomaly "Signature and its instance do not match." Please report at http://coq.inria.fr/bugs/. *)
