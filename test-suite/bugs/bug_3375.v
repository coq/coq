Require Import TestSuite.admit.
(* -*- mode: coq; coq-prog-args: ("-impredicative-set") -*- *)
(* File reduced by coq-bug-finder from original input, then from 5968 lines to 11933 lines, then from 11239 lines to 11231 lines, then from 10365 lines to 446 lines, then from 456 lines to 379 lines, then from 391 lines to 373 lines, then from 369 lines to 351 lines, then from 350 lines to 340 lines, then from 348 lines to 320 lines, then from 328 lines to 302 lines, then from 330 lines to 45 lines *)

Set Universe Polymorphism.
Axiom admit : forall {T}, T.
Definition UU := Set.
Definition dirprod ( X Y : UU ) := sigT ( fun x : X => Y ) .
Definition dirprodpair { X Y : UU } := existT ( fun x : X => Y ) .
Definition hProp := sigT (fun X : Type => admit).
Axiom hProppair : forall ( X : UU ) ( is : admit ), hProp.
Definition hProptoType := @projT1 _ _ : hProp -> Type .
Coercion hProptoType: hProp >-> Sortclass.
Definition ishinh_UU ( X : UU ) : UU := forall P: Set, ( ( X -> P ) -> P ).
Definition ishinh ( X : UU ) : hProp := hProppair ( ishinh_UU X ) admit.
Definition hsubtypes ( X : UU ) : Type := X -> hProp.
Axiom carrier : forall { X : UU } ( A : hsubtypes X ), Type.
Definition hrel ( X : UU ) : Type := X -> X -> hProp.
Set Printing Universes.
Definition iseqclass { X : UU } ( R : hrel X ) ( A : hsubtypes X ) : Type.
  intros; exact ( dirprod ( ishinh ( carrier A ) ) ( dirprod ( forall x1 x2 : X , R x1 x2 -> A x1 -> A x2 )
                                                             ( forall x1 x2 : X, A x1 ->  A x2 -> R x1 x2 ) )) .
Defined.
Definition iseqclassconstr' { X : UU } ( R : hrel X ) { A : hsubtypes X } ( ax0 : ishinh ( carrier A ) )
           ( ax1 : forall x1 x2 : X , R x1 x2 -> A x1 -> A x2 ) ( ax2 : forall x1 x2 : X, A x1 ->  A x2 -> R x1 x2 ) : iseqclass R A.
  intros.
  apply dirprodpair. { exact ax0. }
                     apply dirprodpair. { exact ax1. } {exact ax2. }
Defined.
Definition iseqclassconstr { X : UU } ( R : hrel X ) { A : hsubtypes X } ( ax0 : ishinh ( carrier A ) )
           ( ax1 : forall x1 x2 : X , R x1 x2 -> A x1 -> A x2 ) ( ax2 : forall x1 x2 : X, A x1 ->  A x2 -> R x1 x2 ) : iseqclass R A.
  pose @iseqclassconstr'.
  intros.
  exact (dirprodpair ax0 (dirprodpair ax1 ax2)).
Defined.
(* Toplevel input, characters 15-23:
Error: Illegal application:
The term "dirprodpair" of type
 "forall (X Y : UU) (x : X), (fun _ : X => Y) x -> {_ : X & Y}"
cannot be applied to the terms
 "forall x1 x2 : X, R x1 x2 -> A x1 -> A x2"
   : "Type@{max(Set, Top.476, Top.479)}"
 "forall x1 x2 : X, A x1 -> A x2 -> R x1 x2"
   : "Type@{max(Set, Top.476, Top.479)}"
 "ax1" : "forall x1 x2 : X, R x1 x2 -> A x1 -> A x2"
 "ax2" : "forall x1 x2 : X, A x1 -> A x2 -> R x1 x2"
The 1st term has type "Type@{max(Set, Top.476, Top.479)}"
which should be coercible to "UU".
 *)
