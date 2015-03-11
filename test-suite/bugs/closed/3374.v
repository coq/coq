Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 5968 lines to 11933 lines, then from 11239 lines to 11231 lines, then from 10365 lines to 446 lines, then from 456 lines to 379 lines, then from 391 lines to 373 lines, then from 369 lines to 351 lines, then from 350 lines to 340 lines, then from 348 lines to 320 lines, then from 328 lines to 302 lines, then from 331 lines to 59 lines *)

Set Universe Polymorphism.
Axiom admit : forall {T}, T.
Notation paths := identity .
Definition UU := Set.
Definition dirprod ( X Y : UU ) := sigT ( fun x : X => Y ) .
Definition dirprodpair { X Y : UU } := existT ( fun x : X => Y ) .
Definition hProp := sigT (fun X : Type => admit).
Definition hProptoType := @projT1 _ _ : hProp -> Type .
Coercion hProptoType: hProp >-> Sortclass.
Definition UU' := Type.
Definition hSet:= sigT (fun X : UU' => admit) .
Definition pr1hSet:= @projT1 UU (fun X : UU' => admit) : hSet -> Type.
Coercion pr1hSet: hSet >-> Sortclass.
Axiom hsubtypes : UU -> Type.
Definition hrel ( X : UU ) := X -> X -> hProp.
Axiom hreldirprod : forall { X Y : UU } ( RX : hrel X ) ( RY : hrel Y ), hrel ( dirprod X Y ) .
Axiom iseqclass : forall { X : UU } ( R : hrel X ) ( A : hsubtypes X ), Type.
Definition setquot { X : UU } ( R : hrel X ) : Type := sigT (fun A => iseqclass R A).
Axiom dirprodtosetquot : forall { X Y : UU } ( RX : hrel X ) ( RY : hrel Y ) (cd : dirprod ( setquot RX ) ( setquot RY ) ),
                           setquot ( hreldirprod RX RY ).
Definition iscomprelfun2 { X Y : UU } ( R : hrel X ) ( f : X -> X -> Y )
  := forall x x' x0 x0' : X , R x x' ->  R x0 x0' ->  paths ( f x x0 ) ( f x' x0' ) .
Axiom setquotuniv : forall  { X : UU } ( R : hrel X ) ( Y : hSet ) ( f : X -> Y ) ( c : setquot R ), Y .
Definition setquotuniv2  { X : UU } ( R : hrel X ) ( Y : hSet ) ( f : X -> X -> Y ) ( is : iscomprelfun2 R f ) ( c c0 : setquot R )
: Y .
Proof.
  intros .
  set ( RR := hreldirprod R R ) .
  apply (setquotuniv RR Y admit).
  apply (dirprodtosetquot R R).
  apply dirprodpair; [ exact c | exact c0 ].
  Undo.
  exact (dirprodpair c c0).
Defined.
  (* Toplevel input, characters 39-40:
Error:
In environment
X : UU
R : hrel X
Y : hSet
f : X -> X -> Y
is : iscomprelfun2 R f
c : setquot R
c0 : setquot R
RR := hreldirprod R R : hrel (dirprod X X)
The term "c" has type "setquot R" while it is expected to have type
"?42" (unable to find a well-typed instantiation for
"?42": cannot unify"Type" and "UU").
 *)
