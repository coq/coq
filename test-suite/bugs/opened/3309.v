(* -*- coq-prog-args: ("-emacs" "-impredicative-set") -*- *)
(* File reduced by coq-bug-finder from original input, then from 5968 lines to 11933 lines, then from 11239 lines to 11231 lines, then from 10365 lines to 446 lines, then from 456 lines to 379 lines, then from 391 lines to 373 lines, then from 369 lines to 351 lines, then from 350 lines to 340 lines, then from 348 lines to 320 lines, then from 328 lines to 302 lines *)
Set Universe Polymorphism.
Record sigT' {A} (P : A -> Type) := existT' { projT1' : A; projT2' : P projT1' }.
Notation "{ x : A &' P }" := (sigT' (A := A) (fun x => P)) : type_scope.
Arguments existT' {A} P _ _.
Axiom admit : forall {T}, T.
Notation paths := identity .

Unset Automatic Introduction.

Definition UU := Set.

Definition dirprod ( X Y : UU ) := sigT' ( fun x : X => Y ) .
Definition dirprodpair { X Y : UU } := existT' ( fun x : X => Y ) .

Definition ddualand { X Y P : UU } (xp : ( X -> P ) -> P ) ( yp : ( Y -> P ) -> P ) : ( dirprod X Y -> P ) -> P.
Proof.
  intros X Y P xp yp X0 .
  set ( int1 := fun ypp : ( ( Y -> P ) -> P ) => fun x : X => yp ( fun y : Y => X0 ( dirprodpair x y) ) ) .
  apply ( xp ( int1 yp ) ) .
Defined .
Definition weq ( X Y : UU )  : UU .
intros; exact ( sigT' (fun f:X->Y => admit) ).
Defined.
Definition pr1weq ( X Y : UU):= @projT1' _ _ : weq X Y -> (X -> Y).
Coercion pr1weq : weq >-> Funclass.

Definition invweq { X Y : UU } ( w : weq X Y ) : weq Y X .
admit.
Defined.

Definition hProp := sigT' (fun X : Type => admit).

Definition hProppair ( X : UU ) ( is : admit ) : hProp@{i j Set k}.
intros; exact (existT' (fun X : UU => admit ) X is ).
Defined.
Definition hProptoType := @projT1' _ _ : hProp -> Type .
Coercion hProptoType: hProp >-> Sortclass.

Definition ishinh_UU ( X : UU ) : UU := forall P: Set, ( ( X -> P ) -> P ).

Definition ishinh ( X : UU ) : hProp := hProppair ( ishinh_UU X ) admit.

Definition hinhfun { X Y : UU } ( f : X -> Y ) : ishinh_UU X -> ishinh_UU Y.
intros X Y f; exact ( fun isx : ishinh X => fun P : _ =>  fun yp : Y -> P => isx P ( fun x : X => yp ( f x ) ) ).
Defined.

Definition hinhuniv { X : UU } { P : hProp } ( f : X -> P ) ( wit : ishinh_UU X ) : P.
intros; exact (  wit P f ).
Defined.

Definition hinhand { X Y : UU } ( inx1 : ishinh_UU X ) ( iny1 : ishinh_UU Y) : ishinh ( dirprod X Y ).
intros; exact ( fun P:_  => ddualand (inx1 P) (iny1 P)) .
Defined.

Definition UU' := Type.
Definition hSet:= sigT' (fun X : UU' => admit) .
Definition hSetpair := existT' (fun X : UU' => admit).
Definition pr1hSet:= @projT1' UU (fun X : UU' => admit) : hSet -> Type.
Coercion pr1hSet: hSet >-> Sortclass.

Definition hPropset : hSet := existT' _ hProp admit .

Definition hsubtypes ( X : UU ) : Type.
intros; exact (X -> hProp ).
Defined.
Definition carrier { X : UU } ( A : hsubtypes X ) : Type.
intros; exact (sigT' A).
Defined.
Coercion carrier : hsubtypes >-> Sortclass.

Definition subtypesdirprod { X Y : UU } ( A : hsubtypes X ) ( B : hsubtypes Y ) : hsubtypes ( dirprod X Y ).
admit.
Defined.

Lemma weqsubtypesdirprod { X Y : UU } ( A : hsubtypes X ) ( B : hsubtypes Y ) : weq ( subtypesdirprod A B ) ( dirprod A B ) .
  admit.
Defined.

Lemma ishinhsubtypesdirprod  { X Y : UU } ( A : hsubtypes X ) ( B : hsubtypes Y ) ( isa : ishinh A ) ( isb : ishinh B ) : ishinh ( subtypesdirprod A B ) .
Proof .
  intros .
  apply ( hinhfun ( invweq ( weqsubtypesdirprod A B ) ) ) .
  apply hinhand .
  apply isa .
  apply isb .
Defined .

Definition hrel ( X : UU ) : Type.
intros; exact ( X -> X -> hProp).
Defined.

Definition iseqrel { X : UU } ( R : hrel X ) : Type.
admit.
Defined.

Definition eqrel ( X : UU ) : Type.
intros; exact ( sigT' ( fun R : hrel X => iseqrel R ) ).
Defined.
Definition pr1eqrel ( X : UU ) : eqrel X -> ( X -> ( X -> hProp ) ) := @projT1' _ _ .
Coercion pr1eqrel : eqrel >-> Funclass .

Definition hreldirprod { X Y : UU } ( RX : hrel X ) ( RY : hrel Y ) : hrel ( dirprod X Y ) .
admit.
Defined.
Set Printing Universes.
Print hProp.
Print ishinh_UU.
Print hProppair.
Definition iseqclass { X : UU } ( R : hrel X ) ( A : hsubtypes X ) : Type.
intros; exact ( dirprod ( ishinh ( carrier A ) ) ( dirprod ( forall x1 x2 : X , R x1 x2 -> A x1 -> A x2 ) ( forall x1 x2 : X, A x1 ->  A x2 -> R x1 x2 ) )) .
Defined.
Definition iseqclassconstr { X : UU } ( R : hrel X ) { A : hsubtypes X } ( ax0 : ishinh ( carrier A ) ) ( ax1 : forall x1 x2 : X , R x1 x2 -> A x1 -> A x2 ) ( ax2 : forall x1 x2 : X, A x1 ->  A x2 -> R x1 x2 ) : iseqclass R A.
intros. hnf. apply dirprodpair. exact ax0. apply dirprodpair. exact ax1. exact ax2.
Defined.

Definition eqax0 { X : UU } { R : hrel X } { A : hsubtypes X }  : iseqclass R A -> ishinh ( carrier A ) .
intros X R A; exact ( fun is : iseqclass R A =>  projT1' _ is ).
Defined.

Lemma iseqclassdirprod { X Y : UU } { R : hrel X } { Q : hrel Y } { A : hsubtypes X } { B : hsubtypes Y } ( isa : iseqclass R A ) ( isb : iseqclass Q B ) : iseqclass ( hreldirprod R Q ) ( subtypesdirprod A B ) .
Proof .
  intros .
  set ( XY := dirprod X Y ) .
  set ( AB := subtypesdirprod A B ) .
  set ( RQ := hreldirprod R Q ) .
  set ( ax0 := ishinhsubtypesdirprod  A B ( eqax0 isa ) admit ) .
  apply ( iseqclassconstr _ ax0 admit admit ) .
Defined .

Definition image { X Y : UU } ( f : X -> Y ) : Type.
intros; exact ( sigT' ( fun y : Y => admit ) ).
Defined.
Definition pr1image { X Y : UU } ( f : X -> Y ) : image f -> Y.
intros X Y f; exact ( @projT1' _  ( fun y : Y => admit ) ).
Defined.

Definition prtoimage { X Y : UU } (f : X -> Y) : X -> image f.
  admit.
Defined.

Definition setquot { X : UU } ( R : hrel X ) : Type.
intros; exact ( sigT' ( fun A : _ => iseqclass R A ) ).
Defined.
Definition setquotpair { X : UU } ( R : hrel X ) ( A : hsubtypes X ) ( is : iseqclass R A ) : setquot R.
intros; exact (existT' _ A is ).
Defined.
Definition pr1setquot { X : UU } ( R : hrel X ) : setquot R -> ( hsubtypes X ).
intros X R.
exact ( @projT1' _ ( fun A : _ => iseqclass R A ) ).
Defined.
Coercion pr1setquot : setquot >-> hsubtypes .

Definition setquotinset { X : UU } ( R : hrel X ) : hSet.
intros; exact ( hSetpair (setquot R) admit) .
Defined.

Definition dirprodtosetquot { X Y : UU } ( RX : hrel X ) ( RY : hrel Y ) (cd : dirprod ( setquot RX ) ( setquot RY ) ) : setquot ( hreldirprod RX RY ).
intros; exact ( setquotpair _ _ ( iseqclassdirprod ( projT2' _ ( projT1' _ cd ) ) ( projT2' _  ( projT2' _ cd ) ) ) ).
Defined.

Definition iscomprelfun2 { X Y : UU } ( R : hrel X ) ( f : X -> X -> Y ) := forall x x' x0 x0' : X , R x x' ->  R x0 x0' ->  paths ( f x x0 ) ( f x' x0' ) .

Definition binop ( X : UU ) : Type.
intros; exact ( X -> X -> X ).
Defined.

Definition setwithbinop : Type.
exact (sigT' ( fun X : hSet => binop X ) ).
Defined.
Definition pr1setwithbinop : setwithbinop -> hSet@{j k Set l}.
unfold setwithbinop.
exact ( @projT1' _ ( fun X : hSet@{j k Set l} => binop@{Set} X ) ).
Defined.
Coercion pr1setwithbinop : setwithbinop >-> hSet .

Definition op { X : setwithbinop } : binop X.
intros; exact ( projT2' _ X ).
Defined.

Definition subsetswithbinop { X : setwithbinop } : Type.
admit.
Defined.

Definition carrierofasubsetwithbinop { X : setwithbinop } ( A : @subsetswithbinop X ) : setwithbinop .
admit.
Defined.

Coercion carrierofasubsetwithbinop : subsetswithbinop >-> setwithbinop .

Definition binopeqrel { X : setwithbinop } : Type.
intros; exact (sigT' ( fun R : eqrel X => admit ) ).
Defined.
Definition binopeqrelpair { X : setwithbinop } := existT' ( fun R : eqrel X => admit ).
Definition pr1binopeqrel ( X : setwithbinop ) : @binopeqrel X -> eqrel X.
intros X; exact ( @projT1' _ ( fun R : eqrel X => admit ) ) .
Defined.
Coercion pr1binopeqrel : binopeqrel >-> eqrel .

Definition setwithbinopdirprod ( X Y : setwithbinop ) : setwithbinop .
admit.
Defined.

Definition monoid : Type.
exact ( sigT' ( fun X : setwithbinop => admit ) ).
Defined.
Definition monoidpair := existT' ( fun X : setwithbinop => admit ) .
Definition pr1monoid : monoid -> setwithbinop := @projT1' _ _ .
Coercion pr1monoid : monoid >-> setwithbinop .

Notation "x + y" := ( op x y ) : addmonoid_scope .

Definition submonoids { X : monoid } : Type.
admit.
Defined.

Definition submonoidstosubsetswithbinop ( X : monoid ) : @submonoids X -> @subsetswithbinop X.
admit.
Defined.
Coercion  submonoidstosubsetswithbinop : submonoids >-> subsetswithbinop .

Definition abmonoid : Type.
exact (sigT' ( fun X : setwithbinop => admit ) ).
Defined.

Definition abmonoidtomonoid : abmonoid -> monoid.
exact (fun X : _ => monoidpair ( projT1' _ X ) admit ).
Defined.
Coercion abmonoidtomonoid : abmonoid >-> monoid .

Definition subabmonoids { X : abmonoid } := @submonoids X .

Definition carrierofsubabmonoid { X : abmonoid } ( A : @subabmonoids X ) : abmonoid .
Proof .
  intros .
  unfold subabmonoids in A .
  split with A .
  admit.
Defined .

Coercion carrierofsubabmonoid : subabmonoids >-> abmonoid .

Definition abmonoiddirprod ( X Y : abmonoid ) : abmonoid .
Proof .
  intros .
  split with ( setwithbinopdirprod X Y ) .
  admit.
Defined .

Open Scope addmonoid_scope .

Definition eqrelabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : eqrel ( setwithbinopdirprod X A ).
admit.
Defined.

Definition binopeqrelabmonoidfrac ( X : abmonoid ) ( A : @subabmonoids X ) : @binopeqrel ( abmonoiddirprod X A ).
intros; exact ( @binopeqrelpair ( setwithbinopdirprod X A ) ( eqrelabmonoidfrac X A ) admit ).
Defined.

Theorem setquotuniv  { X : UU } ( R : hrel X ) ( Y : hSet ) ( f : X -> Y ) ( c : setquot R ) : Y .
Proof.
  intros.
  apply ( pr1image ( fun x : c => f ( projT1' _ x ) ) ) .
  apply ( @hinhuniv ( projT1' _ c ) ( hProppair _ admit ) ( prtoimage ( fun x : c => f ( projT1' _ x ) ) ) ) .
  pose ( eqax0 ( projT2' _ c ) )  as h.
  simpl in *.
  Set Printing Universes.
  exact h.
Defined .

Definition setquotuniv2  { X : UU } ( R : hrel X ) ( Y : hSet ) ( f : X -> X -> Y ) ( is : iscomprelfun2 R f ) ( c c0 : setquot R ) : Y .
Proof.
  intros .
  set ( RR := hreldirprod R R ) .
  apply (setquotuniv RR Y admit).
  apply dirprodtosetquot.
  apply dirprodpair.
  exact c.
  exact c0.
Defined .

Definition  setquotfun2  { X Y : UU } ( RX : hrel X ) ( RY : eqrel Y ) ( f : X -> X -> Y ) ( cx cx0 : setquot RX ) : setquot RY .
Proof .
  intros .
  apply ( setquotuniv2 RX ( setquotinset RY ) admit admit admit admit ) .
Defined .

Definition quotrel  { X : UU } { R : hrel X } : hrel ( setquot R ).
intros; exact ( setquotuniv2 R hPropset admit admit ).
Defined.

Definition setwithbinopquot { X : setwithbinop } ( R : @binopeqrel X ) : setwithbinop .
Proof .
  intros .
  split with ( setquotinset R )  .
  set ( qtmlt := setquotfun2 R R op ) .
  simpl .
  unfold binop .
  apply qtmlt .
Defined .

Definition abmonoidquot { X : abmonoid } ( R : @binopeqrel X ) : abmonoid .
Proof .
  intros .
  split with  ( setwithbinopquot R )  .
  admit.
Defined .

Definition abmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : abmonoid.
intros; exact ( @abmonoidquot (abmonoiddirprod X (@carrierofsubabmonoid X A)) ( binopeqrelabmonoidfrac X A ) ).
Defined.

Definition abmonoidfracrel ( X : abmonoid ) ( A : @submonoids X ) :  hrel (@setquot (setwithbinopdirprod X A) (eqrelabmonoidfrac X A)).
intros; exact (@quotrel _ _).
Defined.

Fail Timeout 1 Axiom ispartlbinopabmonoidfracrel : forall ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( z : abmonoidfrac X A ) , @abmonoidfracrel X A ( ( admit + z ) )admit.

Definition ispartlbinopabmonoidfracrel_type : Type :=
  forall ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( z : abmonoidfrac X A ), 
    @abmonoidfracrel X A ( ( admit + z ) )admit.

Axiom ispartlbinopabmonoidfracrel : $(let t:= eval unfold ispartlbinopabmonoidfracrel_type in
                                      ispartlbinopabmonoidfracrel_type in exact t)$.

