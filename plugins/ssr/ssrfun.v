(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

(** #<style> .doc { font-family: monospace; white-space: pre; } </style># **)

Require Import ssreflect.


(**
 This file contains the basic definitions and notations for working with
 functions. The definitions provide for:

 - Pair projections:
    p.1  == first element of a pair
    p.2  == second element of a pair
   These notations also apply to p : P /\ Q, via an and >-> pair coercion.

 - Simplifying functions, beta-reduced by /= and simpl:
           #[#fun : T => E#]# == constant function from type T that returns E
             #[#fun x => E#]# == unary function
         #[#fun x : T => E#]# == unary function with explicit domain type
           #[#fun x y => E#]# == binary function
       #[#fun x y : T => E#]# == binary function with common domain type
         #[#fun (x : T) y => E#]# \
 #[#fun (x : xT) (y : yT) => E#]# | == binary function with (some) explicit,
         #[#fun x (y : T) => E#]# / independent domain types for each argument

 - Partial functions using option type:
     oapp f d ox == if ox is Some x returns f x,        d otherwise
      odflt d ox == if ox is Some x returns x,          d otherwise
      obind f ox == if ox is Some x returns f x,        None otherwise
       omap f ox == if ox is Some x returns Some (f x), None otherwise

 - Singleton types:
  all_equal_to x0 == x0 is the only value in its type, so any such value
                     can be rewritten to x0.

 - A generic wrapper type:
       wrapped T == the inductive type with values Wrap x for x : T.
        unwrap w == the projection of w : wrapped T on T.
          wrap x == the canonical injection of x : T into wrapped T; it is
                    equivalent to Wrap x, but is declared as a (default)
                    Canonical Structure, which lets the Coq HO unification
                    automatically expand x into unwrap (wrap x). The delta
                    reduction of wrap x to Wrap can be exploited to
                    introduce controlled nondeterminism in Canonical
                    Structure inference, as in the implementation of
                    the mxdirect predicate in matrix.v.

 - Sigma types:
           tag w == the i of w : {i : I & T i}.
        tagged w == the T i component of w : {i : I & T i}.
      Tagged T x == the {i : I & T i} with component x : T i.
          tag2 w == the i of w : {i : I & T i & U i}.
       tagged2 w == the T i component of w : {i : I & T i & U i}.
      tagged2' w == the U i component of w : {i : I & T i & U i}.
 Tagged2 T U x y == the {i : I & T i} with components x : T i and y : U i.
          sval u == the x of u : {x : T | P x}.
         s2val u == the x of u : {x : T | P x & Q x}.
   The properties of sval u, s2val u are given by lemmas svalP, s2valP, and
   s2valP'. We provide coercions sigT2 >-> sigT and sig2 >-> sig >-> sigT.
   A suite of lemmas (all_sig, ...) let us skolemize sig, sig2, sigT, sigT2
   and pair, e.g.,
     have /all_sig#[#f fP#]# (x : T): {y : U | P y} by ...
   yields an f : T -> U such that fP : forall x, P (f x).
 - Identity functions:
    id           == NOTATION for the explicit identity function fun x => x.
    @id T        == notation for the explicit identity at type T.
    idfun        == an expression with a head constant, convertible to id;
                    idfun x simplifies to x.
    @idfun T     == the expression above, specialized to type T.
    phant_id x y == the function type phantom _ x -> phantom _ y.
 *** In addition to their casual use in functional programming, identity
 functions are often used to trigger static unification as part of the
 construction of dependent Records and Structures. For example, if we need
 a structure sT over a type T, we take as arguments T, sT, and a "dummy"
 function T -> sort sT:
   Definition foo T sT & T -> sort sT := ...
 We can avoid specifying sT directly by calling foo (@id T), or specify
 the call completely while still ensuring the consistency of T and sT, by
 calling @foo T sT idfun. The phant_id type allows us to extend this trick
 to non-Type canonical projections. It also allows us to sidestep
 dependent type constraints when building explicit records, e.g., given
    Record r := R {x; y : T(x)}.
 if we need to build an r from a given y0 while inferring some x0, such
 that y0 : T(x0), we pose
    Definition mk_r .. y .. (x := ...) y' & phant_id y y' := R x y'.
 Calling @mk_r .. y0 .. id will cause Coq to use y' := y0, while checking
 the dependent type constraint y0 : T(x0).

 - Extensional equality for functions and relations (i.e. functions of two
   arguments):
    f1 =1 f2      ==  f1 x is equal to f2 x for all x.
    f1 =1 f2 :> A ==    ... and f2 is explicitly typed.
    f1 =2 f2      ==  f1 x y is equal to f2 x y for all x y.
    f1 =2 f2 :> A ==    ... and f2 is explicitly typed.

 - Composition for total and partial functions:
            f^~ y == function f with second argument specialised to y,
                     i.e., fun x => f x y
                     CAVEAT: conditional (non-maximal) implicit arguments
                     of f are NOT inserted in this context
            @^~ x == application at x, i.e., fun f => f x
          #[#eta f#]# == the explicit eta-expansion of f, i.e., fun x => f x
                     CAVEAT: conditional (non-maximal) implicit arguments
                     of f are NOT inserted in this context.
          fun=> v := the constant function fun _ => v.
        f1 \o f2  == composition of f1 and f2.
                     Note: (f1 \o f2) x simplifies to f1 (f2 x).
         f1 \; f2 == categorical composition of f1 and f2. This expands to
                     to f2 \o f1 and (f1 \; f2) x simplifies to f2 (f1 x).
      pcomp f1 f2 == composition of partial functions f1 and f2.


 - Properties of functions:
      injective f <-> f is injective.
       cancel f g <-> g is a left inverse of f / f is a right inverse of g.
      pcancel f g <-> g is a left inverse of f where g is partial.
      ocancel f g <-> g is a left inverse of f where f is partial.
      bijective f <-> f is bijective (has a left and right inverse).
     involutive f <-> f is involutive.

 - Properties for operations.
              left_id e op <-> e is a left identity for op (e op x = x).
             right_id e op <-> e is a right identity for op (x op e = x).
     left_inverse e inv op <-> inv is a left inverse for op wrt identity e,
                               i.e., (inv x) op x = e.
    right_inverse e inv op <-> inv is a right inverse for op wrt identity e
                               i.e., x op (i x) = e.
         self_inverse e op <-> each x is its own op-inverse (x op x = e).
             idempotent op <-> op is idempotent for op (x op x = x).
              associative op <-> op is associative, i.e.,
                               x op (y op z) = (x op y) op z.
            commutative op <-> op is commutative (x op y = y op x).
       left_commutative op <-> op is left commutative, i.e.,
                                   x op (y op z) = y op (x op z).
      right_commutative op <-> op is right commutative, i.e.,
                                   (x op y) op z = (x op z) op y.
            left_zero z op <-> z is a left zero for op (z op x = z).
           right_zero z op <-> z is a right zero for op (x op z = z).
  left_distributive op1 op2 <-> op1 distributes over op2 to the left:
                             (x op2 y) op1 z = (x op1 z) op2 (y op1 z).
 right_distributive op1 op2 <-> op distributes over add to the right:
                             x op1 (y op2 z) = (x op1 z) op2 (x op1 z).
        interchange op1 op2 <-> op1 and op2 satisfy an interchange law:
                        (x op2 y) op1 (z op2 t) = (x op1 z) op2 (y op1 t).
  Note that interchange op op is a commutativity property.
         left_injective op <-> op is injective in its left argument:
                             x op y = z op y -> x = z.
        right_injective op <-> op is injective in its right argument:
                             x op y = x op z -> y = z.
          left_loop inv op <-> op, inv obey the inverse loop left axiom:
                              (inv x) op (x op y) = y for all x, y, i.e.,
                              op (inv x) is always a left inverse of op x
      rev_left_loop inv op <-> op, inv obey the inverse loop reverse left
                              axiom: x op ((inv x) op y) = y, for all x, y.
         right_loop inv op <-> op, inv obey the inverse loop right axiom:
                              (x op y) op (inv y) = x for all x, y.
     rev_right_loop inv op <-> op, inv obey the inverse loop reverse right
                              axiom: (x op y) op (inv y) = x for all x, y.
   Note that familiar "cancellation" identities like x + y - y = x or
 x - y + y = x are respectively instances of right_loop and rev_right_loop
 The corresponding lemmas will use the K and NK/VK suffixes, respectively.

 - Morphisms for functions and relations:
    {morph f : x / a >-> r} <-> f is a morphism with respect to functions
                               (fun x => a) and (fun x => r); if r == R#[#x#]#,
                               this states that f a = R#[#f x#]# for all x.
          {morph f : x / a} <-> f is a morphism with respect to the
                               function expression (fun x => a). This is
                               shorthand for {morph f : x / a >-> a}; note
                               that the two instances of a are often
                               interpreted at different types.
  {morph f : x y / a >-> r} <-> f is a morphism with respect to functions
                               (fun x y => a) and (fun x y => r).
        {morph f : x y / a} <-> f is a morphism with respect to the
                               function expression (fun x y => a).
     {homo f : x / a >-> r} <-> f is a homomorphism with respect to the
                               predicates (fun x => a) and (fun x => r);
                               if r == R#[#x#]#, this states that a -> R#[#f x#]#
                               for all x.
           {homo f : x / a} <-> f is a homomorphism with respect to the
                               predicate expression (fun x => a).
   {homo f : x y / a >-> r} <-> f is a homomorphism with respect to the
                               relations (fun x y => a) and (fun x y => r).
         {homo f : x y / a} <-> f is a homomorphism with respect to the
                               relation expression (fun x y => a).
     {mono f : x / a >-> r} <-> f is monotone with respect to projectors
                               (fun x => a) and (fun x => r); if r == R#[#x#]#,
                               this states that R#[#f x#]# = a for all x.
           {mono f : x / a} <-> f is monotone with respect to the projector
                               expression (fun x => a).
   {mono f : x y / a >-> r} <-> f is monotone with respect to relators
                               (fun x y => a) and (fun x y => r).
         {mono f : x y / a} <-> f is monotone with respect to the relator
                               expression (fun x y => a).

 The file also contains some basic lemmas for the above concepts.
 Lemmas relative to cancellation laws use some abbreviated suffixes:
   K - a cancellation rule like esymK : cancel (@esym T x y) (@esym T y x).
  LR - a lemma moving an operation from the left hand side of a relation to
       the right hand side, like canLR: cancel g f -> x = g y -> f x = y.
  RL - a lemma moving an operation from the right to the left, e.g., canRL.
 Beware that the LR and RL orientations refer to an "apply" (back chaining)
 usage; when using the same lemmas with "have" or "move" (forward chaining)
 the directions will be reversed!.                                           **)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope fun_scope with FUN.
Open Scope fun_scope.

(**  Notations for argument transpose  **)
Notation "f ^~ y" := (fun x => f x y)
  (at level 10, y at level 8, no associativity, format "f ^~  y") : fun_scope.
Notation "@^~ x" := (fun f => f x)
  (at level 10, x at level 8, no associativity, format "@^~  x") : fun_scope.

Delimit Scope pair_scope with PAIR.
Open Scope pair_scope.

(**  Notations for pair/conjunction projections  **)
Notation "p .1" := (fst p)
  (at level 2, left associativity, format "p .1") : pair_scope.
Notation "p .2" := (snd p)
  (at level 2, left associativity, format "p .2") : pair_scope.

Coercion pair_of_and P Q (PandQ : P /\ Q) := (proj1 PandQ, proj2 PandQ).

Definition all_pair I T U (w : forall i : I, T i * U i) :=
  (fun i => (w i).1, fun i => (w i).2).

(**
 Complements on the option type constructor, used below to
 encode partial functions.                                   **)

Module Option.

Definition apply aT rT (f : aT -> rT) x u := if u is Some y then f y else x.

Definition default T := apply (fun x : T => x).

Definition bind aT rT (f : aT -> option rT) := apply f None.

Definition map aT rT (f : aT -> rT) := bind (fun x => Some (f x)).

End Option.

Notation oapp := Option.apply.
Notation odflt := Option.default.
Notation obind := Option.bind.
Notation omap := Option.map.
Notation some := (@Some _) (only parsing).

(**  Shorthand for some basic equality lemmas.  **)

Notation erefl := refl_equal.
Notation ecast i T e x := (let: erefl in _ = i := e return T in x).
Definition esym := sym_eq.
Definition nesym := sym_not_eq.
Definition etrans := trans_eq.
Definition congr1 := f_equal.
Definition congr2 := f_equal2.
(**  Force at least one implicit when used as a view.  **)
Prenex Implicits esym nesym.

(**  A predicate for singleton types.  **)
Definition all_equal_to T (x0 : T) := forall x, unkeyed x = x0.

Lemma unitE : all_equal_to tt. Proof. by case. Qed.

(**  A generic wrapper type  **)

Structure wrapped T := Wrap {unwrap : T}.
Canonical wrap T x := @Wrap T x.

Prenex Implicits unwrap wrap Wrap.

(**
 Syntax for defining auxiliary recursive function.
  Usage:
 Section FooDefinition.
 Variables (g1 : T1) (g2 : T2).  (globals)
 Fixoint foo_auxiliary (a3 : T3) ... :=
        body, using #[#rec e3, ... #]# for recursive calls
 where " #[# 'rec' a3 , a4 , ... #]#" := foo_auxiliary.
 Definition foo x y .. := #[#rec e1, ... #]#.
 + proofs about foo
 End FooDefinition.                                          **)

Reserved Notation "[ 'rec' a0 ]"
  (at level 0, format "[ 'rec'  a0 ]").
Reserved Notation "[ 'rec' a0 , a1 ]"
  (at level 0, format "[ 'rec'  a0 ,  a1 ]").
Reserved Notation "[ 'rec' a0 , a1 , a2 ]"
  (at level 0, format "[ 'rec'  a0 ,  a1 ,  a2 ]").
Reserved Notation "[ 'rec' a0 , a1 , a2 , a3 ]"
  (at level 0, format "[ 'rec'  a0 ,  a1 ,  a2 ,  a3 ]").
Reserved Notation "[ 'rec' a0 , a1 , a2 , a3 , a4 ]"
  (at level 0, format "[ 'rec'  a0 ,  a1 ,  a2 ,  a3 ,  a4 ]").
Reserved Notation "[ 'rec' a0 , a1 , a2 , a3 , a4 , a5 ]"
  (at level 0, format "[ 'rec'  a0 ,  a1 ,  a2 ,  a3 ,  a4 ,  a5 ]").
Reserved Notation "[ 'rec' a0 , a1 , a2 , a3 , a4 , a5 , a6 ]"
  (at level 0, format "[ 'rec'  a0 ,  a1 ,  a2 ,  a3 ,  a4 ,  a5 ,  a6 ]").
Reserved Notation "[ 'rec' a0 , a1 , a2 , a3 , a4 , a5 , a6 , a7 ]"
  (at level 0,
  format "[ 'rec'  a0 ,  a1 ,  a2 ,  a3 ,  a4 ,  a5 ,  a6 ,  a7 ]").
Reserved Notation "[ 'rec' a0 , a1 , a2 , a3 , a4 , a5 , a6 , a7 , a8 ]"
  (at level 0,
  format "[ 'rec'  a0 ,  a1 ,  a2 ,  a3 ,  a4 ,  a5 ,  a6 ,  a7 ,  a8 ]").
Reserved Notation "[ 'rec' a0 , a1 , a2 , a3 , a4 , a5 , a6 , a7 , a8 , a9 ]"
  (at level 0,
  format "[ 'rec'  a0 ,  a1 ,  a2 ,  a3 ,  a4 ,  a5 ,  a6 ,  a7 ,  a8 ,  a9 ]").

(**
 Definitions and notation for explicit functions with simplification,
 i.e., which simpl and /= beta expand (this is complementary to nosimpl).  **)

Section SimplFun.

Variables aT rT : Type.

Variant simpl_fun := SimplFun of aT -> rT.

Definition fun_of_simpl f := fun x => let: SimplFun lam := f in lam x.

Coercion fun_of_simpl : simpl_fun >-> Funclass.

End SimplFun.

Notation "[ 'fun' : T => E ]" := (SimplFun (fun _ : T => E))
  (at level 0,
   format "'[hv' [ 'fun' :  T  => '/ '  E ] ']'") : fun_scope.

Notation "[ 'fun' x => E ]" := (SimplFun (fun x => E))
  (at level 0, x ident,
   format "'[hv' [ 'fun'  x  => '/ '  E ] ']'") : fun_scope.

Notation "[ 'fun' x : T => E ]" := (SimplFun (fun x : T => E))
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'fun' x y => E ]" := (fun x => [fun y => E])
  (at level 0, x ident, y ident,
   format "'[hv' [ 'fun'  x  y  => '/ '  E ] ']'") : fun_scope.

Notation "[ 'fun' x y : T => E ]" := (fun x : T => [fun y : T => E])
  (at level 0, x ident, y ident, only parsing) : fun_scope.

Notation "[ 'fun' ( x : T ) y => E ]" := (fun x : T => [fun y => E])
  (at level 0, x ident, y ident, only parsing) : fun_scope.

Notation "[ 'fun' x ( y : T ) => E ]" := (fun x => [fun y : T => E])
  (at level 0, x ident, y ident, only parsing) : fun_scope.

Notation "[ 'fun' ( x : xT ) ( y : yT ) => E ]" :=
    (fun x : xT => [fun y : yT => E])
  (at level 0, x ident, y ident, only parsing) : fun_scope.

(**  For delta functions in eqtype.v.  **)
Definition SimplFunDelta aT rT (f : aT -> aT -> rT) := [fun z => f z z].

(**
 Extensional equality, for unary and binary functions, including syntactic
 sugar.                                                                      **)

Section ExtensionalEquality.

Variables A B C : Type.

Definition eqfun (f g : B -> A) : Prop := forall x, f x = g x.

Definition eqrel (r s : C -> B -> A) : Prop := forall x y, r x y = s x y.

Lemma frefl f : eqfun f f. Proof. by []. Qed.
Lemma fsym f g : eqfun f g -> eqfun g f. Proof. by move=> eq_fg x. Qed.

Lemma ftrans f g h : eqfun f g -> eqfun g h -> eqfun f h.
Proof. by move=> eq_fg eq_gh x; rewrite eq_fg. Qed.

Lemma rrefl r : eqrel r r. Proof. by []. Qed.

End ExtensionalEquality.

Typeclasses Opaque eqfun.
Typeclasses Opaque eqrel.

Hint Resolve frefl rrefl.

Notation "f1 =1 f2" := (eqfun f1 f2)
  (at level 70, no associativity) : fun_scope.
Notation "f1 =1 f2 :> A" := (f1 =1 (f2 : A))
  (at level 70, f2 at next level, A at level 90) : fun_scope.
Notation "f1 =2 f2" := (eqrel f1 f2)
  (at level 70, no associativity) : fun_scope.
Notation "f1 =2 f2 :> A" := (f1 =2 (f2 : A))
  (at level 70, f2 at next level, A at level 90) : fun_scope.

Section Composition.

Variables A B C : Type.

Definition funcomp u (f : B -> A) (g : C -> B) x := let: tt := u in f (g x).
Definition catcomp u g f := funcomp u f g.
Local Notation comp := (funcomp tt).

Definition pcomp (f : B -> option A) (g : C -> option B) x := obind f (g x).

Lemma eq_comp f f' g g' : f =1 f' -> g =1 g' -> comp f g =1 comp f' g'.
Proof. by move=> eq_ff' eq_gg' x; rewrite /= eq_gg' eq_ff'. Qed.

End Composition.

Notation comp := (funcomp tt).
Notation "@ 'comp'" := (fun A B C => @funcomp A B C tt).
Notation "f1 \o f2" := (comp f1 f2)
  (at level 50, format "f1  \o '/ '  f2") : fun_scope.
Notation "f1 \; f2" := (catcomp tt f1 f2)
  (at level 60, right associativity, format "f1  \; '/ '  f2") : fun_scope.

Notation "[ 'eta' f ]" := (fun x => f x)
  (at level 0, format "[ 'eta'  f ]") : fun_scope.

Notation "'fun' => E" := (fun _ => E) (at level 200, only parsing) : fun_scope.

Notation id := (fun x => x).
Notation "@ 'id' T" := (fun x : T => x)
  (at level 10, T at level 8, only parsing) : fun_scope.

Definition id_head T u x : T := let: tt := u in x.
Definition explicit_id_key := tt.
Notation idfun := (id_head tt).
Notation "@ 'idfun' T " := (@id_head T explicit_id_key)
  (at level 10, T at level 8, format "@ 'idfun'  T") : fun_scope.

Definition phant_id T1 T2 v1 v2 := phantom T1 v1 -> phantom T2 v2.

(**  Strong sigma types.  **)

Section Tag.

Variables (I : Type) (i : I) (T_ U_ : I -> Type).

Definition tag := projT1.
Definition tagged : forall w, T_(tag w) := @projT2 I [eta T_].
Definition Tagged x := @existT I [eta T_] i x.

Definition tag2 (w : @sigT2 I T_ U_) := let: existT2 _ _ i _ _ := w in i.
Definition tagged2 w : T_(tag2 w) := let: existT2 _ _ _ x _ := w in x.
Definition tagged2' w : U_(tag2 w) := let: existT2 _ _ _ _ y := w in y.
Definition Tagged2 x y := @existT2 I [eta T_] [eta U_] i x y.

End Tag.

Arguments Tagged [I i].
Arguments Tagged2 [I i].
Prenex Implicits tag tagged Tagged tag2 tagged2 tagged2' Tagged2.

Coercion tag_of_tag2 I T_ U_ (w : @sigT2 I T_ U_) :=
  Tagged (fun i => T_ i * U_ i)%type (tagged2 w, tagged2' w).

Lemma all_tag I T U :
   (forall x : I, {y : T x & U x y}) ->
  {f : forall x, T x & forall x, U x (f x)}.
Proof. by move=> fP; exists (fun x => tag (fP x)) => x; case: (fP x). Qed.

Lemma all_tag2 I T U V :
    (forall i : I, {y : T i & U i y & V i y}) ->
  {f : forall i, T i & forall i, U i (f i) & forall i, V i (f i)}.
Proof. by case/all_tag=> f /all_pair[]; exists f. Qed.

(**  Refinement types.  **)

(**  Prenex Implicits and renaming.  **)
Notation sval := (@proj1_sig _ _).
Notation "@ 'sval'" := (@proj1_sig) (at level 10, format "@ 'sval'").

Section Sig.

Variables (T : Type) (P Q : T -> Prop).

Lemma svalP (u : sig P) : P (sval u). Proof. by case: u. Qed.

Definition s2val (u : sig2 P Q) := let: exist2 _ _ x _ _ := u in x.

Lemma s2valP u : P (s2val u). Proof. by case: u. Qed.

Lemma s2valP' u : Q (s2val u). Proof. by case: u. Qed.

End Sig.

Prenex Implicits svalP s2val s2valP s2valP'.

Coercion tag_of_sig I P (u : @sig I P) := Tagged P (svalP u).

Coercion sig_of_sig2 I P Q (u : @sig2 I P Q) :=
  exist (fun i => P i /\ Q i) (s2val u) (conj (s2valP u) (s2valP' u)).

Lemma all_sig I T P :
    (forall x : I, {y : T x | P x y}) ->
  {f : forall x, T x | forall x, P x (f x)}.
Proof. by case/all_tag=> f; exists f. Qed.

Lemma all_sig2 I T P Q :
    (forall x : I, {y : T x | P x y & Q x y}) ->
  {f : forall x, T x | forall x, P x (f x) & forall x, Q x (f x)}.
Proof. by case/all_sig=> f /all_pair[]; exists f. Qed.

Section Morphism.

Variables (aT rT sT : Type) (f : aT -> rT).

(**  Morphism property for unary and binary functions  **)
Definition morphism_1 aF rF := forall x, f (aF x) = rF (f x).
Definition morphism_2 aOp rOp := forall x y, f (aOp x y) = rOp (f x) (f y).

(**  Homomorphism property for unary and binary relations  **)
Definition homomorphism_1 (aP rP : _ -> Prop) := forall x, aP x -> rP (f x).
Definition homomorphism_2 (aR rR : _ -> _ -> Prop) :=
  forall x y, aR x y -> rR (f x) (f y).

(**  Stability property for unary and binary relations  **)
Definition monomorphism_1 (aP rP : _ -> sT) := forall x, rP (f x) = aP x.
Definition monomorphism_2 (aR rR : _ -> _ -> sT) :=
  forall x y, rR (f x) (f y) = aR x y.

End Morphism.

Notation "{ 'morph' f : x / a >-> r }" :=
  (morphism_1 f (fun x => a) (fun x => r))
  (at level 0, f at level 99, x ident,
   format "{ 'morph'  f  :  x  /  a  >->  r }") : type_scope.

Notation "{ 'morph' f : x / a }" :=
  (morphism_1 f (fun x => a) (fun x => a))
  (at level 0, f at level 99, x ident,
   format "{ 'morph'  f  :  x  /  a }") : type_scope.

Notation "{ 'morph' f : x y / a >-> r }" :=
  (morphism_2 f (fun x y => a) (fun x y => r))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'morph'  f  :  x  y  /  a  >->  r }") : type_scope.

Notation "{ 'morph' f : x y / a }" :=
  (morphism_2 f (fun x y => a) (fun x y => a))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'morph'  f  :  x  y  /  a }") : type_scope.

Notation "{ 'homo' f : x / a >-> r }" :=
  (homomorphism_1 f (fun x => a) (fun x => r))
  (at level 0, f at level 99, x ident,
   format "{ 'homo'  f  :  x  /  a  >->  r }") : type_scope.

Notation "{ 'homo' f : x / a }" :=
  (homomorphism_1 f (fun x => a) (fun x => a))
  (at level 0, f at level 99, x ident,
   format "{ 'homo'  f  :  x  /  a }") : type_scope.

Notation "{ 'homo' f : x y / a >-> r }" :=
  (homomorphism_2 f (fun x y => a) (fun x y => r))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'homo'  f  :  x  y  /  a  >->  r }") : type_scope.

Notation "{ 'homo' f : x y / a }" :=
  (homomorphism_2 f (fun x y => a) (fun x y => a))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'homo'  f  :  x  y  /  a }") : type_scope.

Notation "{ 'homo' f : x y /~ a }" :=
  (homomorphism_2 f (fun y x => a) (fun x y => a))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'homo'  f  :  x  y  /~  a }") : type_scope.

Notation "{ 'mono' f : x / a >-> r }" :=
  (monomorphism_1 f (fun x => a) (fun x => r))
  (at level 0, f at level 99, x ident,
   format "{ 'mono'  f  :  x  /  a  >->  r }") : type_scope.

Notation "{ 'mono' f : x / a }" :=
  (monomorphism_1 f (fun x => a) (fun x => a))
  (at level 0, f at level 99, x ident,
   format "{ 'mono'  f  :  x  /  a }") : type_scope.

Notation "{ 'mono' f : x y / a >-> r }" :=
  (monomorphism_2 f (fun x y => a) (fun x y => r))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'mono'  f  :  x  y  /  a  >->  r }") : type_scope.

Notation "{ 'mono' f : x y / a }" :=
  (monomorphism_2 f (fun x y => a) (fun x y => a))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'mono'  f  :  x  y  /  a }") : type_scope.

Notation "{ 'mono' f : x y /~ a }" :=
  (monomorphism_2 f (fun y x => a) (fun x y => a))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'mono'  f  :  x  y  /~  a }") : type_scope.

(**
 In an intuitionistic setting, we have two degrees of injectivity. The
 weaker one gives only simplification, and the strong one provides a left
 inverse (we show in `fintype' that they coincide for finite types).
 We also define an intermediate version where the left inverse is only a
 partial function.                                                          **)

Section Injections.

(**
 rT must come first so we can use @ to mitigate the Coq 1st order
 unification bug (e..g., Coq can't infer rT from a "cancel" lemma).  **)
Variables (rT aT : Type) (f : aT -> rT).

Definition injective := forall x1 x2, f x1 = f x2 -> x1 = x2.

Definition cancel g := forall x, g (f x) = x.

Definition pcancel g := forall x, g (f x) = Some x.

Definition ocancel (g : aT -> option rT) h := forall x, oapp h x (g x) = x.

Lemma can_pcan g : cancel g -> pcancel (fun y => Some (g y)).
Proof. by move=> fK x; congr (Some _). Qed.

Lemma pcan_inj g : pcancel g -> injective.
Proof. by move=> fK x y /(congr1 g); rewrite !fK => [[]]. Qed.

Lemma can_inj g : cancel g -> injective.
Proof. by move/can_pcan; apply: pcan_inj. Qed.

Lemma canLR g x y : cancel g -> x = f y -> g x = y.
Proof. by move=> fK ->. Qed.

Lemma canRL g x y : cancel g -> f x = y -> x = g y.
Proof. by move=> fK <-. Qed.

End Injections.

Lemma Some_inj {T} : injective (@Some T). Proof. by move=> x y []. Qed.

(**  Force implicits to use as a view.  **)
Prenex Implicits Some_inj.

(**  cancellation lemmas for dependent type casts. **)
Lemma esymK T x y : cancel (@esym T x y) (@esym T y x).
Proof. by case: y /. Qed.

Lemma etrans_id T x y (eqxy : x = y :> T) : etrans (erefl x) eqxy = eqxy.
Proof. by case: y / eqxy. Qed.

Section InjectionsTheory.

Variables (A B C : Type) (f g : B -> A) (h : C -> B).

Lemma inj_id : injective (@id A).
Proof. by []. Qed.

Lemma inj_can_sym f' : cancel f f' -> injective f' -> cancel f' f.
Proof. by move=> fK injf' x; apply: injf'. Qed.

Lemma inj_comp : injective f -> injective h -> injective (f \o h).
Proof. by move=> injf injh x y /injf; apply: injh. Qed.

Lemma can_comp f' h' : cancel f f' -> cancel h h' -> cancel (f \o h) (h' \o f').
Proof. by move=> fK hK x; rewrite /= fK hK. Qed.

Lemma pcan_pcomp f' h' :
  pcancel f f' -> pcancel h h' -> pcancel (f \o h) (pcomp h' f').
Proof. by move=> fK hK x; rewrite /pcomp fK /= hK. Qed.

Lemma eq_inj : injective f -> f =1 g -> injective g.
Proof. by move=> injf eqfg x y; rewrite -2!eqfg; apply: injf. Qed.

Lemma eq_can f' g' : cancel f f' -> f =1 g -> f' =1 g' -> cancel g g'.
Proof. by move=> fK eqfg eqfg' x; rewrite -eqfg -eqfg'. Qed.

Lemma inj_can_eq f' : cancel f f' -> injective f' -> cancel g f' -> f =1 g.
Proof. by move=> fK injf' gK x; apply: injf'; rewrite fK. Qed.

End InjectionsTheory.

Section Bijections.

Variables (A B : Type) (f : B -> A).

Variant bijective : Prop := Bijective g of cancel f g & cancel g f.

Hypothesis bijf : bijective.

Lemma bij_inj : injective f.
Proof. by case: bijf => g fK _; apply: can_inj fK. Qed.

Lemma bij_can_sym f' : cancel f' f <-> cancel f f'.
Proof.
split=> fK; first exact: inj_can_sym fK bij_inj.
by case: bijf => h _ hK x; rewrite -[x]hK fK.
Qed.

Lemma bij_can_eq f' f'' : cancel f f' -> cancel f f'' -> f' =1 f''.
Proof.
by move=> fK fK'; apply: (inj_can_eq _ bij_inj); apply/bij_can_sym.
Qed.

End Bijections.

Section BijectionsTheory.

Variables (A B C : Type) (f : B -> A) (h : C -> B).

Lemma eq_bij : bijective f -> forall g, f =1 g -> bijective g.
Proof. by case=> f' fK f'K g eqfg; exists f'; eapply eq_can; eauto. Qed.

Lemma bij_comp : bijective f -> bijective h -> bijective (f \o h).
Proof.
by move=> [f' fK f'K] [h' hK h'K]; exists (h' \o f'); apply: can_comp; auto.
Qed.

Lemma bij_can_bij : bijective f -> forall f', cancel f f' -> bijective f'.
Proof. by move=> bijf; exists f; first by apply/(bij_can_sym bijf). Qed.

End BijectionsTheory.

Section Involutions.

Variables (A : Type) (f : A -> A).

Definition involutive := cancel f f.

Hypothesis Hf : involutive.

Lemma inv_inj : injective f. Proof. exact: can_inj Hf. Qed.
Lemma inv_bij : bijective f. Proof. by exists f. Qed.

End Involutions.

Section OperationProperties.

Variables S T R : Type.

Section SopTisR.
Implicit Type op :  S -> T -> R.
Definition left_inverse e inv op := forall x, op (inv x) x = e.
Definition right_inverse e inv op := forall x, op x (inv x) = e.
Definition left_injective op := forall x, injective (op^~ x).
Definition right_injective op := forall y, injective (op y).
End SopTisR.


Section SopTisS.
Implicit Type op :  S -> T -> S.
Definition right_id e op := forall x, op x e = x.
Definition left_zero z op := forall x, op z x = z.
Definition right_commutative op := forall x y z, op (op x y) z = op (op x z) y.
Definition left_distributive op add :=
  forall x y z, op (add x y) z = add (op x z) (op y z).
Definition right_loop inv op := forall y, cancel (op^~ y) (op^~ (inv y)).
Definition rev_right_loop inv op := forall y, cancel (op^~ (inv y)) (op^~ y).
End SopTisS.

Section SopTisT.
Implicit Type op :  S -> T -> T.
Definition left_id e op := forall x, op e x = x.
Definition right_zero z op := forall x, op x z = z.
Definition left_commutative op := forall x y z, op x (op y z) = op y (op x z).
Definition right_distributive op add :=
  forall x y z, op x (add y z) = add (op x y) (op x z).
Definition left_loop inv op := forall x, cancel (op x) (op (inv x)).
Definition rev_left_loop inv op := forall x, cancel (op (inv x)) (op x).
End SopTisT.

Section SopSisT.
Implicit Type op :  S -> S -> T.
Definition self_inverse e op := forall x, op x x = e.
Definition commutative op := forall x y, op x y = op y x.
End SopSisT.

Section SopSisS.
Implicit Type op :  S -> S -> S.
Definition idempotent op := forall x, op x x = x.
Definition associative op := forall x y z, op x (op y z) = op (op x y) z.
Definition interchange op1 op2 :=
  forall x y z t, op1 (op2 x y) (op2 z t) = op2 (op1 x z) (op1 y t).
End SopSisS.

End OperationProperties.










