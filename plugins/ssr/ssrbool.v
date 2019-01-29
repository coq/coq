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

Require Bool.
Require Import ssreflect ssrfun.

(**
 A theory of boolean predicates and operators. A large part of this file is
 concerned with boolean reflection.
 Definitions and notations:
               is_true b == the coercion of b : bool to Prop (:= b = true).
                            This is just input and displayed as `b''.
             reflect P b == the reflection inductive predicate, asserting
                            that the logical proposition P : prop with the
                            formula b : bool. Lemmas asserting reflect P b
                            are often referred to as "views".
  iffP, appP, sameP, rwP :: lemmas for direct manipulation of reflection
                            views: iffP is used to prove reflection from
                            logical equivalence, appP to compose views, and
                            sameP and rwP to perform boolean and setoid
                            rewriting.
                   elimT :: coercion reflect >-> Funclass, which allows the
                            direct application of `reflect' views to
                            boolean assertions.
             decidable P <-> P is effectively decidable (:= {P} + {~ P}.
    contra, contraL, ... :: contraposition lemmas.
           altP my_viewP :: natural alternative for reflection; given
                            lemma myviewP: reflect my_Prop my_formula,
                              have #[#myP | not_myP#]# := altP my_viewP.
                            generates two subgoals, in which my_formula has
                            been replaced by true and false, resp., with
                            new assumptions myP : my_Prop and
                            not_myP: ~~ my_formula.
                            Caveat: my_formula must be an APPLICATION, not
                            a variable, constant, let-in, etc. (due to the
                            poor behaviour of dependent index matching).
        boolP my_formula :: boolean disjunction, equivalent to
                            altP (idP my_formula) but circumventing the
                            dependent index capture issue; destructing
                            boolP my_formula generates two subgoals with
                            assumptions my_formula and ~~ myformula. As
                            with altP, my_formula must be an application.
            \unless C, P <-> we can assume property P when a something that
                            holds under condition C (such as C itself).
                         := forall G : Prop, (C -> G) -> (P -> G) -> G.
                            This is just C \/ P or rather its impredicative
                            encoding, whose usage better fits the above
                            description: given a lemma UCP whose conclusion
                            is \unless C, P we can assume P by writing:
                              wlog hP: / P by apply/UCP; (prove C -> goal).
                           or even apply: UCP id _ => hP if the goal is C.
           classically P <-> we can assume P when proving is_true b.
                         := forall b : bool, (P -> b) -> b.
                            This is equivalent to ~ (~ P) when P : Prop.
             implies P Q == wrapper variant type that coerces to P -> Q and
                            can be used as a P -> Q view unambiguously.
                            Useful to avoid spurious insertion of <-> views
                            when Q is a conjunction of foralls, as in Lemma
                            all_and2 below; conversely, avoids confusion in
                            apply views for impredicative properties, such
                            as \unless C, P. Also supports contrapositives.
                  a && b == the boolean conjunction of a and b.
                  a || b == the boolean disjunction of a and b.
                 a ==> b == the boolean implication of b by a.
                    ~~ a == the boolean negation of a.
                 a (+) b == the boolean exclusive or (or sum) of a and b.
     #[# /\ P1 , P2 & P3 #]# == multiway logical conjunction, up to 5 terms.
     #[# \/ P1 , P2 | P3 #]# == multiway logical disjunction, up to 4 terms.
        #[#&& a, b, c & d#]# == iterated, right associative boolean conjunction
                            with arbitrary arity.
        #[#|| a, b, c | d#]# == iterated, right associative boolean disjunction
                            with arbitrary arity.
      #[#==> a, b, c => d#]# == iterated, right associative boolean implication
                            with arbitrary arity.
              and3P, ... == specific reflection lemmas for iterated
                            connectives.
       andTb, orbAC, ... == systematic names for boolean connective
                            properties (see suffix conventions below).
              prop_congr == a tactic to move a boolean equality from
                            its coerced form in Prop to the equality
                            in bool.
              bool_congr == resolution tactic for blindly weeding out
                            like terms from boolean equalities (can fail).
 This file provides a theory of boolean predicates and relations:
                  pred T == the type of bool predicates (:= T -> bool).
            simpl_pred T == the type of simplifying bool predicates, based on
                            the simpl_fun type from ssrfun.v.
              mem_pred T == a specialized form of simpl_pred for "collective"
                            predicates (see below).
                   rel T == the type of bool relations.
                         := T -> pred T or T -> T -> bool.
             simpl_rel T == type of simplifying relations.
                         := T -> simpl_pred T
                predType == the generic predicate interface, supported for
                            for lists and sets.
               pred_sort == the predType >-> Type projection; pred_sort is
                            itself a Coercion target class. Declaring a
                            coercion to pred_sort is an alternative way of
                            equiping a type with a predType structure, which
                            interoperates better with coercion subtyping.
                            This is used, e.g., for finite sets, so that finite
                            groups inherit the membership operation by
                            coercing to sets.
                {pred T} == a type convertible to pred T, but whose head
                            constant is pred_sort. This type should be used
                            for parameters that can be used as collective
                            predicates (see below), as this will allow passing
                            in directly collections that implement predType
                            by coercion as described above, e.g., finite sets.
                         := pred_sort (predPredType T)
 If P is a predicate the proposition "x satisfies P" can be written
 applicatively as (P x), or using an explicit connective as (x \in P); in
 the latter case we say that P is a "collective" predicate. We use A, B
 rather than P, Q for collective predicates:
                 x \in A == x satisfies the (collective) predicate A.
              x \notin A == x doesn't satisfy the (collective) predicate A.
 The pred T type can be used as a generic predicate type for either kind,
 but the two kinds of predicates should not be confused. When a "generic"
 pred T value of one type needs to be passed as the other the following
 conversions should be used explicitly:
             SimplPred P == a (simplifying) applicative equivalent of P.
                   mem A == an applicative equivalent of collective predicate A:
                            mem A x simplifies to x \in A, as mem A has in
                            fact type mem_pred T.
 --> In user notation collective predicates _only_ occur as arguments to mem:
     A only appears as (mem A). This is hidden by notation, e.g.,
     x \in A := in_mem x (mem A) here, enum A := enum_mem (mem A) in fintype.
     This makes it possible to unify the various ways in which A can be
     interpreted as a predicate, for both pattern matching and display.
 Alternatively one can use the syntax for explicit simplifying predicates
 and relations (in the following x is bound in E):
            #[#pred x | E#]# == simplifying (see ssrfun) predicate x => E.
        #[#pred x : T | E#]# == predicate x => E, with a cast on the argument.
          #[#pred : T | P#]# == constant predicate P on type T.
      #[#pred x | E1 & E2#]# == #[#pred x | E1 && E2#]#; an x : T cast is allowed.
           #[#pred x in A#]# == #[#pred x | x in A#]#.
       #[#pred x in A | E#]# == #[#pred x | x in A & E#]#.
 #[#pred x in A | E1 & E2#]# == #[#pred x in A | E1 && E2#]#.
           #[#predU A & B#]# == union of two collective predicates A and B.
           #[#predI A & B#]# == intersection of collective predicates A and B.
           #[#predD A & B#]# == difference of collective predicates A and B.
               #[#predC A#]# == complement of the collective predicate A.
          #[#preim f of A#]# == preimage under f of the collective predicate A.
   predU P Q, ..., preim f P == union, etc of applicative predicates.
                       pred0 == the empty predicate.
                       predT == the total (always true) predicate.
                                if T : predArgType, then T coerces to predT.
                       {: T} == T cast to predArgType (e.g., {: bool * nat}).
 In the following, x and y are bound in E:
           #[#rel x y | E#]# == simplifying relation x, y => E.
       #[#rel x y : T | E#]# == simplifying relation with arguments cast.
  #[#rel x y in A & B | E#]# == #[#rel x y | #[#&& x \in A, y \in B & E#]# #]#.
      #[#rel x y in A & B#]# == #[#rel x y | (x \in A) && (y \in B) #]#.
      #[#rel x y in A | E#]# == #[#rel x y in A & A | E#]#.
          #[#rel x y in A#]# == #[#rel x y in A & A#]#.
                    relU R S == union of relations R and S.
                  relpre f R == preimage of relation R under f.
        xpredU, ..., xrelpre == lambda terms implementing predU, ..., etc.
 Explicit values of type pred T (i.e., lamdba terms) should always be used
 applicatively, while values of collection types implementing the predType
 interface, such as sequences or sets should always be used as collective
 predicates. Defined constants and functions of type pred T or simpl_pred T
 as well as the explicit simpl_pred T values described below, can generally
 be used either way. Note however that x \in A will not auto-simplify when
 A is an explicit simpl_pred T value; the generic simplification rule inE
 must be used (when A : pred T, the unfold_in rule can be used). Constants
 of type pred T with an explicit simpl_pred value do not auto-simplify when
 used applicatively, but can still be expanded with inE. This behavior can
 be controlled as follows:
   Let A : collective_pred T := #[#pred x | ... #]#.
     The collective_pred T type is just an alias for pred T, but this cast
     stops rewrite inE from expanding the definition of A, thus treating A
     into an abstract collection (unfold_in or in_collective can be used to
     expand manually).
   Let A : applicative_pred T := #[#pred x | ... #]#.
     This cast causes inE to turn x \in A into the applicative A x form;
     A will then have to unfolded explicitly with the /A rule. This will
     also apply to any definition that reduces to A (e.g., Let B := A).
   Canonical A_app_pred := ApplicativePred A.
     This declaration, given after definition of A, similarly causes inE to
     turn x \in A into A x, but in addition allows the app_predE rule to
     turn A x back into x \in A; it can be used for any definition of type
     pred T, which makes it especially useful for ambivalent predicates
     as the relational transitive closure connect, that are used in both
     applicative and collective styles.
 Purely for aesthetics, we provide a subtype of collective predicates:
   qualifier q T == a pred T pretty-printing wrapper. An A : qualifier q T
                    coerces to pred_sort and thus behaves as a collective
                    predicate, but x \in A and x \notin A are displayed as:
             x \is A and x \isn't A when q = 0,
         x \is a A and x \isn't a A when q = 1,
       x \is an A and x \isn't an A when q = 2, respectively.
   #[#qualify x | P#]# := Qualifier 0 (fun x => P), constructor for the above.
 #[#qualify x : T | P#]#, #[#qualify a x | P#]#, #[#qualify an X | P#]#, etc.
                  variants of the above with type constraints and different
                  values of q.
 We provide an internal interface to support attaching properties (such as
 being multiplicative) to predicates:
    pred_key p == phantom type that will serve as a support for properties
                  to be attached to p : {pred _}; instances should be
                  created with Fact/Qed so as to be opaque.
 KeyedPred k_p == an instance of the interface structure that attaches
                  (k_p : pred_key P) to P; the structure projection is a
                  coercion to pred_sort.
 KeyedQualifier k_q == an instance of the interface structure that attaches
                  (k_q : pred_key q) to (q : qualifier n T).
 DefaultPredKey p == a default value for pred_key p; the vernacular command
                  Import DefaultKeying attaches this key to all predicates
                  that are not explicitly keyed.
 Keys can be used to attach properties to predicates, qualifiers and
 generic nouns in a way that allows them to be used transparently. The key
 projection of a predicate property structure such as unsignedPred should
 be a pred_key, not a pred, and corresponding lemmas will have the form
    Lemma rpredN R S (oppS : @opprPred R S) (kS : keyed_pred oppS) :
       {mono -%%R: x / x \in kS}.
 Because x \in kS will be displayed as x \in S (or x \is S, etc), the
 canonical instance of opprPred will not normally be exposed (it will also
 be erased by /= simplification). In addition each predicate structure
 should have a DefaultPredKey Canonical instance that simply issues the
 property as a proof obligation (which can be caught by the Prop-irrelevant
 feature of the ssreflect plugin).
   Some properties of predicates and relations:
                  A =i B <-> A and B are extensionally equivalent.
         {subset A <= B} <-> A is a (collective) subpredicate of B.
             subpred P Q <-> P is an (applicative) subpredicate or Q.
              subrel R S <-> R is a subrelation of S.
 In the following R is in rel T:
             reflexive R <-> R is reflexive.
           irreflexive R <-> R is irreflexive.
             symmetric R <-> R (in rel T) is symmetric (equation).
         pre_symmetric R <-> R is symmetric (implication).
         antisymmetric R <-> R is antisymmetric.
                 total R <-> R is total.
            transitive R <-> R is transitive.
       left_transitive R <-> R is a congruence on its left hand side.
      right_transitive R <-> R is a congruence on its right hand side.
       equivalence_rel R <-> R is an equivalence relation.
 Localization of (Prop) predicates; if P1 is convertible to forall x, Qx,
 P2 to forall x y, Qxy and P3 to forall x y z, Qxyz :
            {for y, P1} <-> Qx{y / x}.
             {in A, P1} <-> forall x, x \in A -> Qx.
       {in A1 & A2, P2} <-> forall x y, x \in A1 -> y \in A2 -> Qxy.
           {in A &, P2} <-> forall x y, x \in A -> y \in A -> Qxy.
  {in A1 & A2 & A3, Q3} <-> forall x y z,
                            x \in A1 -> y \in A2 -> z \in A3 -> Qxyz.
     {in A1 & A2 &, Q3} := {in A1 & A2 & A2, Q3}.
      {in A1 && A3, Q3} := {in A1 & A1 & A3, Q3}.
          {in A &&, Q3} := {in A & A & A, Q3}.
    {in A, bijective f} <-> f has a right inverse in A.
             {on C, P1} <-> forall x, (f x) \in C -> Qx
                           when P1 is also convertible to Pf f, e.g.,
                           {on C, involutive f}.
           {on C &, P2} == forall x y, f x \in C -> f y \in C -> Qxy
                           when P2 is also convertible to Pf f, e.g.,
                           {on C &, injective f}.
        {on C, P1' & g} == forall x, (f x) \in cd -> Qx
                           when P1' is convertible to Pf f
                           and P1' g is convertible to forall x, Qx, e.g.,
                           {on C, cancel f & g}.
    {on C, bijective f} == f has a right inverse on C.
 This file extends the lemma name suffix conventions of ssrfun as follows:
   A -- associativity, as in andbA : associative andb.
  AC -- right commutativity.
 ACA -- self-interchange (inner commutativity), e.g.,
        orbACA : (a || b) || (c || d) = (a || c) || (b || d).
   b -- a boolean argument, as in andbb : idempotent andb.
   C -- commutativity, as in andbC : commutative andb,
        or predicate complement, as in predC.
  CA -- left commutativity.
   D -- predicate difference, as in predD.
   E -- elimination, as in negbFE : ~~ b = false -> b.
   F or f -- boolean false, as in andbF : b && false = false.
   I -- left/right injectivity, as in addbI : right_injective addb,
        or predicate intersection, as in predI.
   l -- a left-hand operation, as andb_orl : left_distributive andb orb.
   N or n -- boolean negation, as in andbN : a && (~~ a) = false.
   P -- a characteristic property, often a reflection lemma, as in
        andP : reflect (a /\ b) (a && b).
   r -- a right-hand operation, as orb_andr : rightt_distributive orb andb.
   T or t -- boolean truth, as in andbT: right_id true andb.
   U -- predicate union, as in predU.
   W -- weakening, as in in1W : {in D, forall x, P} -> forall x, P.          **)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Warnings "-projection-no-head-constant".

Notation reflect := Bool.reflect.
Notation ReflectT := Bool.ReflectT.
Notation ReflectF := Bool.ReflectF.

Reserved Notation "~~ b" (at level 35, right associativity).
Reserved Notation "b ==> c" (at level 55, right associativity).
Reserved Notation "b1 (+) b2" (at level 50, left associativity).

Reserved Notation "x \in A" (at level 70, no associativity,
  format "'[hv' x '/ '  \in  A ']'").
Reserved Notation "x \notin A" (at level 70, no associativity,
  format "'[hv' x '/ '  \notin  A ']'").
Reserved Notation "x \is A" (at level 70, no associativity,
  format "'[hv' x '/ '  \is  A ']'").
Reserved Notation "x \isn't A" (at level 70, no associativity,
  format "'[hv' x '/ '  \isn't  A ']'").
Reserved Notation "x \is 'a' A" (at level 70, no associativity,
  format "'[hv' x '/ '  \is  'a'  A ']'").
Reserved Notation "x \isn't 'a' A" (at level 70, no associativity,
  format "'[hv' x '/ '  \isn't  'a'  A ']'").
Reserved Notation "x \is 'an' A" (at level 70, no associativity,
  format "'[hv' x '/ '  \is  'an'  A ']'").
Reserved Notation "x \isn't 'an' A" (at level 70, no associativity,
  format "'[hv' x '/ '  \isn't  'an'  A ']'").
Reserved Notation "p1 =i p2" (at level 70, no associativity,
  format "'[hv' p1 '/ '  =i  p2 ']'").
Reserved Notation "{ 'subset' A <= B }" (at level 0, A, B at level 69,
  format "'[hv' { 'subset'  A '/    '  <=  B } ']'").

Reserved Notation "{ : T }" (at level 0, format "{ :  T }").
Reserved Notation "{ 'pred' T }" (at level 0, format "{ 'pred'  T }").
Reserved Notation "[ 'predType' 'of' T ]" (at level 0,
  format "[ 'predType'  'of'  T ]").

Reserved Notation "[ 'pred' : T | E ]" (at level 0,
  format "'[hv' [ 'pred' :  T  | '/ '  E ] ']'").
Reserved Notation "[ 'pred' x | E ]" (at level 0, x ident,
  format "'[hv' [ 'pred'  x  | '/ '  E ] ']'").
Reserved Notation "[ 'pred' x : T | E ]" (at level 0, x ident,
  format "'[hv' [ 'pred'  x  :  T  | '/ '  E ] ']'").
Reserved Notation "[ 'pred' x | E1 & E2 ]" (at level 0, x ident,
  format "'[hv' [ 'pred'  x  | '/ '  E1  & '/ '  E2 ] ']'").
Reserved Notation "[ 'pred' x : T | E1 & E2 ]" (at level 0, x ident,
  format "'[hv' [ 'pred'  x  :  T  | '/ '  E1  &  E2 ] ']'").
Reserved Notation "[ 'pred' x 'in' A ]" (at level 0, x ident,
  format "'[hv' [ 'pred'  x  'in'  A ] ']'").
Reserved Notation "[ 'pred' x 'in' A | E ]" (at level 0, x ident,
  format "'[hv' [ 'pred'  x  'in'  A  | '/ '  E ] ']'").
Reserved Notation "[ 'pred' x 'in' A | E1 & E2 ]" (at level 0, x ident,
  format "'[hv' [ 'pred'  x  'in'  A  | '/ '  E1  & '/ '  E2 ] ']'").

Reserved Notation "[ 'qualify' x | P ]" (at level 0, x at level 99,
  format "'[hv' [  'qualify'  x  | '/ '  P ] ']'").
Reserved Notation "[ 'qualify' x : T | P ]" (at level 0, x at level 99,
  format "'[hv' [  'qualify'  x  :  T  | '/ '  P ] ']'").
Reserved Notation "[ 'qualify' 'a' x | P ]" (at level 0, x at level 99,
  format "'[hv' [ 'qualify'  'a'  x  | '/ '  P ] ']'").
Reserved Notation "[ 'qualify' 'a' x : T | P ]" (at level 0, x at level 99,
  format "'[hv' [ 'qualify'  'a'  x  :  T  | '/ '  P ] ']'").
Reserved Notation "[ 'qualify' 'an' x | P ]" (at level 0, x at level 99,
  format "'[hv' [ 'qualify'  'an'  x  | '/ '  P ] ']'").
Reserved Notation "[ 'qualify' 'an' x : T | P ]" (at level 0, x at level 99,
  format "'[hv' [ 'qualify'  'an'  x  :  T  | '/ '  P ] ']'").

Reserved Notation "[ 'rel' x y | E ]"  (at level 0, x ident, y ident,
  format "'[hv' [ 'rel'  x  y  | '/ '  E ] ']'").
Reserved Notation "[ 'rel' x y : T | E ]" (at level 0, x ident, y ident,
  format "'[hv' [ 'rel'  x  y  :  T  | '/ '  E ] ']'").
Reserved Notation "[ 'rel' x y 'in' A & B | E ]" (at level 0, x ident, y ident,
  format "'[hv' [ 'rel'  x  y  'in'  A  &  B  | '/ '  E ] ']'").
Reserved Notation "[ 'rel' x y 'in' A & B ]" (at level 0, x ident, y ident,
  format "'[hv' [ 'rel'  x  y  'in'  A  &  B ] ']'").
Reserved Notation "[ 'rel' x y 'in' A | E ]" (at level 0, x ident, y ident,
  format "'[hv' [ 'rel'  x  y  'in'  A  | '/ '  E ] ']'").
Reserved Notation "[ 'rel' x y 'in' A ]" (at level 0, x ident, y ident,
  format "'[hv' [ 'rel'  x  y  'in'  A ] ']'").

Reserved Notation "[ 'mem' A ]" (at level 0, format "[ 'mem'  A ]").
Reserved Notation "[ 'predI' A & B ]" (at level 0,
  format "[ 'predI'  A  &  B ]").
Reserved Notation "[ 'predU' A & B ]" (at level 0,
  format "[ 'predU'  A  &  B ]").
Reserved Notation "[ 'predD' A & B ]" (at level 0,
  format "[ 'predD'  A  &  B ]").
Reserved Notation "[ 'predC' A ]" (at level 0,
  format "[ 'predC'  A ]").
Reserved Notation "[ 'preim' f 'of' A ]" (at level 0,
  format "[ 'preim'  f  'of'  A ]").

Reserved Notation "\unless C , P" (at level 200, C at level 100,
  format "'[hv' \unless  C , '/ '  P ']'").

Reserved Notation "{ 'for' x , P }" (at level 0,
  format "'[hv' { 'for'  x , '/ '  P } ']'").
Reserved Notation "{ 'in' d , P }" (at level 0,
  format "'[hv' { 'in'  d , '/ '  P } ']'").
Reserved Notation "{ 'in' d1 & d2 , P }" (at level 0,
  format "'[hv' { 'in'  d1  &  d2 , '/ '  P } ']'").
Reserved Notation "{ 'in' d & , P }" (at level 0,
  format "'[hv' { 'in'  d  & , '/ '  P } ']'").
Reserved Notation "{ 'in' d1 & d2 & d3 , P }" (at level 0,
  format "'[hv' { 'in'  d1  &  d2  &  d3 , '/ '  P } ']'").
Reserved Notation "{ 'in' d1 & & d3 , P }" (at level 0,
  format "'[hv' { 'in'  d1  &  &  d3 , '/ '  P } ']'").
Reserved Notation "{ 'in' d1 & d2 & , P }" (at level 0,
  format "'[hv' { 'in'  d1  &  d2  & , '/ '  P } ']'").
Reserved Notation "{ 'in' d & & , P }" (at level 0,
  format "'[hv' { 'in'  d  &  & , '/ '  P } ']'").
Reserved Notation "{ 'on' cd , P }" (at level 0,
  format "'[hv' { 'on'  cd , '/ '  P } ']'").
Reserved Notation "{ 'on' cd & , P }" (at level 0,
  format "'[hv' { 'on'  cd  & , '/ '  P } ']'").
Reserved Notation "{ 'on' cd , P & g }" (at level 0, g at level 8,
  format "'[hv' { 'on'  cd , '/ '  P  &  g } ']'").
Reserved Notation "{ 'in' d , 'bijective' f }" (at level 0, f at level 8,
   format "'[hv' { 'in'  d , '/ '  'bijective'  f } ']'").
Reserved Notation "{ 'on' cd , 'bijective' f }" (at level 0, f at level 8,
   format "'[hv' { 'on'  cd , '/ '  'bijective'  f } ']'").


(**
 We introduce a number of n-ary "list-style" notations that share a common
 format, namely
    #[#op arg1, arg2, ... last_separator last_arg#]#
 This usually denotes a right-associative applications of op, e.g.,
  #[#&& a, b, c & d#]# denotes a && (b && (c && d))
 The last_separator must be a non-operator token. Here we use &, | or =>;
 our default is &, but we try to match the intended meaning of op. The
 separator is a workaround for limitations of the parsing engine; the same
 limitations mean the separator cannot be omitted even when last_arg can.
   The Notation declarations are complicated by the separate treatment for
 some fixed arities (binary for bool operators, and all arities for Prop
 operators).
   We also use the square brackets in comprehension-style notations
    #[#type var separator expr#]#
 where "type" is the type of the comprehension (e.g., pred) and "separator"
 is | or => . It is important that in other notations a leading square
 bracket #[# is always followed by an operator symbol or a fixed identifier.   **)

Reserved Notation "[ /\ P1 & P2 ]" (at level 0, only parsing).
Reserved Notation "[ /\ P1 , P2 & P3 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 ']' '/ '  &  P3 ] ']'").
Reserved Notation "[ /\ P1 , P2 , P3 & P4 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 ']' '/ '  &  P4 ] ']'").
Reserved Notation "[ /\ P1 , P2 , P3 , P4 & P5 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 ']' '/ '  &  P5 ] ']'").

Reserved Notation "[ \/ P1 | P2 ]" (at level 0, only parsing).
Reserved Notation "[ \/ P1 , P2 | P3 ]" (at level 0, format
  "'[hv' [ \/ '['  P1 , '/'  P2 ']' '/ '  |  P3 ] ']'").
Reserved Notation "[ \/ P1 , P2 , P3 | P4 ]" (at level 0, format
  "'[hv' [ \/ '['  P1 , '/'  P2 , '/'  P3 ']' '/ '  |  P4 ] ']'").

Reserved Notation "[ && b1 & c ]" (at level 0, only parsing).
Reserved Notation "[ && b1 , b2 , .. , bn & c ]" (at level 0, format
  "'[hv' [ && '['  b1 , '/'  b2 , '/'  .. , '/'  bn ']' '/ '  &  c ] ']'").

Reserved Notation "[ || b1 | c ]" (at level 0, only parsing).
Reserved Notation "[ || b1 , b2 , .. , bn | c ]" (at level 0, format
  "'[hv' [ || '['  b1 , '/'  b2 , '/'  .. , '/'  bn ']' '/ '  |  c ] ']'").

Reserved Notation "[ ==> b1 => c ]" (at level 0, only parsing).
Reserved Notation "[ ==> b1 , b2 , .. , bn => c ]" (at level 0, format
  "'[hv' [ ==> '['  b1 , '/'  b2 , '/'  .. , '/'  bn ']' '/'  =>  c ] ']'").

(**  Shorter delimiter  **)
Delimit Scope bool_scope with B.
Open Scope bool_scope.

(**  An alternative to xorb that behaves somewhat better wrt simplification. **)
Definition addb b := if b then negb else id.

(**  Notation for && and || is declared in Init.Datatypes.  **)
Notation "~~ b" := (negb b) : bool_scope.
Notation "b ==> c" := (implb b c) : bool_scope.
Notation "b1 (+) b2" := (addb b1 b2) : bool_scope.

(**  Constant is_true b := b = true is defined in Init.Datatypes.  **)
Coercion is_true : bool >-> Sortclass. (* Prop *)

Lemma prop_congr : forall b b' : bool, b = b' -> b = b' :> Prop.
Proof. by move=> b b' ->. Qed.

Ltac prop_congr := apply: prop_congr.

(**  Lemmas for trivial.  **)
Lemma is_true_true : true.               Proof. by []. Qed.
Lemma not_false_is_true : ~ false.       Proof. by []. Qed.
Lemma is_true_locked_true : locked true. Proof. by unlock. Qed.
Hint Resolve is_true_true not_false_is_true is_true_locked_true : core.

(**  Shorter names.  **)
Definition isT := is_true_true.
Definition notF := not_false_is_true.

(**  Negation lemmas.  **)

(**
 We generally take NEGATION as the standard form of a false condition:
 negative boolean hypotheses should be of the form ~~ b, rather than ~ b or
 b = false, as much as possible.                                             **)

Lemma negbT b : b = false -> ~~ b.          Proof. by case: b. Qed.
Lemma negbTE b : ~~ b -> b = false.         Proof. by case: b. Qed.
Lemma negbF b : (b : bool) -> ~~ b = false. Proof. by case: b. Qed.
Lemma negbFE b : ~~ b = false -> b.         Proof. by case: b. Qed.
Lemma negbK : involutive negb.              Proof. by case. Qed.
Lemma negbNE b : ~~ ~~ b -> b.              Proof. by case: b. Qed.

Lemma negb_inj : injective negb. Proof. exact: can_inj negbK. Qed.
Lemma negbLR b c : b = ~~ c -> ~~ b = c. Proof. exact: canLR negbK. Qed.
Lemma negbRL b c : ~~ b = c -> b = ~~ c. Proof. exact: canRL negbK. Qed.

Lemma contra (c b : bool) : (c -> b) -> ~~ b -> ~~ c.
Proof. by case: b => //; case: c. Qed.
Definition contraNN := contra.

Lemma contraL (c b : bool) : (c -> ~~ b) -> b -> ~~ c.
Proof. by case: b => //; case: c. Qed.
Definition contraTN := contraL.

Lemma contraR (c b : bool) : (~~ c -> b) -> ~~ b -> c.
Proof. by case: b => //; case: c. Qed.
Definition contraNT := contraR.

Lemma contraLR (c b : bool) : (~~ c -> ~~ b) -> b -> c.
Proof. by case: b => //; case: c. Qed.
Definition contraTT := contraLR.

Lemma contraT b : (~~ b -> false) -> b. Proof. by case: b => // ->. Qed.

Lemma wlog_neg b : (~~ b -> b) -> b. Proof. by case: b => // ->. Qed.

Lemma contraFT (c b : bool) : (~~ c -> b) -> b = false -> c.
Proof. by move/contraR=> notb_c /negbT. Qed.

Lemma contraFN (c b : bool) : (c -> b) -> b = false -> ~~ c.
Proof. by move/contra=> notb_notc /negbT. Qed.

Lemma contraTF (c b : bool) : (c -> ~~ b) -> b -> c = false.
Proof. by move/contraL=> b_notc /b_notc/negbTE. Qed.

Lemma contraNF (c b : bool) : (c -> b) -> ~~ b -> c = false.
Proof. by move/contra=> notb_notc /notb_notc/negbTE. Qed.

Lemma contraFF (c b : bool) : (c -> b) -> b = false -> c = false.
Proof. by move/contraFN=> bF_notc /bF_notc/negbTE. Qed.

(**
 Coercion of sum-style datatypes into bool, which makes it possible
 to use ssr's boolean if rather than Coq's "generic" if.             **)

Coercion isSome T (u : option T) := if u is Some _ then true else false.

Coercion is_inl A B (u : A + B) := if u is inl _ then true else false.

Coercion is_left A B (u : {A} + {B}) := if u is left _ then true else false.

Coercion is_inleft A B (u : A + {B}) := if u is inleft _ then true else false.

Prenex Implicits  isSome is_inl is_left is_inleft.

Definition decidable P := {P} + {~ P}.

(**
 Lemmas for ifs with large conditions, which allow reasoning about the
 condition without repeating it inside the proof (the latter IS
 preferable when the condition is short).
 Usage :
   if the goal contains (if cond then ...) = ...
     case: ifP => Hcond.
   generates two subgoal, with the assumption Hcond : cond = true/false
     Rewrite if_same  eliminates redundant ifs
     Rewrite (fun_if f) moves a function f inside an if
     Rewrite if_arg moves an argument inside a function-valued if        **)

Section BoolIf.

Variables (A B : Type) (x : A) (f : A -> B) (b : bool) (vT vF : A).

Variant if_spec (not_b : Prop) : bool -> A -> Set :=
  | IfSpecTrue  of      b : if_spec not_b true vT
  | IfSpecFalse of  not_b : if_spec not_b false vF.

Lemma ifP : if_spec (b = false) b (if b then vT else vF).
Proof. by case def_b: b; constructor. Qed.

Lemma ifPn : if_spec (~~ b) b (if b then vT else vF).
Proof. by case def_b: b; constructor; rewrite ?def_b. Qed.

Lemma ifT : b -> (if b then vT else vF) = vT. Proof. by move->. Qed.
Lemma ifF : b = false -> (if b then vT else vF) = vF. Proof. by move->. Qed.
Lemma ifN : ~~ b -> (if b then vT else vF) = vF. Proof. by move/negbTE->. Qed.

Lemma if_same : (if b then vT else vT) = vT.
Proof. by case b. Qed.

Lemma if_neg : (if ~~ b then vT else vF) = if b then vF else vT.
Proof. by case b. Qed.

Lemma fun_if : f (if b then vT else vF) = if b then f vT else f vF.
Proof. by case b. Qed.

Lemma if_arg (fT fF : A -> B) :
  (if b then fT else fF) x = if b then fT x else fF x.
Proof. by case b. Qed.

(**  Turning a boolean "if" form into an application.  **)
Definition if_expr := if b then vT else vF.
Lemma ifE : (if b then vT else vF) = if_expr. Proof. by []. Qed.

End BoolIf.

(**  Core (internal) reflection lemmas, used for the three kinds of views.  **)

Section ReflectCore.

Variables (P Q : Prop) (b c : bool).

Hypothesis Hb : reflect P b.

Lemma introNTF : (if c then ~ P else P) -> ~~ b = c.
Proof. by case c; case Hb. Qed.

Lemma introTF : (if c then P else ~ P) -> b = c.
Proof. by case c; case Hb. Qed.

Lemma elimNTF : ~~ b = c -> if c then ~ P else P.
Proof. by move <-; case Hb. Qed.

Lemma elimTF : b = c -> if c then P else ~ P.
Proof. by move <-; case Hb. Qed.

Lemma equivPif : (Q -> P) -> (P -> Q) -> if b then Q else ~ Q.
Proof. by case Hb; auto. Qed.

Lemma xorPif : Q \/ P -> ~ (Q /\ P) -> if b then ~ Q else Q.
Proof. by case Hb => [? _ H ? | ? H _]; case: H. Qed.

End ReflectCore.

(**  Internal negated reflection lemmas  **)
Section ReflectNegCore.

Variables (P Q : Prop) (b c : bool).
Hypothesis Hb : reflect P (~~ b).

Lemma introTFn : (if c then ~ P else P) -> b = c.
Proof. by move/(introNTF Hb) <-; case b. Qed.

Lemma elimTFn : b = c -> if c then ~ P else P.
Proof. by move <-; apply: (elimNTF Hb); case b. Qed.

Lemma equivPifn : (Q -> P) -> (P -> Q) -> if b then ~ Q else Q.
Proof. by rewrite -if_neg; apply: equivPif. Qed.

Lemma xorPifn : Q \/ P -> ~ (Q /\ P) -> if b then Q else ~ Q.
Proof. by rewrite -if_neg; apply: xorPif. Qed.

End ReflectNegCore.

(**  User-oriented reflection lemmas  **)
Section Reflect.

Variables (P Q : Prop) (b b' c : bool).
Hypotheses (Pb : reflect P b) (Pb' : reflect P (~~ b')).

Lemma introT  : P -> b.            Proof. exact: introTF true _. Qed.
Lemma introF  : ~ P -> b = false.  Proof. exact: introTF false _. Qed.
Lemma introN  : ~ P -> ~~ b.       Proof. exact: introNTF true _. Qed.
Lemma introNf : P -> ~~ b = false. Proof. exact: introNTF false _. Qed.
Lemma introTn : ~ P -> b'.         Proof. exact: introTFn true _. Qed.
Lemma introFn : P -> b' = false.   Proof. exact: introTFn false _. Qed.

Lemma elimT  : b -> P.             Proof. exact: elimTF true _. Qed.
Lemma elimF  : b = false -> ~ P.   Proof. exact: elimTF false _. Qed.
Lemma elimN  : ~~ b -> ~P.         Proof. exact: elimNTF true _. Qed.
Lemma elimNf : ~~ b = false -> P.  Proof. exact: elimNTF false _. Qed.
Lemma elimTn : b' -> ~ P.          Proof. exact: elimTFn true _. Qed.
Lemma elimFn : b' = false -> P.    Proof. exact: elimTFn false _. Qed.

Lemma introP : (b -> Q) -> (~~ b -> ~ Q) -> reflect Q b.
Proof. by case b; constructor; auto. Qed.

Lemma iffP : (P -> Q) -> (Q -> P) -> reflect Q b.
Proof. by case: Pb; constructor; auto. Qed.

Lemma equivP : (P <-> Q) -> reflect Q b.
Proof. by case; apply: iffP. Qed.

Lemma sumboolP (decQ : decidable Q) : reflect Q decQ.
Proof. by case: decQ; constructor. Qed.

Lemma appP : reflect Q b -> P -> Q.
Proof. by move=> Qb; move/introT; case: Qb. Qed.

Lemma sameP : reflect P c -> b = c.
Proof. by case; [apply: introT | apply: introF]. Qed.

Lemma decPcases : if b then P else ~ P. Proof. by case Pb. Qed.

Definition decP : decidable P. by case: b decPcases; [left | right]. Defined.

Lemma rwP : P <-> b. Proof. by split; [apply: introT | apply: elimT]. Qed.

Lemma rwP2 : reflect Q b -> (P <-> Q).
Proof. by move=> Qb; split=> ?; [apply: appP | apply: elimT; case: Qb]. Qed.

(**   Predicate family to reflect excluded middle in bool.  **)
Variant alt_spec : bool -> Type :=
  | AltTrue of     P : alt_spec true
  | AltFalse of ~~ b : alt_spec false.

Lemma altP : alt_spec b.
Proof. by case def_b: b / Pb; constructor; rewrite ?def_b. Qed.

End Reflect.

Hint View for move/ elimTF|3 elimNTF|3 elimTFn|3 introT|2 introTn|2 introN|2.

Hint View for apply/ introTF|3 introNTF|3 introTFn|3 elimT|2 elimTn|2 elimN|2.

Hint View for apply// equivPif|3 xorPif|3 equivPifn|3 xorPifn|3.

(**  Allow the direct application of a reflection lemma to a boolean assertion.  **)
Coercion elimT : reflect >-> Funclass.

#[universes(template)]
Variant implies P Q := Implies of P -> Q.
Lemma impliesP P Q : implies P Q -> P -> Q. Proof. by case. Qed.
Lemma impliesPn (P Q : Prop) : implies P Q -> ~ Q -> ~ P.
Proof. by case=> iP ? /iP. Qed.
Coercion impliesP : implies >-> Funclass.
Hint View for move/ impliesPn|2 impliesP|2.
Hint View for apply/ impliesPn|2 impliesP|2.

(**  Impredicative or, which can emulate a classical not-implies.  **)
Definition unless condition property : Prop :=
 forall goal : Prop, (condition -> goal) -> (property -> goal) -> goal.

Notation "\unless C , P" := (unless C P) : type_scope.

Lemma unlessL C P : implies C (\unless C, P).
Proof. by split=> hC G /(_ hC). Qed.

Lemma unlessR C P : implies P (\unless C, P).
Proof. by split=> hP G _ /(_ hP). Qed.

Lemma unless_sym C P : implies (\unless C, P) (\unless P, C).
Proof. by split; apply; [apply/unlessR | apply/unlessL]. Qed.

Lemma unlessP (C P : Prop) : (\unless C, P) <-> C \/ P.
Proof. by split=> [|[/unlessL | /unlessR]]; apply; [left | right]. Qed.

Lemma bind_unless C P {Q} : implies (\unless C, P) (\unless (\unless C, Q), P).
Proof. by split; apply=> [hC|hP]; [apply/unlessL/unlessL | apply/unlessR]. Qed.

Lemma unless_contra b C : implies (~~ b -> C) (\unless C, b).
Proof. by split; case: b => [_ | hC]; [apply/unlessR | apply/unlessL/hC]. Qed.

(**
 Classical reasoning becomes directly accessible for any bool subgoal.
 Note that we cannot use "unless" here for lack of universe polymorphism.    **)
Definition classically P : Prop := forall b : bool, (P -> b) -> b.

Lemma classicP (P : Prop) : classically P <-> ~ ~ P.
Proof.
split=> [cP nP | nnP [] // nP]; last by case nnP; move/nP.
by have: P -> false; [move/nP | move/cP].
Qed.

Lemma classicW P : P -> classically P. Proof. by move=> hP _ ->. Qed.

Lemma classic_bind P Q : (P -> classically Q) -> classically P -> classically Q.
Proof. by move=> iPQ cP b /iPQ-/cP. Qed.

Lemma classic_EM P : classically (decidable P).
Proof.
by case=> // undecP; apply/undecP; right=> notP; apply/notF/undecP; left.
Qed.

Lemma classic_pick T P : classically ({x : T | P x} + (forall x, ~ P x)).
Proof.
case=> // undecP; apply/undecP; right=> x Px.
by apply/notF/undecP; left; exists x.
Qed.

Lemma classic_imply P Q : (P -> classically Q) -> classically (P -> Q).
Proof.
move=> iPQ []// notPQ; apply/notPQ=> /iPQ-cQ.
by case: notF; apply: cQ => hQ; apply: notPQ.
Qed.

(**
 List notations for wider connectives; the Prop connectives have a fixed
 width so as to avoid iterated destruction (we go up to width 5 for /\, and
 width 4 for or). The bool connectives have arbitrary widths, but denote
 expressions that associate to the RIGHT. This is consistent with the right
 associativity of list expressions and thus more convenient in most proofs.  **)

Inductive and3 (P1 P2 P3 : Prop) : Prop := And3 of P1 & P2 & P3.

Inductive and4 (P1 P2 P3 P4 : Prop) : Prop := And4 of P1 & P2 & P3 & P4.

Inductive and5 (P1 P2 P3 P4 P5 : Prop) : Prop :=
  And5 of P1 & P2 & P3 & P4 & P5.

Inductive or3 (P1 P2 P3 : Prop) : Prop := Or31 of P1 | Or32 of P2 | Or33 of P3.

Inductive or4 (P1 P2 P3 P4 : Prop) : Prop :=
  Or41 of P1 | Or42 of P2 | Or43 of P3 | Or44 of P4.

Notation "[ /\ P1 & P2 ]" := (and P1 P2) (only parsing) : type_scope.
Notation "[ /\ P1 , P2 & P3 ]" := (and3 P1 P2 P3) : type_scope.
Notation "[ /\ P1 , P2 , P3 & P4 ]" := (and4 P1 P2 P3 P4) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 & P5 ]" := (and5 P1 P2 P3 P4 P5) : type_scope.

Notation "[ \/ P1 | P2 ]" := (or P1 P2) (only parsing) : type_scope.
Notation "[ \/ P1 , P2 | P3 ]" := (or3 P1 P2 P3) : type_scope.
Notation "[ \/ P1 , P2 , P3 | P4 ]" := (or4 P1 P2 P3 P4) : type_scope.

Notation "[ && b1 & c ]" := (b1 && c) (only parsing) : bool_scope.
Notation "[ && b1 , b2 , .. , bn & c ]" := (b1 && (b2 && .. (bn && c) .. ))
  : bool_scope.

Notation "[ || b1 | c ]" := (b1 || c) (only parsing) : bool_scope.
Notation "[ || b1 , b2 , .. , bn | c ]" := (b1 || (b2 || .. (bn || c) .. ))
  : bool_scope.

Notation "[ ==> b1 , b2 , .. , bn => c ]" :=
   (b1 ==> (b2 ==> .. (bn ==> c) .. )) : bool_scope.
Notation "[ ==> b1 => c ]" := (b1 ==> c) (only parsing) : bool_scope.

Section AllAnd.

Variables (T : Type) (P1 P2 P3 P4 P5 : T -> Prop).
Local Notation a P := (forall x, P x).

Lemma all_and2 : implies (forall x, [/\ P1 x & P2 x]) [/\ a P1 & a P2].
Proof. by split=> haveP; split=> x; case: (haveP x). Qed.

Lemma all_and3 : implies (forall x, [/\ P1 x, P2 x & P3 x])
                         [/\ a P1, a P2 & a P3].
Proof. by split=> haveP; split=> x; case: (haveP x). Qed.

Lemma all_and4 : implies (forall x, [/\ P1 x, P2 x, P3 x & P4 x])
                         [/\ a P1, a P2, a P3 & a P4].
Proof. by split=> haveP; split=> x; case: (haveP x). Qed.

Lemma all_and5 : implies (forall x, [/\ P1 x, P2 x, P3 x, P4 x & P5 x])
                         [/\ a P1, a P2, a P3, a P4 & a P5].
Proof. by split=> haveP; split=> x; case: (haveP x). Qed.

End AllAnd.

Arguments all_and2 {T P1 P2}.
Arguments all_and3 {T P1 P2 P3}.
Arguments all_and4 {T P1 P2 P3 P4}.
Arguments all_and5 {T P1 P2 P3 P4 P5}.

Lemma pair_andP P Q : P /\ Q <-> P * Q. Proof. by split; case. Qed.

Section ReflectConnectives.

Variable b1 b2 b3 b4 b5 : bool.

Lemma idP : reflect b1 b1.
Proof. by case b1; constructor. Qed.

Lemma boolP : alt_spec b1 b1 b1.
Proof. exact: (altP idP). Qed.

Lemma idPn : reflect (~~ b1) (~~ b1).
Proof. by case b1; constructor. Qed.

Lemma negP : reflect (~ b1) (~~ b1).
Proof. by case b1; constructor; auto. Qed.

Lemma negPn : reflect b1 (~~ ~~ b1).
Proof. by case b1; constructor. Qed.

Lemma negPf : reflect (b1 = false) (~~ b1).
Proof. by case b1; constructor. Qed.

Lemma andP : reflect (b1 /\ b2) (b1 && b2).
Proof. by case b1; case b2; constructor=> //; case. Qed.

Lemma and3P : reflect [/\ b1, b2 & b3] [&& b1, b2 & b3].
Proof. by case b1; case b2; case b3; constructor; try by case. Qed.

Lemma and4P : reflect [/\ b1, b2, b3 & b4] [&& b1, b2, b3 & b4].
Proof. by case b1; case b2; case b3; case b4; constructor; try by case. Qed.

Lemma and5P : reflect [/\ b1, b2, b3, b4 & b5] [&& b1, b2, b3, b4 & b5].
Proof.
by case b1; case b2; case b3; case b4; case b5; constructor; try by case.
Qed.

Lemma orP : reflect (b1 \/ b2) (b1 || b2).
Proof. by case b1; case b2; constructor; auto; case. Qed.

Lemma or3P : reflect [\/ b1, b2 | b3] [|| b1, b2 | b3].
Proof.
case b1; first by constructor; constructor 1.
case b2; first by constructor; constructor 2.
case b3; first by constructor; constructor 3.
by constructor; case.
Qed.

Lemma or4P : reflect [\/ b1, b2, b3 | b4] [|| b1, b2, b3 | b4].
Proof.
case b1; first by constructor; constructor 1.
case b2; first by constructor; constructor 2.
case b3; first by constructor; constructor 3.
case b4; first by constructor; constructor 4.
by constructor; case.
Qed.

Lemma nandP : reflect (~~ b1 \/ ~~ b2) (~~ (b1 && b2)).
Proof. by case b1; case b2; constructor; auto; case; auto. Qed.

Lemma norP : reflect (~~ b1 /\ ~~ b2) (~~ (b1 || b2)).
Proof. by case b1; case b2; constructor; auto; case; auto. Qed.

Lemma implyP : reflect (b1 -> b2) (b1 ==> b2).
Proof. by case b1; case b2; constructor; auto. Qed.

End ReflectConnectives.

Arguments idP {b1}.
Arguments idPn {b1}.
Arguments negP {b1}.
Arguments negPn {b1}.
Arguments negPf {b1}.
Arguments andP {b1 b2}.
Arguments and3P {b1 b2 b3}.
Arguments and4P {b1 b2 b3 b4}.
Arguments and5P {b1 b2 b3 b4 b5}.
Arguments orP {b1 b2}.
Arguments or3P {b1 b2 b3}.
Arguments or4P {b1 b2 b3 b4}.
Arguments nandP {b1 b2}.
Arguments norP {b1 b2}.
Arguments implyP {b1 b2}.
Prenex Implicits idP idPn negP negPn negPf.
Prenex Implicits andP and3P and4P and5P orP or3P or4P nandP norP implyP.

(**  Shorter, more systematic names for the boolean connectives laws.        **)

Lemma andTb : left_id true andb.       Proof. by []. Qed.
Lemma andFb : left_zero false andb.    Proof. by []. Qed.
Lemma andbT : right_id true andb.      Proof. by case. Qed.
Lemma andbF : right_zero false andb.   Proof. by case. Qed.
Lemma andbb : idempotent andb.         Proof. by case. Qed.
Lemma andbC : commutative andb.        Proof. by do 2!case. Qed.
Lemma andbA : associative andb.        Proof. by do 3!case. Qed.
Lemma andbCA : left_commutative andb.  Proof. by do 3!case. Qed.
Lemma andbAC : right_commutative andb. Proof. by do 3!case. Qed.
Lemma andbACA : interchange andb andb. Proof. by do 4!case. Qed.

Lemma orTb : forall b, true || b.      Proof. by []. Qed.
Lemma orFb : left_id false orb.        Proof. by []. Qed.
Lemma orbT : forall b, b || true.      Proof. by case. Qed.
Lemma orbF : right_id false orb.       Proof. by case. Qed.
Lemma orbb : idempotent orb.           Proof. by case. Qed.
Lemma orbC : commutative orb.          Proof. by do 2!case. Qed.
Lemma orbA : associative orb.          Proof. by do 3!case. Qed.
Lemma orbCA : left_commutative orb.    Proof. by do 3!case. Qed.
Lemma orbAC : right_commutative orb.   Proof. by do 3!case. Qed.
Lemma orbACA : interchange orb orb.    Proof. by do 4!case. Qed.

Lemma andbN b : b && ~~ b = false. Proof. by case: b. Qed.
Lemma andNb b : ~~ b && b = false. Proof. by case: b. Qed.
Lemma orbN b : b || ~~ b = true.   Proof. by case: b. Qed.
Lemma orNb b : ~~ b || b = true.   Proof. by case: b. Qed.

Lemma andb_orl : left_distributive andb orb.  Proof. by do 3!case. Qed.
Lemma andb_orr : right_distributive andb orb. Proof. by do 3!case. Qed.
Lemma orb_andl : left_distributive orb andb.  Proof. by do 3!case. Qed.
Lemma orb_andr : right_distributive orb andb. Proof. by do 3!case. Qed.

Lemma andb_idl (a b : bool) : (b -> a) -> a && b = b.
Proof. by case: a; case: b => // ->. Qed.
Lemma andb_idr (a b : bool) : (a -> b) -> a && b = a.
Proof. by case: a; case: b => // ->. Qed.
Lemma andb_id2l (a b c : bool) : (a -> b = c) -> a && b = a && c.
Proof. by case: a; case: b; case: c => // ->. Qed.
Lemma andb_id2r (a b c : bool) : (b -> a = c) -> a && b = c && b.
Proof. by case: a; case: b; case: c => // ->. Qed.

Lemma orb_idl (a b : bool) : (a -> b) -> a || b = b.
Proof. by case: a; case: b => // ->. Qed.
Lemma orb_idr (a b : bool) : (b -> a) -> a || b = a.
Proof. by case: a; case: b => // ->. Qed.
Lemma orb_id2l (a b c : bool) : (~~ a -> b = c) -> a || b = a || c.
Proof. by case: a; case: b; case: c => // ->. Qed.
Lemma orb_id2r (a b c : bool) : (~~ b -> a = c) -> a || b = c || b.
Proof. by case: a; case: b; case: c => // ->. Qed.

Lemma negb_and (a b : bool) : ~~ (a && b) = ~~ a || ~~ b.
Proof. by case: a; case: b. Qed.

Lemma negb_or (a b : bool) : ~~ (a || b) = ~~ a && ~~ b.
Proof. by case: a; case: b. Qed.

(**  Pseudo-cancellation -- i.e, absorption  **)

Lemma andbK a b : a && b || a = a.  Proof. by case: a; case: b. Qed.
Lemma andKb a b : a || b && a = a.  Proof. by case: a; case: b. Qed.
Lemma orbK a b : (a || b) && a = a. Proof. by case: a; case: b. Qed.
Lemma orKb a b : a && (b || a) = a. Proof. by case: a; case: b. Qed.

(**  Imply  **)

Lemma implybT b : b ==> true.           Proof. by case: b. Qed.
Lemma implybF b : (b ==> false) = ~~ b. Proof. by case: b. Qed.
Lemma implyFb b : false ==> b.          Proof. by []. Qed.
Lemma implyTb b : (true ==> b) = b.     Proof. by []. Qed.
Lemma implybb b : b ==> b.              Proof. by case: b. Qed.

Lemma negb_imply a b : ~~ (a ==> b) = a && ~~ b.
Proof. by case: a; case: b. Qed.

Lemma implybE a b : (a ==> b) = ~~ a || b.
Proof. by case: a; case: b. Qed.

Lemma implyNb a b : (~~ a ==> b) = a || b.
Proof. by case: a; case: b. Qed.

Lemma implybN a b : (a ==> ~~ b) = (b ==> ~~ a).
Proof. by case: a; case: b. Qed.

Lemma implybNN a b : (~~ a ==> ~~ b) = b ==> a.
Proof. by case: a; case: b. Qed.

Lemma implyb_idl (a b : bool) : (~~ a -> b) -> (a ==> b) = b.
Proof. by case: a; case: b => // ->. Qed.
Lemma implyb_idr (a b : bool) : (b -> ~~ a) -> (a ==> b) = ~~ a.
Proof. by case: a; case: b => // ->. Qed.
Lemma implyb_id2l (a b c : bool) : (a -> b = c) -> (a ==> b) = (a ==> c).
Proof. by case: a; case: b; case: c => // ->. Qed.

(**  Addition (xor)  **)

Lemma addFb : left_id false addb.               Proof. by []. Qed.
Lemma addbF : right_id false addb.              Proof. by case. Qed.
Lemma addbb : self_inverse false addb.          Proof. by case. Qed.
Lemma addbC : commutative addb.                 Proof. by do 2!case. Qed.
Lemma addbA : associative addb.                 Proof. by do 3!case. Qed.
Lemma addbCA : left_commutative addb.           Proof. by do 3!case. Qed.
Lemma addbAC : right_commutative addb.          Proof. by do 3!case. Qed.
Lemma addbACA : interchange addb addb.          Proof. by do 4!case. Qed.
Lemma andb_addl : left_distributive andb addb.  Proof. by do 3!case. Qed.
Lemma andb_addr : right_distributive andb addb. Proof. by do 3!case. Qed.
Lemma addKb : left_loop id addb.                Proof. by do 2!case. Qed.
Lemma addbK : right_loop id addb.               Proof. by do 2!case. Qed.
Lemma addIb : left_injective addb.              Proof. by do 3!case. Qed.
Lemma addbI : right_injective addb.             Proof. by do 3!case. Qed.

Lemma addTb b : true (+) b = ~~ b. Proof. by []. Qed.
Lemma addbT b : b (+) true = ~~ b. Proof. by case: b. Qed.

Lemma addbN a b : a (+) ~~ b = ~~ (a (+) b).
Proof. by case: a; case: b. Qed.
Lemma addNb a b : ~~ a (+) b = ~~ (a (+) b).
Proof. by case: a; case: b. Qed.

Lemma addbP a b : reflect (~~ a = b) (a (+) b).
Proof. by case: a; case: b; constructor. Qed.
Arguments addbP {a b}.

(**
 Resolution tactic for blindly weeding out common terms from boolean
 equalities. When faced with a goal of the form (andb/orb/addb b1 b2) = b3
 they will try to locate b1 in b3 and remove it. This can fail!             **)

Ltac bool_congr :=
  match goal with
  | |- (?X1 && ?X2 = ?X3) => first
  [ symmetry; rewrite -1?(andbC X1) -?(andbCA X1); congr 1 (andb X1); symmetry
  | case: (X1); [ rewrite ?andTb ?andbT // | by rewrite ?andbF /= ] ]
  | |- (?X1 || ?X2 = ?X3) => first
  [ symmetry; rewrite -1?(orbC X1) -?(orbCA X1); congr 1 (orb X1); symmetry
  | case: (X1); [ by rewrite ?orbT //= | rewrite ?orFb ?orbF ] ]
  | |- (?X1 (+) ?X2 = ?X3) =>
    symmetry; rewrite -1?(addbC X1) -?(addbCA X1); congr 1 (addb X1); symmetry
  | |- (~~ ?X1 = ?X2) => congr 1 negb
  end.


(**
 Predicates, i.e., packaged functions to bool.
 - pred T, the basic type for predicates over a type T, is simply an alias
 for T -> bool.
 We actually distinguish two kinds of predicates, which we call applicative
 and collective, based on the syntax used to test them at some x in T:
 - For an applicative predicate P, one uses prefix syntax:
     P x
   Also, most operations on applicative predicates use prefix syntax as
   well (e.g., predI P Q).
 - For a collective predicate A, one uses infix syntax:
     x \in A
   and all operations on collective predicates use infix syntax as well
   (e.g., #[#predI A & B#]#).
 There are only two kinds of applicative predicates:
 - pred T, the alias for T -> bool mentioned above
 - simpl_pred T, an alias for simpl_fun T bool with a coercion to pred T
   that auto-simplifies on application (see ssrfun).
 On the other hand, the set of collective predicate types is open-ended via
 - predType T, a Structure that can be used to put Canonical collective
   predicate interpretation on other types, such as lists, tuples,
   finite sets, etc.
 Indeed, we define such interpretations for applicative predicate types,
 which can therefore also be used with the infix syntax, e.g.,
     x \in predI P Q
 Moreover these infix forms are convertible to their prefix counterpart
 (e.g., predI P Q x which in turn simplifies to P x && Q x). The converse
 is not true, however; collective predicate types cannot, in general, be
 used applicatively, because of restrictions on implicit coercions.
   However, we do define an explicit generic coercion
 - mem : forall (pT : predType), pT -> mem_pred T
   where mem_pred T is a variant of simpl_pred T that preserves the infix
   syntax, i.e., mem A x auto-simplifies to x \in A.
 Indeed, the infix "collective" operators are notation for a prefix
 operator with arguments of type mem_pred T or pred T, applied to coerced
 collective predicates, e.g.,
      Notation "x \in A" := (in_mem x (mem A)).
 This prevents the variability in the predicate type from interfering with
 the application of generic lemmas. Moreover this also makes it much easier
 to define generic lemmas, because the simplest type -- pred T -- can be
 used as the type of generic collective predicates, provided one takes care
 not to use it applicatively; this avoids the burden of having to declare a
 different predicate type for each predicate parameter of each section or
 lemma.
   In detail, we ensure that the head normal form of mem A is always of the
 eta-long MemPred (fun x => pA x) form, where pA is the pred interpretation of
 A following its predType pT, i.e., the _expansion_ of topred A. For a pred T
 evar ?P, (mem ?P) converts MemPred (fun x => ?P x), whose argument is a Miller
 pattern and therefore always unify: unifying (mem A) with (mem ?P) always
 yields ?P = pA, because the rigid constant MemPred aligns the unification.
 Furthermore, we ensure pA is always either A or toP .... A where toP ... is
 the expansion of @topred T pT, and toP is declared as a Coercion, so pA will
 _display_ as A in either case, and the instances of @mem T (predPredType T) pA
 appearing in the premises or right-hand side of a generic lemma parametrized
 by ?P will be indistinguishable from @mem T pT A.
   Users should take care not to inadvertently "strip" (mem A) down to the
 coerced A, since this will expose the internal toP coercion: Coq could then
 display terms A x that cannot be typed as such. The topredE lemma can be used
 to restore the x \in A syntax in this case. While -topredE can conversely be
 used to change x \in P into P x for an applicative P, it is safer to use the
 inE, unfold_in or and memE lemmas instead, as they do not run the risk of
 exposing internal coercions. As a consequence it is better to explicitly
 cast a generic applicative predicate to simpl_pred using the SimplPred
 constructor when it is used as a collective predicate (see, e.g.,
 Lemma eq_big in bigop).
   We also sometimes "instantiate" the predType structure by defining a
 coercion to the sort of the predPredType structure, conveniently denoted
 {pred T}. This works better for types such as {set T} that have subtypes that
 coerce to them, since the same coercion will be inserted by the application
 of mem, or of any lemma that expects a generic collective predicates with
 type {pred T} := pred_sort (predPredType T) = pred T; thus {pred T} should be
 the preferred type for generic collective predicate parameters.
   This device also lets us turn any Type aT : predArgType into the total
 predicate over that type, i.e., fun _: aT => true. This allows us to write,
 e.g., ##|'I_n| for the cardinal of the (finite) type of integers less than n.
 **)

(** Boolean predicates. *)

Definition pred T := T -> bool.
Identity Coercion fun_of_pred : pred >-> Funclass.

Definition subpred T (p1 p2 : pred T) := forall x : T, p1 x -> p2 x.

(* Notation for some manifest predicates. *)

Notation xpred0 := (fun=> false).
Notation xpredT := (fun=> true).
Notation xpredI := (fun (p1 p2 : pred _) x => p1 x && p2 x).
Notation xpredU := (fun (p1 p2 : pred _) x => p1 x || p2 x).
Notation xpredC := (fun (p : pred _) x => ~~ p x).
Notation xpredD := (fun (p1 p2 : pred _) x => ~~ p2 x && p1 x).
Notation xpreim := (fun f (p : pred _) x => p (f x)).

(** The packed class interface for pred-like types. **)

#[universes(template)]
Structure predType T :=
   PredType {pred_sort :> Type; topred : pred_sort -> pred T}.

Definition clone_pred T U :=
  fun pT & @pred_sort T pT -> U =>
  fun toP (pT' := @PredType T U toP) & phant_id pT' pT => pT'.
Notation "[ 'predType' 'of' T ]" := (@clone_pred _ T _ id _ id) : form_scope.

Canonical predPredType T := PredType (@id (pred T)).
Canonical boolfunPredType T := PredType (@id (T -> bool)).

(** The type of abstract collective predicates.
 While {pred T} is contertible to pred T, it presents the pred_sort coercion
 class, which crucially does _not_ coerce to Funclass. Term whose type P coerces
 to {pred T} cannot be applied to arguments, but they _can_ be used as if P
 had a canonical predType instance, as the coercion will be inserted if the
 unification P =~= pred_sort ?pT fails, changing the problem into the trivial
 {pred T} =~= pred_sort ?pT (solution ?pT := predPredType P).
   Additional benefits of this approach are that any type coercing to P will
 also inherit this behaviour, and that the coercion will be apparent in the
 elaborated expression. The latter may be important if the coercion is also
 a canonical structure projector - see mathcomp/fingroup/fingroup.v. The
 main drawback of implementing predType by coercion in this way is that the
 type of the value must be known when the unification constraint is imposed:
 if we only register the constraint and then later discover later that the
 expression had type P it will be too late of insert a coercion, whereas a
 canonical instance of predType fo P would have solved the deferred constraint.
   Finally, definitions, lemmas and sections should use type {pred T} for
 their generic collective type parameters, as this will make it possible to
 apply such definitions and lemmas directly to values of types that implement
 predType by coercion to {pred T} (values of types that implement predType
 without coercing to {pred T} will have to be coerced explicitly using topred).
**)
Notation "{ 'pred' T }" := (pred_sort (predPredType T)) : type_scope.

(** The type of self-simplifying collective predicates. **)
Definition simpl_pred T := simpl_fun T bool.
Definition SimplPred {T} (p : pred T) : simpl_pred T := SimplFun p.

(** Some simpl_pred constructors. **)

Definition pred0 {T} := @SimplPred T xpred0.
Definition predT {T} := @SimplPred T xpredT.
Definition predI {T} (p1 p2 : pred T) := SimplPred (xpredI p1 p2).
Definition predU {T} (p1 p2 : pred T) := SimplPred (xpredU p1 p2).
Definition predC {T} (p : pred T) := SimplPred (xpredC p).
Definition predD {T} (p1 p2 : pred T) := SimplPred (xpredD p1 p2).
Definition preim {aT rT} (f : aT -> rT) (d : pred rT) := SimplPred (xpreim f d).

Notation "[ 'pred' : T | E ]" := (SimplPred (fun _ : T => E%B)) : fun_scope.
Notation "[ 'pred' x | E ]" := (SimplPred (fun x => E%B)) : fun_scope.
Notation "[ 'pred' x | E1 & E2 ]" := [pred x | E1 && E2 ] : fun_scope.
Notation "[ 'pred' x : T | E ]" :=
  (SimplPred (fun x : T => E%B)) (only parsing) : fun_scope.
Notation "[ 'pred' x : T | E1 & E2 ]" :=
  [pred x : T | E1 && E2 ] (only parsing) : fun_scope.

(** Coercions for simpl_pred.
   As simpl_pred T values are used both applicatively and collectively we
 need simpl_pred to coerce to both pred T _and_ {pred T}. However it is
 undesirable to have two distinct constants for what are essentially identical
 coercion functions, as this confuses the SSReflect keyed matching algorithm.
 While the Coq Coercion declarations appear to disallow such Coercion aliasing,
 it is possible to work around this limitation with a combination of modules
 and functors, which we do below.
   In addition we also give a predType instance for simpl_pred, which will
 be preferred to the {pred T} coercion to solve simpl_pred T =~= pred_sort ?pT
 constraints; not however that the pred_of_simpl coercion _will_ be used
 when a simpl_pred T is passed as a {pred T}, since the simplPredType T
 structure for simpl_pred T is _not_ convertible to predPredType T.  **)

Module PredOfSimpl.
Definition coerce T (sp : simpl_pred T) : pred T := fun_of_simpl sp.
End PredOfSimpl.
Notation pred_of_simpl := PredOfSimpl.coerce.
Coercion pred_of_simpl : simpl_pred >-> pred.
Canonical simplPredType T := PredType (@pred_of_simpl T).

Module Type PredSortOfSimplSignature.
Parameter coerce : forall T, simpl_pred T -> {pred T}.
End PredSortOfSimplSignature.
Module DeclarePredSortOfSimpl (PredSortOfSimpl : PredSortOfSimplSignature).
Coercion PredSortOfSimpl.coerce : simpl_pred >-> pred_sort.
End DeclarePredSortOfSimpl.
Module Export PredSortOfSimplCoercion := DeclarePredSortOfSimpl PredOfSimpl.

(** Type to pred coercion.
   This lets us use types of sort predArgType as a synonym for their universal
 predicate. We define this predicate as a simpl_pred T rather than a pred T or
 a {pred T} so that /= and inE reduce (T x) and x \in T to true, respectively.
   Unfortunately, this can't be used for existing types like bool whose sort
 is already fixed (at least, not without redefining bool, true, false and
 all bool operations and lemmas); we provide syntax to recast a given type
 in predArgType as a workaround. **)
Definition predArgType := Type.
Bind Scope type_scope with predArgType.
Identity Coercion sort_of_predArgType : predArgType >-> Sortclass.
Coercion pred_of_argType (T : predArgType) : simpl_pred T := predT.
Notation "{ : T }" := (T%type : predArgType) : type_scope.

(** Boolean relations.
 Simplifying relations follow the coding pattern of 2-argument simplifying
 functions: the simplifying type constructor is applied to the _last_
 argument. This design choice will let the in_simpl componenent of inE expand
 membership in simpl_rel as well. We provide an explicit coercion to rel T
 to avoid eta-expansion during coercion; this coercion self-simplifies so it
 should be invisible.
 **)

Definition rel T := T -> pred T.
Identity Coercion fun_of_rel : rel >-> Funclass.

Definition subrel T (r1 r2 : rel T) := forall x y : T, r1 x y -> r2 x y.

Definition simpl_rel T := T -> simpl_pred T.

Coercion rel_of_simpl T (sr : simpl_rel T) : rel T := fun x : T => sr x.
Arguments rel_of_simpl {T} sr x /.

Notation xrelU := (fun (r1 r2 : rel _) x y => r1 x y || r2 x y).
Notation xrelpre := (fun f (r : rel _) x y => r (f x) (f y)).

Definition SimplRel {T} (r : rel T) : simpl_rel T := fun x => SimplPred (r x).
Definition relU {T} (r1 r2 : rel T) := SimplRel (xrelU r1 r2).
Definition relpre {aT rT} (f : aT -> rT) (r : rel rT) := SimplRel (xrelpre f r).

Notation "[ 'rel' x y | E ]" := (SimplRel (fun x y => E%B)) : fun_scope.
Notation "[ 'rel' x y : T | E ]" :=
  (SimplRel (fun x y : T => E%B)) (only parsing) : fun_scope.

Lemma subrelUl T (r1 r2 : rel T) : subrel r1 (relU r1 r2).
Proof. by move=> x y r1xy; apply/orP; left. Qed.

Lemma subrelUr T (r1 r2 : rel T) : subrel r2 (relU r1 r2).
Proof. by move=> x y r2xy; apply/orP; right. Qed.

(** Variant of simpl_pred specialised to the membership operator. **)

Variant mem_pred T := Mem of pred T.

(**
  We mainly declare pred_of_mem as a coercion so that it is not displayed.
  Similarly to pred_of_simpl, it will usually not be inserted by type
  inference, as all mem_pred mp =~= pred_sort ?pT unification problems will
  be solve by the memPredType instance below; pred_of_mem will however
  be used if a mem_pred T is used as a {pred T}, which is desirable as it
  will avoid a redundant mem in a collective, e.g., passing (mem A) to a lemma
  exception a generic collective predicate p : {pred T} and premise x \in P
  will display a subgoal x \in A rathere than x \in mem A.
    Conversely, pred_of_mem will _not_ if it is used id (mem A) is used
  applicatively or as a pred T; there the simpl_of_mem coercion defined below
  will be used, resulting in a subgoal that displays as mem A x by simplifies
  to x \in A.
 **)
Coercion pred_of_mem {T} mp : {pred T} := let: Mem p := mp in [eta p].
Canonical memPredType T := PredType (@pred_of_mem T).

Definition in_mem {T} (x : T) mp := pred_of_mem mp x.
Definition eq_mem {T} mp1 mp2 := forall x : T, in_mem x mp1 = in_mem x mp2.
Definition sub_mem {T} mp1 mp2 := forall x : T, in_mem x mp1 -> in_mem x mp2.

Arguments in_mem {T} x mp : simpl never.
Typeclasses Opaque eq_mem.
Typeclasses Opaque sub_mem.

(** The [simpl_of_mem; pred_of_simpl] path provides a new mem_pred >-> pred
  coercion, but does _not_ override the pred_of_mem : mem_pred >-> pred_sort
  explicit coercion declaration above.
 **)
Coercion simpl_of_mem {T} mp := SimplPred (fun x : T => in_mem x mp).

Lemma sub_refl T (mp : mem_pred T) : sub_mem mp mp. Proof. by []. Qed.
Arguments sub_refl {T mp} [x] mp_x.

(**
 It is essential to interlock the production of the Mem constructor inside
 the branch of the predType match, to ensure that unifying mem A with
 Mem [eta ?p] sets ?p := toP A (or ?p := P if toP = id and A = [eta P]),
 rather than topred pT A, had we put mem A := Mem (topred A).
**)
Definition mem T (pT : predType T) : pT -> mem_pred T :=
  let: PredType toP := pT in fun A => Mem [eta toP A].
Arguments mem {T pT} A : rename, simpl never.

Notation "x \in A" := (in_mem x (mem A)) : bool_scope.
Notation "x \in A" := (in_mem x (mem A)) : bool_scope.
Notation "x \notin A" := (~~ (x \in A)) : bool_scope.
Notation "A =i B" := (eq_mem (mem A) (mem B)) : type_scope.
Notation "{ 'subset' A <= B }" := (sub_mem (mem A) (mem B)) : type_scope.

Notation "[ 'mem' A ]" :=
  (pred_of_simpl (simpl_of_mem (mem A))) (only parsing) : fun_scope.

Notation "[ 'predI' A & B ]" := (predI [mem A] [mem B]) : fun_scope.
Notation "[ 'predU' A & B ]" := (predU [mem A] [mem B]) : fun_scope.
Notation "[ 'predD' A & B ]" := (predD [mem A] [mem B]) : fun_scope.
Notation "[ 'predC' A ]" := (predC [mem A]) : fun_scope.
Notation "[ 'preim' f 'of' A ]" := (preim f [mem A]) : fun_scope.
Notation "[ 'pred' x 'in' A ]" := [pred x | x \in A] : fun_scope.
Notation "[ 'pred' x 'in' A | E ]" := [pred x | x \in A & E] : fun_scope.
Notation "[ 'pred' x 'in' A | E1 & E2 ]" :=
  [pred x | x \in A & E1 && E2 ] : fun_scope.

Notation "[ 'rel' x y 'in' A & B | E ]" :=
  [rel x y | (x \in A) && (y \in B) && E] : fun_scope.
Notation "[ 'rel' x y 'in' A & B ]" :=
  [rel x y | (x \in A) && (y \in B)] : fun_scope.
Notation "[ 'rel' x y 'in' A | E ]" := [rel x y in A & A | E] : fun_scope.
Notation "[ 'rel' x y 'in' A ]" := [rel x y in A & A] : fun_scope.

(** Aliases of pred T that let us tag instances of simpl_pred as applicative
  or collective, via bespoke coercions. This tagging will give control over
  the simplification behaviour of inE and othe rewriting lemmas below.
    For this control to work it is crucial that collective_of_simpl _not_
  be convertible to either applicative_of_simpl or pred_of_simpl. Indeed
  they differ here by a commutattive conversion (of the match and lambda).
 **)
Definition applicative_pred T := pred T.
Definition collective_pred T := pred T.
Coercion applicative_pred_of_simpl T (sp : simpl_pred T) : applicative_pred T :=
  fun_of_simpl sp.
Coercion collective_pred_of_simpl T (sp : simpl_pred T) : collective_pred T :=
  let: SimplFun p := sp in p.

(** Explicit simplification rules for predicate application and membership. **)
Section PredicateSimplification.

Variables T : Type.

Implicit Types (p : pred T) (pT : predType T) (sp : simpl_pred T).
Implicit Types (mp : mem_pred T).

(**
 The following four bespoke structures provide fine-grained control over
 matching the various predicate forms. While all four follow a common pattern
 of using a canonical projection to match a particular form of predicate
 (in pred T, simpl_pred, mem_pred and mem_pred, respectively), and display
 the matched predicate in the structure type, each is in fact used for a
 different, specific purpose:
  - registered_applicative_pred: this user-facing structure is used to
    declare values of type pred T meant to be used applicatively. The
    structure parameter merely displays this same value, and is used to avoid
    undesirable, visible occurrence of the structure in the right hand side
    of rewrite rules such as app_predE.
      There is a canonical instance of registered_applicative_pred for values
    of the applicative_of_simpl coercion, which handles the
       Definition Apred : applicative_pred T := [pred x | ...] idiom.
    This instance is mainly intended for the in_applicative component of inE,
    in conjunction with manifest_mem_pred and applicative_mem_pred.
  - manifest_simpl_pred: the only instance of this structure matches manifest
    simpl_pred values of the form SimplPred p, displaying p in the structure
    type. This structure is used in in_simpl to detect and selectively expand
    collective predicates of this form. An explicit SimplPred p pattern would
    _NOT_ work for this purpose, as then the left-hand side of in_simpl would
    reduce to in_mem ?x (Mem [eta ?p]) and would thus match _any_ instance
    of \in, not just those arising from a manifest simpl_pred.
  - manifest_mem_pred: similar to manifest_simpl_pred, the one instance of this
    structure matches manifest mem_pred values of the form Mem [eta ?p]. The
    purpose is different however: to match and display in ?p the actual
    predicate appearing in an ... \in ... expression matched by the left hand
    side of the in_applicative component of inE; then
  - applicative_mem_pred is a telescope refinement of manifest_mem_pred p with
    a default constructor that checks that the predicate p is the value of a
    registered_applicative_pred; any unfolding occurring during this check
    does _not_ affect the value of p passed to in_applicative, since that
    has been fixed earlier by the manifest_mem_pred match. In particular the
    definition of a predicate using the applicative_pred_of_simpl idiom above
    will not be expanded - this very case is the reason in_applicative uses
    a mem_pred telescope in its left hand side. The more straightforward
    ?x \in applicative_pred_value ?ap (equivalent to in_mem ?x (Mem ?ap))
    with ?ap : registered_applicative_pred ?p would set ?p := [pred x | ...]
    rather than ?p := Apred in the example above.
 Also note that the in_applicative component of inE must be come before the
 in_simpl one, as the latter also matches terms of the form x \in Apred.
 Finally, no component of inE matches x \in Acoll, when
   Definition Acoll : collective_pred T := [pred x | ...].
 as the collective_pred_of_simpl is _not_ convertible to pred_of_simpl.  **)

Structure registered_applicative_pred p := RegisteredApplicativePred {
  applicative_pred_value :> pred T;
  _ : applicative_pred_value = p
}.
Definition ApplicativePred p := RegisteredApplicativePred (erefl p).
Canonical applicative_pred_applicative sp :=
  ApplicativePred (applicative_pred_of_simpl sp).

Structure manifest_simpl_pred p := ManifestSimplPred {
  simpl_pred_value :> simpl_pred T;
  _ : simpl_pred_value = SimplPred p
}.
Canonical expose_simpl_pred p := ManifestSimplPred (erefl (SimplPred p)).

Structure manifest_mem_pred p := ManifestMemPred {
  mem_pred_value :> mem_pred T;
  _ : mem_pred_value = Mem [eta p]
}.
Canonical expose_mem_pred p := ManifestMemPred (erefl (Mem [eta p])).

Structure applicative_mem_pred p :=
  ApplicativeMemPred {applicative_mem_pred_value :> manifest_mem_pred p}.
Canonical check_applicative_mem_pred p (ap : registered_applicative_pred p) :=
  [eta @ApplicativeMemPred ap].

Lemma mem_topred pT (pp : pT) : mem (topred pp) = mem pp.
Proof. by case: pT pp. Qed.

Lemma topredE pT x (pp : pT) : topred pp x = (x \in pp).
Proof. by rewrite -mem_topred. Qed.

Lemma app_predE x p (ap : registered_applicative_pred p) : ap x = (x \in p).
Proof. by case: ap => _ /= ->. Qed.

Lemma in_applicative x p (amp : applicative_mem_pred p) : in_mem x amp = p x.
Proof. by case: amp => -[_ /= ->]. Qed.

Lemma in_collective x p (msp : manifest_simpl_pred p) :
  (x \in collective_pred_of_simpl msp) = p x.
Proof. by case: msp => _ /= ->. Qed.

Lemma in_simpl x p (msp : manifest_simpl_pred p) :
  in_mem x (Mem [eta pred_of_simpl msp]) = p x.
Proof. by case: msp => _ /= ->. Qed.

(**
 Because of the explicit eta expansion in the left-hand side, this lemma
 should only be used in the left-to-right direction.
 **)
Lemma unfold_in x p : (x \in ([eta p] : pred T)) = p x.
Proof. by []. Qed.

Lemma simpl_predE p : SimplPred p =1 p.
Proof. by []. Qed.

Definition inE := (in_applicative, in_simpl, simpl_predE). (* to be extended *)

Lemma mem_simpl sp : mem sp = sp :> pred T.
Proof. by []. Qed.

Definition memE := mem_simpl. (* could be extended *)

Lemma mem_mem mp :
  (mem mp = mp) * (mem (mp : simpl_pred T) = mp) * (mem (mp : pred T) = mp).
Proof. by case: mp. Qed.

End PredicateSimplification.

(**  Qualifiers and keyed predicates.  **)

Variant qualifier (q : nat) T := Qualifier of {pred T}.

Coercion has_quality n T (q : qualifier n T) : {pred T} :=
  fun x => let: Qualifier _ p := q in p x.
Arguments has_quality n {T}.

Lemma qualifE n T p x : (x \in @Qualifier n T p) = p x. Proof. by []. Qed.

Notation "x \is A" := (x \in has_quality 0 A) : bool_scope.
Notation "x \is 'a' A" := (x \in has_quality 1 A) : bool_scope.
Notation "x \is 'an' A" := (x \in has_quality 2 A) : bool_scope.
Notation "x \isn't A" := (x \notin has_quality 0 A) : bool_scope.
Notation "x \isn't 'a' A" := (x \notin has_quality 1 A) : bool_scope.
Notation "x \isn't 'an' A" := (x \notin has_quality 2 A) : bool_scope.
Notation "[ 'qualify' x | P ]" := (Qualifier 0 (fun x => P%B)) : form_scope.
Notation "[ 'qualify' x : T | P ]" :=
  (Qualifier 0 (fun x : T => P%B)) (only parsing) : form_scope.
Notation "[ 'qualify' 'a' x | P ]" := (Qualifier 1 (fun x => P%B)) : form_scope.
Notation "[ 'qualify' 'a' x : T | P ]" :=
  (Qualifier 1 (fun x : T => P%B)) (only parsing) : form_scope.
Notation "[ 'qualify' 'an' x | P ]" :=
  (Qualifier 2 (fun x => P%B)) : form_scope.
Notation "[ 'qualify' 'an' x : T | P ]" :=
  (Qualifier 2 (fun x : T => P%B)) (only parsing) : form_scope.

(**  Keyed predicates: support for property-bearing predicate interfaces.  **)

Section KeyPred.

Variable T : Type.
#[universes(template)]
Variant pred_key (p : {pred T}) := DefaultPredKey.

Variable p : {pred T}.
Structure keyed_pred (k : pred_key p) :=
  PackKeyedPred {unkey_pred :> {pred T}; _ : unkey_pred =i p}.

Variable k : pred_key p.
Definition KeyedPred := @PackKeyedPred k p (frefl _).

Variable k_p : keyed_pred k.
Lemma keyed_predE : k_p =i p. Proof. by case: k_p. Qed.

(**
 Instances that strip the mem cast; the first one has "pred_of_mem" as its
 projection head value, while the second has "pred_of_simpl". The latter
 has the side benefit of preempting accidental misdeclarations.
 Note: pred_of_mem is the registered mem >-> pred_sort coercion, while
 [simpl_of_mem; pred_of_simpl] is the mem >-> pred >=> Funclass coercion. We
 must write down the coercions explicitly as the Canonical head constant
 computation does not strip casts.                                        **)
Canonical keyed_mem :=
  @PackKeyedPred k (pred_of_mem (mem k_p)) keyed_predE.
Canonical keyed_mem_simpl :=
  @PackKeyedPred k (pred_of_simpl (mem k_p)) keyed_predE.

End KeyPred.

Local Notation in_unkey x S := (x \in @unkey_pred _ S _ _) (only parsing).
Notation "x \in S" := (in_unkey x S) (only printing) : bool_scope.

Section KeyedQualifier.

Variables (T : Type) (n : nat) (q : qualifier n T).

Structure keyed_qualifier (k : pred_key q) :=
  PackKeyedQualifier {unkey_qualifier; _ : unkey_qualifier = q}.
Definition KeyedQualifier k := PackKeyedQualifier k (erefl q).
Variables (k : pred_key q) (k_q : keyed_qualifier k).
Fact keyed_qualifier_suproof : unkey_qualifier k_q =i q.
Proof. by case: k_q => /= _ ->. Qed.
Canonical keyed_qualifier_keyed := PackKeyedPred k keyed_qualifier_suproof.

End KeyedQualifier.

Notation "x \is A" :=
  (in_unkey x (has_quality 0 A)) (only printing) : bool_scope.
Notation "x \is 'a' A" :=
  (in_unkey x (has_quality 1 A)) (only printing) : bool_scope.
Notation "x \is 'an' A" :=
  (in_unkey x (has_quality 2 A)) (only printing) : bool_scope.

Module DefaultKeying.

Canonical default_keyed_pred T p := KeyedPred (@DefaultPredKey T p).
Canonical default_keyed_qualifier T n (q : qualifier n T) :=
  KeyedQualifier (DefaultPredKey q).

End DefaultKeying.

(**  Skolemizing with conditions.  **)

Lemma all_tag_cond_dep I T (C : pred I) U :
    (forall x, T x) -> (forall x, C x -> {y : T x & U x y}) ->
  {f : forall x, T x & forall x, C x -> U x (f x)}.
Proof.
move=> f0 fP; apply: all_tag (fun x y => C x -> U x y) _ => x.
by case Cx: (C x); [case/fP: Cx => y; exists y | exists (f0 x)].
Qed.

Lemma all_tag_cond I T (C : pred I) U :
    T -> (forall x, C x -> {y : T & U x y}) ->
  {f : I -> T & forall x, C x -> U x (f x)}.
Proof. by move=> y0; apply: all_tag_cond_dep. Qed.

Lemma all_sig_cond_dep I T (C : pred I) P :
    (forall x, T x) -> (forall x, C x -> {y : T x | P x y}) ->
  {f : forall x, T x | forall x, C x -> P x (f x)}.
Proof. by move=> f0 /(all_tag_cond_dep f0)[f]; exists f. Qed.

Lemma all_sig_cond I T (C : pred I) P :
    T -> (forall x, C x -> {y : T | P x y}) ->
  {f : I -> T | forall x, C x -> P x (f x)}.
Proof. by move=> y0; apply: all_sig_cond_dep. Qed.

Section RelationProperties.

(**
 Caveat: reflexive should not be used to state lemmas, as auto and trivial
 will not expand the constant.                                               **)

Variable T : Type.

Variable R : rel T.

Definition total := forall x y, R x y || R y x.
Definition transitive := forall y x z, R x y -> R y z -> R x z.

Definition symmetric := forall x y, R x y = R y x.
Definition antisymmetric := forall x y, R x y && R y x -> x = y.
Definition pre_symmetric := forall x y, R x y -> R y x.

Lemma symmetric_from_pre : pre_symmetric -> symmetric.
Proof. by move=> symR x y; apply/idP/idP; apply: symR. Qed.

Definition reflexive := forall x, R x x.
Definition irreflexive := forall x, R x x = false.

Definition left_transitive := forall x y, R x y -> R x =1 R y.
Definition right_transitive := forall x y, R x y -> R^~ x =1 R^~ y.

Section PER.

Hypotheses (symR : symmetric) (trR : transitive).

Lemma sym_left_transitive : left_transitive.
Proof. by move=> x y Rxy z; apply/idP/idP; apply: trR; rewrite // symR. Qed.

Lemma sym_right_transitive : right_transitive.
Proof. by move=> x y /sym_left_transitive Rxy z; rewrite !(symR z) Rxy. Qed.

End PER.

(**
 We define the equivalence property with prenex quantification so that it
 can be localized using the {in ..., ..} form defined below.                 **)

Definition equivalence_rel := forall x y z, R z z * (R x y -> R x z = R y z).

Lemma equivalence_relP : equivalence_rel <-> reflexive /\ left_transitive.
Proof.
split=> [eqiR | [Rxx trR] x y z]; last by split=> [|/trR->].
by split=> [x | x y Rxy z]; [rewrite (eqiR x x x) | rewrite (eqiR x y z)].
Qed.

End RelationProperties.

Lemma rev_trans T (R : rel T) : transitive R -> transitive (fun x y => R y x).
Proof. by move=> trR x y z Ryx Rzy; apply: trR Rzy Ryx. Qed.

(**  Property localization  **)

Local Notation "{ 'all1' P }" := (forall x, P x : Prop) (at level 0).
Local Notation "{ 'all2' P }" := (forall x y, P x y : Prop) (at level 0).
Local Notation "{ 'all3' P }" := (forall x y z, P x y z: Prop) (at level 0).
Local Notation ph := (phantom _).

Section LocalProperties.

Variables T1 T2 T3 : Type.

Variables (d1 : mem_pred T1) (d2 : mem_pred T2) (d3 : mem_pred T3).
Local Notation ph := (phantom Prop).

Definition prop_for (x : T1) P & ph {all1 P} := P x.

Lemma forE x P phP : @prop_for x P phP = P x. Proof. by []. Qed.

Definition prop_in1 P & ph {all1 P} :=
  forall x, in_mem x d1 -> P x.

Definition prop_in11 P & ph {all2 P} :=
  forall x y, in_mem x d1 -> in_mem y d2 -> P x y.

Definition prop_in2 P & ph {all2 P} :=
  forall x y, in_mem x d1 -> in_mem y d1 -> P x y.

Definition prop_in111 P & ph {all3 P} :=
  forall x y z, in_mem x d1 -> in_mem y d2 -> in_mem z d3 -> P x y z.

Definition prop_in12 P & ph {all3 P} :=
  forall x y z, in_mem x d1 -> in_mem y d2 -> in_mem z d2 -> P x y z.

Definition prop_in21 P & ph {all3 P} :=
  forall x y z, in_mem x d1 -> in_mem y d1 -> in_mem z d2 -> P x y z.

Definition prop_in3 P & ph {all3 P} :=
  forall x y z, in_mem x d1 -> in_mem y d1 -> in_mem z d1 -> P x y z.

Variable f : T1 -> T2.

Definition prop_on1 Pf P & phantom T3 (Pf f) & ph {all1 P} :=
  forall x, in_mem (f x) d2 -> P x.

Definition prop_on2 Pf P & phantom T3 (Pf f) & ph {all2 P} :=
  forall x y, in_mem (f x) d2 -> in_mem (f y) d2 -> P x y.

End LocalProperties.

Definition inPhantom := Phantom Prop.
Definition onPhantom {T} P (x : T) := Phantom Prop (P x).

Definition bijective_in aT rT (d : mem_pred aT) (f : aT -> rT) :=
  exists2 g, prop_in1 d (inPhantom (cancel f g))
           & prop_on1 d (Phantom _ (cancel g)) (onPhantom (cancel g) f).

Definition bijective_on aT rT (cd : mem_pred rT) (f : aT -> rT) :=
  exists2 g, prop_on1 cd (Phantom _ (cancel f)) (onPhantom (cancel f) g)
           & prop_in1 cd (inPhantom (cancel g f)).

Notation "{ 'for' x , P }" := (prop_for x (inPhantom P)) : type_scope.
Notation "{ 'in' d , P }" := (prop_in1 (mem d) (inPhantom P)) : type_scope.
Notation "{ 'in' d1 & d2 , P }" :=
  (prop_in11 (mem d1) (mem d2) (inPhantom P)) : type_scope.
Notation "{ 'in' d & , P }" := (prop_in2 (mem d) (inPhantom P)) : type_scope.
Notation "{ 'in' d1 & d2 & d3 , P }" :=
  (prop_in111 (mem d1) (mem d2) (mem d3) (inPhantom P)) : type_scope.
Notation "{ 'in' d1 & & d3 , P }" :=
  (prop_in21 (mem d1) (mem d3) (inPhantom P)) : type_scope.
Notation "{ 'in' d1 & d2 & , P }" :=
  (prop_in12 (mem d1) (mem d2) (inPhantom P)) : type_scope.
Notation "{ 'in' d & & , P }" := (prop_in3 (mem d) (inPhantom P)) : type_scope.
Notation "{ 'on' cd , P }" :=
  (prop_on1 (mem cd) (inPhantom P) (inPhantom P)) : type_scope.

Notation "{ 'on' cd & , P }" :=
  (prop_on2 (mem cd) (inPhantom P) (inPhantom P)) : type_scope.

Local Arguments onPhantom : clear scopes.
Notation "{ 'on' cd , P & g }" :=
  (prop_on1 (mem cd) (Phantom (_ -> Prop) P) (onPhantom P g)) : type_scope.
Notation "{ 'in' d , 'bijective' f }" := (bijective_in (mem d) f) : type_scope.
Notation "{ 'on' cd , 'bijective' f }" :=
  (bijective_on (mem cd) f) : type_scope.

(**
 Weakening and monotonicity lemmas for localized predicates.
 Note that using these lemmas in backward reasoning will force expansion of
 the predicate definition, as Coq needs to expose the quantifier to apply
 these lemmas. We define a few specialized variants to avoid this for some
 of the ssrfun predicates.                                                   **)

Section LocalGlobal.

Variables T1 T2 T3 : predArgType.
Variables (D1 : {pred T1}) (D2 : {pred T2}) (D3 : {pred T3}).
Variables (d1 d1' : mem_pred T1) (d2 d2' : mem_pred T2) (d3 d3' : mem_pred T3).
Variables (f f' : T1 -> T2) (g : T2 -> T1) (h : T3).
Variables (P1 : T1 -> Prop) (P2 : T1 -> T2 -> Prop).
Variable P3 : T1 -> T2 -> T3 -> Prop.
Variable Q1 : (T1 -> T2) -> T1 -> Prop.
Variable Q1l : (T1 -> T2) -> T3 -> T1 -> Prop.
Variable Q2 : (T1 -> T2) -> T1 -> T1 -> Prop.

Hypothesis sub1 : sub_mem d1 d1'.
Hypothesis sub2 : sub_mem d2 d2'.
Hypothesis sub3 : sub_mem d3 d3'.

Lemma in1W : {all1 P1} -> {in D1, {all1 P1}}.
Proof. by move=> ? ?. Qed.
Lemma in2W : {all2 P2} -> {in D1 & D2, {all2 P2}}.
Proof. by move=> ? ?. Qed.
Lemma in3W : {all3 P3} -> {in D1 & D2 & D3, {all3 P3}}.
Proof. by move=> ? ?. Qed.

Lemma in1T : {in T1, {all1 P1}} -> {all1 P1}.
Proof. by move=> ? ?; auto. Qed.
Lemma in2T : {in T1 & T2, {all2 P2}} -> {all2 P2}.
Proof. by move=> ? ?; auto. Qed.
Lemma in3T : {in T1 & T2 & T3, {all3 P3}} -> {all3 P3}.
Proof. by move=> ? ?; auto. Qed.

Lemma sub_in1 (Ph : ph {all1 P1}) : prop_in1 d1' Ph -> prop_in1 d1 Ph.
Proof. by move=> allP x /sub1; apply: allP. Qed.

Lemma sub_in11 (Ph : ph {all2 P2}) : prop_in11 d1' d2' Ph -> prop_in11 d1 d2 Ph.
Proof. by move=> allP x1 x2 /sub1 d1x1 /sub2; apply: allP. Qed.

Lemma sub_in111 (Ph : ph {all3 P3}) :
  prop_in111 d1' d2' d3' Ph -> prop_in111 d1 d2 d3 Ph.
Proof. by move=> allP x1 x2 x3 /sub1 d1x1 /sub2 d2x2 /sub3; apply: allP. Qed.

Let allQ1 f'' := {all1 Q1 f''}.
Let allQ1l f'' h' := {all1 Q1l f'' h'}.
Let allQ2 f'' := {all2 Q2 f''}.

Lemma on1W : allQ1 f -> {on D2, allQ1 f}. Proof. by move=> ? ?. Qed.

Lemma on1lW : allQ1l f h -> {on D2, allQ1l f & h}. Proof. by move=> ? ?. Qed.

Lemma on2W : allQ2 f -> {on D2 &, allQ2 f}. Proof. by move=> ? ?. Qed.

Lemma on1T : {on T2, allQ1 f} -> allQ1 f. Proof. by move=> ? ?; auto. Qed.

Lemma on1lT : {on T2, allQ1l f & h} -> allQ1l f h.
Proof. by move=> ? ?; auto. Qed.

Lemma on2T : {on T2 &, allQ2 f} -> allQ2 f.
Proof. by move=> ? ?; auto. Qed.

Lemma subon1 (Phf : ph (allQ1 f)) (Ph : ph (allQ1 f)) :
  prop_on1 d2' Phf Ph -> prop_on1 d2 Phf Ph.
Proof. by move=> allQ x /sub2; apply: allQ. Qed.

Lemma subon1l (Phf : ph (allQ1l f)) (Ph : ph (allQ1l f h)) :
  prop_on1 d2' Phf Ph -> prop_on1 d2 Phf Ph.
Proof. by move=> allQ x /sub2; apply: allQ. Qed.

Lemma subon2 (Phf : ph (allQ2 f)) (Ph : ph (allQ2 f)) :
  prop_on2 d2' Phf Ph -> prop_on2 d2 Phf Ph.
Proof. by move=> allQ x y /sub2=> d2fx /sub2; apply: allQ. Qed.

Lemma can_in_inj : {in D1, cancel f g} -> {in D1 &, injective f}.
Proof. by move=> fK x y /fK{2}<- /fK{2}<- ->. Qed.

Lemma canLR_in x y : {in D1, cancel f g} -> y \in D1 -> x = f y -> g x = y.
Proof. by move=> fK D1y ->; rewrite fK. Qed.

Lemma canRL_in x y : {in D1, cancel f g} -> x \in D1 -> f x = y -> x = g y.
Proof. by move=> fK D1x <-; rewrite fK. Qed.

Lemma on_can_inj : {on D2, cancel f & g} -> {on D2 &, injective f}.
Proof. by move=> fK x y /fK{2}<- /fK{2}<- ->. Qed.

Lemma canLR_on x y : {on D2, cancel f & g} -> f y \in D2 -> x = f y -> g x = y.
Proof. by move=> fK D2fy ->; rewrite fK. Qed.

Lemma canRL_on x y : {on D2, cancel f & g} -> f x \in D2 -> f x = y -> x = g y.
Proof. by move=> fK D2fx <-; rewrite fK. Qed.

Lemma inW_bij : bijective f -> {in D1, bijective f}.
Proof. by case=> g' fK g'K; exists g' => * ? *; auto. Qed.

Lemma onW_bij : bijective f -> {on D2, bijective f}.
Proof. by case=> g' fK g'K; exists g' => * ? *; auto. Qed.

Lemma inT_bij : {in T1, bijective f} -> bijective f.
Proof. by case=> g' fK g'K; exists g' => * ? *; auto. Qed.

Lemma onT_bij : {on T2, bijective f} -> bijective f.
Proof. by case=> g' fK g'K; exists g' => * ? *; auto. Qed.

Lemma sub_in_bij (D1' : pred T1) :
  {subset D1 <= D1'} -> {in D1', bijective f} -> {in D1, bijective f}.
Proof.
by move=> subD [g' fK g'K]; exists g' => x; move/subD; [apply: fK | apply: g'K].
Qed.

Lemma subon_bij (D2' : pred T2) :
  {subset D2 <= D2'} -> {on D2', bijective f} -> {on D2, bijective f}.
Proof.
by move=> subD [g' fK g'K]; exists g' => x; move/subD; [apply: fK | apply: g'K].
Qed.

End LocalGlobal.

Lemma sub_in2 T d d' (P : T -> T -> Prop) :
  sub_mem d d' -> forall Ph : ph {all2 P}, prop_in2 d' Ph -> prop_in2 d Ph.
Proof. by move=> /= sub_dd'; apply: sub_in11. Qed.

Lemma sub_in3 T d d' (P : T -> T -> T -> Prop) :
  sub_mem d d' -> forall Ph : ph {all3 P}, prop_in3 d' Ph -> prop_in3 d Ph.
Proof. by move=> /= sub_dd'; apply: sub_in111. Qed.

Lemma sub_in12 T1 T d1 d1' d d' (P : T1 -> T -> T -> Prop) :
  sub_mem d1 d1' -> sub_mem d d' ->
  forall Ph : ph {all3 P}, prop_in12 d1' d' Ph -> prop_in12 d1 d Ph.
Proof. by move=> /= sub1 sub; apply: sub_in111. Qed.

Lemma sub_in21 T T3 d d' d3 d3' (P : T -> T -> T3 -> Prop) :
  sub_mem d d' -> sub_mem d3 d3' ->
  forall Ph : ph {all3 P}, prop_in21 d' d3' Ph -> prop_in21 d d3 Ph.
Proof. by move=> /= sub sub3; apply: sub_in111. Qed.

Lemma equivalence_relP_in T (R : rel T) (A : pred T) :
  {in A & &, equivalence_rel R}
   <-> {in A, reflexive R} /\ {in A &, forall x y, R x y -> {in A, R x =1 R y}}.
Proof.
split=> [eqiR | [Rxx trR] x y z *]; last by split=> [|/trR-> //]; apply: Rxx.
by split=> [x Ax|x y Ax Ay Rxy z Az]; [rewrite (eqiR x x) | rewrite (eqiR x y)].
Qed.

Section MonoHomoMorphismTheory.

Variables (aT rT sT : Type) (f : aT -> rT) (g : rT -> aT).
Variables (aP : pred aT) (rP : pred rT) (aR : rel aT) (rR : rel rT).

Lemma monoW : {mono f : x / aP x >-> rP x} -> {homo f : x / aP x >-> rP x}.
Proof. by move=> hf x ax; rewrite hf. Qed.

Lemma mono2W :
  {mono f : x y / aR x y >-> rR x y} -> {homo f : x y / aR x y >-> rR x y}.
Proof. by move=> hf x y axy; rewrite hf. Qed.

Hypothesis fgK : cancel g f.

Lemma homoRL :
  {homo f : x y / aR x y >-> rR x y} -> forall x y, aR (g x) y -> rR x (f y).
Proof. by move=> Hf x y /Hf; rewrite fgK. Qed.

Lemma homoLR :
  {homo f : x y / aR x y >-> rR x y} -> forall x y, aR x (g y) -> rR (f x) y.
Proof. by move=> Hf x y /Hf; rewrite fgK. Qed.

Lemma homo_mono :
    {homo f : x y / aR x y >-> rR x y} -> {homo g : x y / rR x y >-> aR x y} ->
  {mono g : x y / rR x y >-> aR x y}.
Proof.
move=> mf mg x y; case: (boolP (rR _ _))=> [/mg //|].
by apply: contraNF=> /mf; rewrite !fgK.
Qed.

Lemma monoLR :
  {mono f : x y / aR x y >-> rR x y} -> forall x y, rR (f x) y = aR x (g y).
Proof. by move=> mf x y; rewrite -{1}[y]fgK mf. Qed.

Lemma monoRL :
  {mono f : x y / aR x y >-> rR x y} -> forall x y, rR x (f y) = aR (g x) y.
Proof. by move=> mf x y; rewrite -{1}[x]fgK mf. Qed.

Lemma can_mono :
  {mono f : x y / aR x y >-> rR x y} -> {mono g : x y / rR x y >-> aR x y}.
Proof. by move=> mf x y /=; rewrite -mf !fgK. Qed.

End MonoHomoMorphismTheory.

Section MonoHomoMorphismTheory_in.

Variables (aT rT sT : predArgType) (f : aT -> rT) (g : rT -> aT).
Variable (aD : {pred aT}).
Variable (aP : pred aT) (rP : pred rT) (aR : rel aT) (rR : rel rT).

Notation rD := [pred x | g x \in aD].

Lemma monoW_in :
    {in aD &, {mono f : x y / aR x y >-> rR x y}} ->
  {in aD &, {homo f : x y / aR x y >-> rR x y}}.
Proof. by move=> hf x y hx hy axy; rewrite hf. Qed.

Lemma mono2W_in :
    {in aD, {mono f : x / aP x >-> rP x}} ->
  {in aD, {homo f : x / aP x >-> rP x}}.
Proof. by move=> hf x hx ax; rewrite hf. Qed.

Hypothesis fgK_on : {on aD, cancel g & f}.

Lemma homoRL_in :
    {in aD &, {homo f : x y / aR x y >-> rR x y}} ->
  {in rD & aD, forall x y, aR (g x) y -> rR x (f y)}.
Proof. by move=> Hf x y hx hy /Hf; rewrite fgK_on //; apply. Qed.

Lemma homoLR_in :
    {in aD &, {homo f : x y / aR x y >-> rR x y}} ->
  {in aD & rD, forall x y, aR x (g y) -> rR (f x) y}.
Proof. by move=> Hf x y hx hy /Hf; rewrite fgK_on //; apply. Qed.

Lemma homo_mono_in :
    {in aD &, {homo f : x y / aR x y >-> rR x y}} ->
    {in rD &, {homo g : x y / rR x y >-> aR x y}} ->
  {in rD &, {mono g : x y / rR x y >-> aR x y}}.
Proof.
move=> mf mg x y hx hy; case: (boolP (rR _ _))=> [/mg //|]; first exact.
by apply: contraNF=> /mf; rewrite !fgK_on //; apply.
Qed.

Lemma monoLR_in :
    {in aD &, {mono f : x y / aR x y >-> rR x y}} ->
  {in aD & rD, forall x y, rR (f x) y = aR x (g y)}.
Proof. by move=> mf x y hx hy; rewrite -{1}[y]fgK_on // mf. Qed.

Lemma monoRL_in :
    {in aD &, {mono f : x y / aR x y >-> rR x y}} ->
  {in rD & aD, forall x y, rR x (f y) = aR (g x) y}.
Proof. by move=> mf x y hx hy; rewrite -{1}[x]fgK_on // mf. Qed.

Lemma can_mono_in :
    {in aD &, {mono f : x y / aR x y >-> rR x y}} ->
  {in rD &, {mono g : x y / rR x y >-> aR x y}}.
Proof. by move=> mf x y hx hy /=; rewrite -mf // !fgK_on. Qed.

End MonoHomoMorphismTheory_in.
