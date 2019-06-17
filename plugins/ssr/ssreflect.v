(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

(** #<style> .doc { font-family: monospace; white-space: pre; } </style># **)

Require Import Bool. (* For bool_scope delimiter 'bool'. *)
Require Import ssrmatching.
Declare ML Module "ssreflect_plugin".


(**
 This file is the Gallina part of the ssreflect plugin implementation.
 Files that use the ssreflect plugin should always Require ssreflect and
 either Import ssreflect or Import ssreflect.SsrSyntax.
   Part of the contents of this file is technical and will only interest
 advanced developers; in addition the following are defined:
   #[#the str of v by f#]# == the Canonical s : str such that f s = v.
        #[#the str of v#]# == the Canonical s : str that coerces to v.
        argumentType c == the T such that c : forall x : T, P x.
          returnType c == the R such that c : T -> R.
     {type of c for s} == P s where c : forall x : T, P x.
           nonPropType == an interface for non-Prop Types: a nonPropType coerces
                          to a Type, and only types that do _not_ have sort
                          Prop are canonical nonPropType instances. This is
                          useful for applied views (see mid-file comment).
             notProp T == the nonPropType instance for type T.
           phantom T v == singleton type with inhabitant Phantom T v.
               phant T == singleton type with inhabitant Phant v.
                 =^~ r == the converse of rewriting rule r (e.g., in a
                          rewrite multirule).
             unkeyed t == t, but treated as an unkeyed matching pattern by
                          the ssreflect matching algorithm.
             nosimpl t == t, but on the right-hand side of Definition C :=
                          nosimpl disables expansion of C by /=.
              locked t == t, but locked t is not convertible to t.
       locked_with k t == t, but not convertible to t or locked_with k' t
                          unless k = k' (with k : unit). Coq type-checking
                          will be much more efficient if locked_with with a
                          bespoke k is used for sealed definitions.
          unlockable v == interface for sealed constant definitions of v.
        Unlockable def == the unlockable that registers def : C = v.
     #[#unlockable of C#]# == a clone for C of the canonical unlockable for the
                          definition of C (e.g., if it uses locked_with).
    #[#unlockable fun C#]# == #[#unlockable of C#]# with the expansion forced to be
                          an explicit lambda expression.
  -> The usage pattern for ADT operations is:
       Definition foo_def x1 .. xn := big_foo_expression.
       Fact foo_key : unit. Proof. by #[# #]#. Qed.
       Definition foo := locked_with foo_key foo_def.
       Canonical foo_unlockable := #[#unlockable fun foo#]#.
     This minimizes the comparison overhead for foo, while still allowing
     rewrite unlock to expose big_foo_expression.
 More information about these definitions and their use can be found in the
 ssreflect manual, and in specific comments below.                           **)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SsrSyntax.

(**
 Declare Ssr keywords: 'is' 'of' '//' '/=' and '//='. We also declare the
 parsing level 8, as a workaround for a notation grammar factoring problem.
 Arguments of application-style notations (at level 10) should be declared
 at level 8 rather than 9 or the camlp5 grammar will not factor properly.    **)

Reserved Notation "(* x 'is' y 'of' z 'isn't' // /= //= *)" (at level 8).
Reserved Notation "(* 69 *)" (at level 69).

(**  Non ambiguous keyword to check if the SsrSyntax module is imported  **)
Reserved Notation "(* Use to test if 'SsrSyntax_is_Imported' *)" (at level 8).

Reserved Notation "<hidden n >" (at level 0, n at level 0,
  format "<hidden  n >").
Reserved Notation "T (* n *)" (at level 200, format "T  (* n *)").

End SsrSyntax.

Export SsrMatchingSyntax.
Export SsrSyntax.

(** Save primitive notation that will be overloaded. **)
Local Notation CoqGenericIf c vT vF := (if c then vT else vF) (only parsing).
Local Notation CoqGenericDependentIf c x R vT vF :=
  (if c as x return R then vT else vF) (only parsing).
Local Notation CoqCast x T := (x : T) (only parsing).

(** Reserve notation that introduced in this file. **)
Reserved Notation "'if' c 'then' vT 'else' vF" (at level 200,
  c, vT, vF at level 200, only parsing).
Reserved Notation "'if' c 'return' R 'then' vT 'else' vF" (at level 200,
  c, R, vT, vF at level 200, only parsing).
Reserved Notation "'if' c 'as' x 'return' R 'then' vT 'else' vF" (at level 200,
  c, R, vT, vF at level 200, x ident, only parsing).

Reserved Notation "x : T" (at level 100, right associativity,
  format "'[hv' x '/ '  :  T ']'").
Reserved Notation "T : 'Type'" (at level 100, format "T  :  'Type'").
Reserved Notation "P : 'Prop'" (at level 100, format "P  :  'Prop'").

Reserved Notation "[ 'the' sT 'of' v 'by' f ]" (at level 0,
  format "[ 'the'  sT  'of'  v  'by'  f ]").
Reserved Notation "[ 'the' sT 'of' v ]" (at level 0,
  format "[ 'the'  sT  'of'  v ]").
Reserved Notation "{ 'type' 'of' c 'for' s }" (at level 0,
  format "{ 'type'  'of'  c  'for'  s }").

Reserved Notation "=^~ r" (at level 100, format "=^~  r").

Reserved Notation "[ 'unlockable' 'of' C ]" (at level 0,
  format "[ 'unlockable'  'of'  C ]").
Reserved Notation "[ 'unlockable' 'fun' C ]" (at level 0,
  format "[ 'unlockable'  'fun'  C ]").

(**
 To define notations for tactic in intro patterns.
 When "=> /t" is parsed, "t:%ssripat" is actually interpreted. **)
Declare Scope ssripat_scope.
Delimit Scope ssripat_scope with ssripat.

(**
 Make the general "if" into a notation, so that we can override it below.
 The notations are "only parsing" because the Coq decompiler will not
 recognize the expansion of the boolean if; using the default printer
 avoids a spurious trailing %%GEN_IF. **)

Declare Scope general_if_scope.
Delimit Scope general_if_scope with GEN_IF.

Notation "'if' c 'then' vT 'else' vF" :=
  (CoqGenericIf c vT vF) (only parsing) : general_if_scope.

Notation "'if' c 'return' R 'then' vT 'else' vF" :=
  (CoqGenericDependentIf c c R vT vF) (only parsing) : general_if_scope.

Notation "'if' c 'as' x 'return' R 'then' vT 'else' vF" :=
  (CoqGenericDependentIf c x R vT vF) (only parsing) : general_if_scope.

(**  Force boolean interpretation of simple if expressions.  **)

Declare Scope boolean_if_scope.
Delimit Scope boolean_if_scope with BOOL_IF.

Notation "'if' c 'return' R 'then' vT 'else' vF" :=
  (if c is true as c in bool return R then vT else vF) : boolean_if_scope.

Notation "'if' c 'then' vT 'else' vF" :=
  (if c%bool is true as _ in bool return _ then vT else vF) : boolean_if_scope.

Notation "'if' c 'as' x 'return' R 'then' vT 'else' vF" :=
  (if c%bool is true as x in bool return R then vT else vF) : boolean_if_scope.

Open Scope boolean_if_scope.

(**
 To allow a wider variety of notations without reserving a large number of
 of identifiers, the ssreflect library systematically uses "forms" to
 enclose complex mixfix syntax. A "form" is simply a mixfix expression
 enclosed in square brackets and introduced by a keyword:
      #[#keyword ... #]#
 Because the keyword follows a bracket it does not need to be reserved.
 Non-ssreflect libraries that do not respect the form syntax (e.g., the Coq
 Lists library) should be loaded before ssreflect so that their notations
 do not mask all ssreflect forms.                                            **)
Declare Scope form_scope.
Delimit Scope form_scope with FORM.
Open Scope form_scope.

(**
 Allow overloading of the cast (x : T) syntax, put whitespace around the
 ":" symbol to avoid lexical clashes (and for consistency with the parsing
 precedence of the notation, which binds less tightly than application),
 and put printing boxes that print the type of a long definition on a
 separate line rather than force-fit it at the right margin.                 **)
Notation "x : T" := (CoqCast x T) : core_scope.

(**
 Allow the casual use of notations like nat * nat for explicit Type
 declarations. Note that (nat * nat : Type) is NOT equivalent to
 (nat * nat)%%type, whose inferred type is legacy type "Set".                **)
Notation "T : 'Type'" := (CoqCast T%type Type) (only parsing) : core_scope.
(**  Allow similarly Prop annotation for, e.g., rewrite multirules. **)
Notation "P : 'Prop'" := (CoqCast P%type Prop) (only parsing) : core_scope.

(**  Constants for abstract: and #[#: name #]# intro pattern  **)
Definition abstract_lock := unit.
Definition abstract_key := tt.

Definition abstract (statement : Type) (id : nat) (lock : abstract_lock) :=
  let: tt := lock in statement.

Declare Scope ssr_scope.
Notation "<hidden n >" := (abstract _ n _) : ssr_scope.
Notation "T (* n *)" := (abstract T n abstract_key) : ssr_scope.
Open Scope ssr_scope.

Register abstract_lock as plugins.ssreflect.abstract_lock.
Register abstract_key as plugins.ssreflect.abstract_key.
Register abstract as plugins.ssreflect.abstract.

(**  Constants for tactic-views  **)
#[universes(template)]
Inductive external_view : Type := tactic_view of Type.

(**
 Syntax for referring to canonical structures:
      #[#the struct_type of proj_val by proj_fun#]#
 This form denotes the Canonical instance s of the Structure type
 struct_type whose proj_fun projection is proj_val, i.e., such that
      proj_fun s = proj_val.
 Typically proj_fun will be A record field accessors of struct_type, but
 this need not be the case; it can be, for instance, a field of a record
 type to which struct_type coerces; proj_val will likewise be coerced to
 the return type of proj_fun. In all but the simplest cases, proj_fun
 should be eta-expanded to allow for the insertion of implicit arguments.
   In the common case where proj_fun itself is a coercion, the "by" part
 can be omitted entirely; in this case it is inferred by casting s to the
 inferred type of proj_val. Obviously the latter can be fixed by using an
 explicit cast on proj_val, and it is highly recommended to do so when the
 return type intended for proj_fun is "Type", as the type inferred for
 proj_val may vary because of sort polymorphism (it could be Set or Prop).
   Note when using the #[#the _ of _ #]# form to generate a substructure from a
 telescopes-style canonical hierarchy (implementing inheritance with
 coercions), one should always project or coerce the value to the BASE
 structure, because Coq will only find a Canonical derived structure for
 the Canonical base structure -- not for a base structure that is specific
 to proj_value.                                                              **)

Module TheCanonical.

#[universes(template)]
Variant put vT sT (v1 v2 : vT) (s : sT) := Put.

Definition get vT sT v s (p : @put vT sT v v s) := let: Put _ _ _ := p in s.

Definition get_by vT sT of sT -> vT := @get vT sT.

End TheCanonical.

Import TheCanonical. (* Note: no export. *)

Local Arguments get_by _%type_scope _%type_scope _ _ _ _.

Notation "[ 'the' sT 'of' v 'by' f ]" :=
  (@get_by _ sT f _ _ ((fun v' (s : sT) => Put v' (f s) s) v _))
  (only parsing) : form_scope.

Notation "[ 'the' sT 'of' v ]" := (get ((fun s : sT => Put v (*coerce*) s s) _))
  (only parsing) : form_scope.

(**
 The following are "format only" versions of the above notations.
 We need to do this to prevent the formatter from being be thrown off by
 application collapsing, coercion insertion and beta reduction in the right
 hand side of the notations above.                                           **)

Notation "[ 'the' sT 'of' v 'by' f ]" := (@get_by _ sT f v _ _)
  (only printing) : form_scope.

Notation "[ 'the' sT 'of' v ]" := (@get _ sT v _ _)
  (only printing) : form_scope.

(**
 We would like to recognize
Notation " #[# 'the' sT 'of' v : 'Type' #]#" := (@get Type sT v _ _)
  (at level 0, format " #[# 'the'  sT   'of'  v  :  'Type' #]#") : form_scope.
 **)

(**
 Helper notation for canonical structure inheritance support.
 This is a workaround for the poor interaction between delta reduction and
 canonical projections in Coq's unification algorithm, by which transparent
 definitions hide canonical instances, i.e., in
   Canonical a_type_struct := @Struct a_type ...
   Definition my_type := a_type.
 my_type doesn't effectively inherit the struct structure from a_type. Our
 solution is to redeclare the instance as follows
   Canonical my_type_struct := Eval hnf in #[#struct of my_type#]#.
 The special notation #[#str of _ #]# must be defined for each Strucure "str"
 with constructor "Str", typically as follows
   Definition clone_str s :=
      let: Str _ x y ... z := s return {type of Str for s} -> str in
      fun k => k _ x y ... z.
    Notation " #[# 'str' 'of' T 'for' s #]#" := (@clone_str s (@Str T))
      (at level 0, format " #[# 'str'  'of'  T  'for'  s #]#") : form_scope.
    Notation " #[# 'str' 'of' T #]#" := (repack_str (fun x => @Str T x))
      (at level 0, format " #[# 'str'  'of'  T #]#") : form_scope.
 The notation for the match return predicate is defined below; the eta
 expansion in the second form serves both to distinguish it from the first
 and to avoid the delta reduction problem.
   There are several variations on the notation and the definition of the
 the "clone" function, for telescopes, mixin classes, and join (multiple
 inheritance) classes. We describe a different idiom for clones in ssrfun;
 it uses phantom types (see below) and static unification; see fintype and
 ssralg for examples.                                                        **)

Definition argumentType T P & forall x : T, P x := T.
Definition dependentReturnType T P & forall x : T, P x := P.
Definition returnType aT rT & aT -> rT := rT.

Notation "{ 'type' 'of' c 'for' s }" := (dependentReturnType c s) : type_scope.

(**
 A generic "phantom" type (actually, a unit type with a phantom parameter).
 This type can be used for type definitions that require some Structure
 on one of their parameters, to allow Coq to infer said structure so it
 does not have to be supplied explicitly or via the " #[#the _ of _ #]#" notation
 (the latter interacts poorly with other Notation).
   The definition of a (co)inductive type with a parameter p : p_type, that
 needs to use the operations of a structure
  Structure p_str : Type := p_Str {p_repr :> p_type; p_op : p_repr -> ...}
 should be given as
  Inductive indt_type (p : p_str) := Indt ... .
  Definition indt_of (p : p_str) & phantom p_type p := indt_type p.
  Notation "{ 'indt' p }" := (indt_of (Phantom p)).
  Definition indt p x y ... z : {indt p} := @Indt p x y ... z.
  Notation " #[# 'indt' x y ... z #]#" := (indt x y ... z).
 That is, the concrete type and its constructor should be shadowed by
 definitions that use a phantom argument to infer and display the true
 value of p (in practice, the "indt" constructor often performs additional
 functions, like "locking" the representation -- see below).
   We also define a simpler version ("phant" / "Phant") of phantom for the
 common case where p_type is Type.                                           **)

#[universes(template)]
Variant phantom T (p : T) := Phantom.
Arguments phantom : clear implicits.
Arguments Phantom : clear implicits.
#[universes(template)]
Variant phant (p : Type) := Phant.

(**  Internal tagging used by the implementation of the ssreflect elim.  **)

Definition protect_term (A : Type) (x : A) : A := x.

Register protect_term as plugins.ssreflect.protect_term.

(**
 The ssreflect idiom for a non-keyed pattern:
  - unkeyed t will match any subterm that unifies with t, regardless of
    whether it displays the same head symbol as t.
  - unkeyed t a b will match any application of a term f unifying with t,
    to two arguments unifying with with a and b, respectively, regardless of
    apparent head symbols.
  - unkeyed x where x is a variable will match any subterm with the same
    type as x (when x would raise the 'indeterminate pattern' error).        **)

Notation unkeyed x := (let flex := x in flex).

(**  Ssreflect converse rewrite rule rule idiom.  **)
Definition ssr_converse R (r : R) := (Logic.I, r).
Notation "=^~ r" := (ssr_converse r) : form_scope.

(**
 Term tagging (user-level).
 The ssreflect library uses four strengths of term tagging to restrict
 convertibility during type checking:
  nosimpl t simplifies to t EXCEPT in a definition; more precisely, given
    Definition foo := nosimpl bar, foo (or foo t') will NOT be expanded by
    the /= and //= switches unless it is in a forcing context (e.g., in
    match foo t' with ... end, foo t' will be reduced if this allows the
    match to be reduced). Note that nosimpl bar is simply notation for a
    a term that beta-iota reduces to bar; hence rewrite /foo will replace
    foo by bar, and rewrite -/foo will replace bar by foo.
    CAVEAT: nosimpl should not be used inside a Section, because the end of
    section "cooking" removes the iota redex.
  locked t is provably equal to t, but is not convertible to t; 'locked'
    provides support for selective rewriting, via the lock t : t = locked t
    Lemma, and the ssreflect unlock tactic.
  locked_with k t is equal but not convertible to t, much like locked t,
    but supports explicit tagging with a value k : unit. This is used to
    mitigate a flaw in the term comparison heuristic of the Coq kernel,
    which treats all terms of the form locked t as equal and compares their
    arguments recursively, leading to an exponential blowup of comparison.
    For this reason locked_with should be used rather than locked when
    defining ADT operations. The unlock tactic does not support locked_with
    but the unlock rewrite rule does, via the unlockable interface.
  we also use Module Type ascription to create truly opaque constants,
    because simple expansion of constants to reveal an unreducible term
    doubles the time complexity of a negative comparison. Such opaque
    constants can be expanded generically with the unlock rewrite rule.
    See the definition of card and subset in fintype for examples of this.   **)

Notation nosimpl t := (let: tt := tt in t).

Lemma master_key : unit. Proof. exact tt. Qed.
Definition locked A := let: tt := master_key in fun x : A => x.

Register master_key as plugins.ssreflect.master_key.
Register locked as plugins.ssreflect.locked.

Lemma lock A x : x = locked x :> A. Proof. unlock; reflexivity. Qed.

(**  Needed for locked predicates, in particular for eqType's.  **)
Lemma not_locked_false_eq_true : locked false <> true.
Proof. unlock; discriminate. Qed.

(**  The basic closing tactic "done".  **)
Ltac done :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | apply: sym_equal; trivial]
         | discriminate | contradiction | split]
   | case not_locked_false_eq_true; assumption
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].

(**  Quicker done tactic not including split, syntax: /0/  **)
Ltac ssrdone0 :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | apply: sym_equal; trivial]
         | discriminate | contradiction ]
   | case not_locked_false_eq_true; assumption
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].

(**  To unlock opaque constants.  **)
#[universes(template)]
Structure unlockable T v := Unlockable {unlocked : T; _ : unlocked = v}.
Lemma unlock T x C : @unlocked T x C = x. Proof. by case: C. Qed.

Notation "[ 'unlockable' 'of' C ]" :=
  (@Unlockable _ _ C (unlock _)) : form_scope.

Notation "[ 'unlockable' 'fun' C ]" :=
  (@Unlockable _ (fun _ => _) C (unlock _)) : form_scope.

(**  Generic keyed constant locking.  **)

(**  The argument order ensures that k is always compared before T.  **)
Definition locked_with k := let: tt := k in fun T x => x : T.

(**
 This can be used as a cheap alternative to cloning the unlockable instance
 below, but with caution as unkeyed matching can be expensive.               **)
Lemma locked_withE T k x : unkeyed (locked_with k x) = x :> T.
Proof. by case: k. Qed.

(**  Intensionaly, this instance will not apply to locked u.  **)
Canonical locked_with_unlockable T k x :=
  @Unlockable T x (locked_with k x) (locked_withE k x).

(**  More accurate variant of unlock, and safer alternative to locked_withE. **)
Lemma unlock_with T k x : unlocked (locked_with_unlockable k x) = x :> T.
Proof. exact: unlock. Qed.

(**  The internal lemmas for the have tactics.  **)

Definition ssr_have Plemma Pgoal (step : Plemma) rest : Pgoal := rest step.
Arguments ssr_have Plemma [Pgoal].

Definition ssr_have_let Pgoal Plemma step
  (rest : let x : Plemma := step in Pgoal) : Pgoal := rest.
Arguments ssr_have_let [Pgoal].

Register ssr_have as plugins.ssreflect.ssr_have.
Register ssr_have_let as plugins.ssreflect.ssr_have_let.

Definition ssr_suff Plemma Pgoal step (rest : Plemma) : Pgoal := step rest.
Arguments ssr_suff Plemma [Pgoal].

Definition ssr_wlog := ssr_suff.
Arguments ssr_wlog Plemma [Pgoal].

Register ssr_suff as plugins.ssreflect.ssr_suff.
Register ssr_wlog as plugins.ssreflect.ssr_wlog.

(**  Internal N-ary congruence lemmas for the congr tactic.  **)

Fixpoint nary_congruence_statement (n : nat)
         : (forall B, (B -> B -> Prop) -> Prop) -> Prop :=
  match n with
  | O => fun k => forall B, k B (fun x1 x2 : B => x1 = x2)
  | S n' =>
    let k' A B e (f1 f2 : A -> B) :=
      forall x1 x2, x1 = x2 -> (e (f1 x1) (f2 x2) : Prop) in
    fun k => forall A, nary_congruence_statement n' (fun B e => k _ (k' A B e))
  end.

Lemma nary_congruence n (k := fun B e => forall y : B, (e y y : Prop)) :
  nary_congruence_statement n k.
Proof.
have: k _ _ := _; rewrite {1}/k.
elim: n k  => [|n IHn] k k_P /= A; first exact: k_P.
by apply: IHn => B e He; apply: k_P => f x1 x2 <-.
Qed.

Lemma ssr_congr_arrow Plemma Pgoal : Plemma = Pgoal -> Plemma -> Pgoal.
Proof. by move->. Qed.
Arguments ssr_congr_arrow : clear implicits.

Register nary_congruence as plugins.ssreflect.nary_congruence.
Register ssr_congr_arrow as plugins.ssreflect.ssr_congr_arrow.

(**  View lemmas that don't use reflection.  **)

Section ApplyIff.

Variables P Q : Prop.
Hypothesis eqPQ : P <-> Q.

Lemma iffLR : P -> Q. Proof. by case: eqPQ. Qed.
Lemma iffRL : Q -> P. Proof. by case: eqPQ. Qed.

Lemma iffLRn : ~P -> ~Q. Proof. by move=> nP tQ; case: nP; case: eqPQ tQ. Qed.
Lemma iffRLn : ~Q -> ~P. Proof. by move=> nQ tP; case: nQ; case: eqPQ tP. Qed.

End ApplyIff.

Hint View for move/ iffLRn|2 iffRLn|2 iffLR|2 iffRL|2.
Hint View for apply/ iffRLn|2 iffLRn|2 iffRL|2 iffLR|2.

(**
 To focus non-ssreflect tactics on a subterm, eg vm_compute.
 Usage:
   elim/abstract_context: (pattern) => G defG.
   vm_compute; rewrite {}defG {G}.
 Note that vm_cast are not stored in the proof term
 for reductions occurring in the context, hence
   set here := pattern; vm_compute in (value of here)
 blows up at Qed time.                                        **)
Lemma abstract_context T (P : T -> Type) x :
  (forall Q, Q = P -> Q x) -> P x.
Proof. by move=> /(_ P); apply. Qed.

(*****************************************************************************)
(* Constants for under, to rewrite under binders using "Leibniz eta lemmas". *)

Module Type UNDER_EQ.
Parameter Under_eq :
  forall (R : Type), R -> R -> Prop.
Parameter Under_eq_from_eq :
  forall (T : Type) (x y : T), @Under_eq T x y -> x = y.

(** [Over_eq, over_eq, over_eq_done]: for "by rewrite over_eq" *)
Parameter Over_eq :
  forall (R : Type), R -> R -> Prop.
Parameter over_eq :
  forall (T : Type) (x : T) (y : T), @Under_eq T x y = @Over_eq T x y.
Parameter over_eq_done :
  forall (T : Type) (x : T), @Over_eq T x x.
(* We need both hints below, otherwise the test-suite does not pass *)
Hint Extern 0 (@Over_eq _ _ _) => solve [ apply over_eq_done ] : core.
(* => for [test-suite/ssr/under.v:test_big_patt1] *)
Hint Resolve over_eq_done : core.
(* => for [test-suite/ssr/over.v:test_over_1_1] *)

(** [under_eq_done]: for Ltac-style over *)
Parameter under_eq_done :
  forall (T : Type) (x : T), @Under_eq T x x.
Notation "''Under[' x ]" := (@Under_eq _ x _)
  (at level 8, format "''Under['  x  ]", only printing).
End UNDER_EQ.

Module Export Under_eq : UNDER_EQ.
Definition Under_eq := @eq.
Lemma Under_eq_from_eq (T : Type) (x y : T) :
  @Under_eq T x y -> x = y.
Proof. by []. Qed.
Definition Over_eq := Under_eq.
Lemma over_eq :
  forall (T : Type) (x : T) (y : T), @Under_eq T x y = @Over_eq T x y.
Proof. by []. Qed.
Lemma over_eq_done :
  forall (T : Type) (x : T), @Over_eq T x x.
Proof. by []. Qed.
Lemma under_eq_done :
  forall (T : Type) (x : T), @Under_eq T x x.
Proof. by []. Qed.
End Under_eq.

Register Under_eq as plugins.ssreflect.Under_eq.
Register Under_eq_from_eq as plugins.ssreflect.Under_eq_from_eq.

Module Type UNDER_IFF.
Parameter Under_iff : Prop -> Prop -> Prop.
Parameter Under_iff_from_iff : forall x y : Prop, @Under_iff x y -> x <-> y.

(** [Over_iff, over_iff, over_iff_done]: for "by rewrite over_iff" *)
Parameter Over_iff : Prop -> Prop -> Prop.
Parameter over_iff :
  forall (x : Prop) (y : Prop), @Under_iff x y = @Over_iff x y.
Parameter over_iff_done :
  forall (x : Prop), @Over_iff x x.
Hint Extern 0 (@Over_iff _ _) => solve [ apply over_iff_done ] : core.
Hint Resolve over_iff_done : core.

(** [under_iff_done]: for Ltac-style over *)
Parameter under_iff_done :
  forall (x : Prop), @Under_iff x x.
Notation "''Under[' x ]" := (@Under_iff x _)
  (at level 8, format "''Under['  x  ]", only printing).
End UNDER_IFF.

Module Export Under_iff : UNDER_IFF.
Definition Under_iff := iff.
Lemma Under_iff_from_iff (x y : Prop) :
  @Under_iff x y -> x <-> y.
Proof. by []. Qed.
Definition Over_iff := Under_iff.
Lemma over_iff :
  forall (x : Prop) (y : Prop), @Under_iff x y = @Over_iff x y.
Proof. by []. Qed.
Lemma over_iff_done :
  forall (x : Prop), @Over_iff x x.
Proof. by []. Qed.
Lemma under_iff_done :
  forall (x : Prop), @Under_iff x x.
Proof. by []. Qed.
End Under_iff.

Register Under_iff as plugins.ssreflect.Under_iff.
Register Under_iff_from_iff as plugins.ssreflect.Under_iff_from_iff.

Definition over := (over_eq, over_iff).

Ltac over :=
  by [ apply: Under_eq.under_eq_done
     | apply: Under_iff.under_iff_done
     | rewrite over
     ].

(** An interface for non-Prop types; used to avoid improper instantiation
    of polymorphic lemmas with on-demand implicits when they are used as views.
    For example: Some_inj {T} : forall x y : T, Some x = Some y -> x = y.
    Using move/Some_inj on a goal of the form Some n = Some 0 will fail:
    SSReflect will interpret the view as @Some_inj ?T _top_assumption_
    since this is the well-typed application of the view with the minimal
    number of inserted evars (taking ?T := Some n = Some 0), and then will
    later complain that it cannot erase _top_assumption_ after having
    abstracted the viewed assumption. Making x and y maximal implicits
    would avoid this and force the intended @Some_inj nat x y _top_assumption_
    interpretation, but is undesirable as it makes it harder to use Some_inj
    with the many SSReflect and MathComp lemmas that have an injectivity
    premise. Specifying {T : nonPropType} solves this more elegantly, as then
    (?T : Type) no longer unifies with (Some n = Some 0), which has sort Prop.
 **)

Module NonPropType.

(** Implementation notes:
 We rely on three interface Structures:
  - test_of r, the middle structure, performs the actual check: it has two
    canonical instances whose 'condition' projection are maybeProj (?P : Prop)
    and tt, and which set r := true and r := false, respectively. Unifying
    condition (?t : test_of ?r) with maybeProj T will thus set ?r to true if
    T is in Prop as the test_Prop T instance will apply, and otherwise simplify
    maybeProp T to tt and use the test_negative instance and set ?r to false.
  - call_of c r sets up a call to test_of on condition c with expected result r.
    It has a default instance for its 'callee' projection to Type, which
    sets c := maybeProj T and r := false when unifying with a type T.
  - type is a telescope on call_of c r, which checks that unifying test_of ?r1
    with c indeed sets ?r1 := r; the type structure bundles the 'test' instance
    and its 'result' value along with its call_of c r projection. The default
    instance essentially provides eta-expansion for 'type'. This is only
    essential for the first 'result' projection to bool; using the instance
    for other projection merely avoids spurious delta expansions that would
    spoil the notProp T notation.
 In detail, unifying T =~= ?S with ?S : nonPropType, i.e.,
  (1)  T =~= @callee (@condition (result ?S) (test ?S)) (result ?S) (frame ?S)
 first uses the default call instance with ?T := T to reduce (1) to
  (2a) @condition (result ?S) (test ?S) =~= maybeProp T
  (3)                         result ?S =~= false
  (4)                          frame ?S =~= call T
 along with some trivial universe-related checks which are irrelevant here.
   Then the unification tries to use the test_Prop instance to reduce (2a) to
  (6a)                        result ?S =~= true
  (7a)                               ?P =~= T with ?P : Prop
  (8a)                          test ?S =~= test_Prop ?P
 Now the default 'check' instance with ?result := true resolves (6a) as
  (9a)                               ?S := @check true ?test ?frame
 Then (7a) can be solved precisely if T has sort at most (hence exactly) Prop,
 and then (8a) is solved by the check instance, yielding ?test := test_Prop T,
 and completing the solution of (2a), and _committing_ to it. But now (3) is
 inconsistent with (9a), and this makes the entire problem (1) fails.
   If on the othe hand T does not have sort Prop then (7a) fails and the
 unification resorts to delta expanding (2a), which gives
  (2b) @condition (result ?S) (test ?S) =~= tt
 which is then reduced, using the test_negative instance, to
  (6b)                        result ?S =~= false
  (8b)                          test ?S =~= test_negative
 Both are solved using the check default instance, as in the (2a) branch, giving
  (9b)                               ?S := @check false test_negative ?frame
 Then (3) and (4) are similarly soved using check, giving the final assignment
  (9)                                ?S := notProp T
 Observe that we _must_ perform the actual test unification on the arguments
 of the initial canonical instance, and not on the instance itself as we do
 in mathcomp/matrix and mathcomp/vector, because we want the unification to
 fail when T has sort Prop. If both the test_of _and_ the result check
 unifications were done as part of the structure telescope then the latter
 would be a sub-problem of the former, and thus failing the check would merely
 make the test_of unification backtrack and delta-expand and we would not get
 failure.
 **)

Structure call_of (condition : unit) (result : bool) := Call {callee : Type}.
Definition maybeProp (T : Type) := tt.
Definition call T := Call (maybeProp T) false T.

Structure test_of (result : bool) := Test {condition :> unit}.
Definition test_Prop (P : Prop) := Test true (maybeProp P).
Definition test_negative := Test false tt.

Structure type :=
  Check {result : bool; test : test_of result; frame : call_of test result}.
Definition check result test frame := @Check result test frame.

Module Exports.
Canonical call.
Canonical test_Prop.
Canonical test_negative.
Canonical check.
Notation nonPropType := type.
Coercion callee : call_of >-> Sortclass.
Coercion frame : type >-> call_of.
Notation notProp T := (@check false test_negative (call T)).
End Exports.

End NonPropType.
Export NonPropType.Exports.
