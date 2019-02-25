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

Reserved Notation "<hidden n >" (at level 200).
Reserved Notation "T (* n *)" (at level 200, format "T  (* n *)").

End SsrSyntax.

Export SsrMatchingSyntax.
Export SsrSyntax.

(**
 To define notations for tactic in intro patterns.
 When "=> /t" is parsed, "t:%ssripat" is actually interpreted. **)
Declare Scope ssripat_scope.
Delimit Scope ssripat_scope with ssripat.

(**
 Make the general "if" into a notation, so that we can override it below.
 The notations are "only parsing" because the Coq decompiler will not
 recognize the expansion of the boolean if; using the default printer
 avoids a spurrious trailing %%GEN_IF. **)

Declare Scope general_if_scope.
Delimit Scope general_if_scope with GEN_IF.

Notation "'if' c 'then' v1 'else' v2" :=
  (if c then v1 else v2)
  (at level 200, c, v1, v2 at level 200, only parsing) : general_if_scope.

Notation "'if' c 'return' t 'then' v1 'else' v2" :=
  (if c return t then v1 else v2)
  (at level 200, c, t, v1, v2 at level 200, only parsing) : general_if_scope.

Notation "'if' c 'as' x 'return' t 'then' v1 'else' v2" :=
  (if c as x return t then v1 else v2)
  (at level 200, c, t, v1, v2 at level 200, x ident, only parsing)
     : general_if_scope.

(**  Force boolean interpretation of simple if expressions.  **)

Declare Scope boolean_if_scope.
Delimit Scope boolean_if_scope with BOOL_IF.

Notation "'if' c 'return' t 'then' v1 'else' v2" :=
  (if c%bool is true in bool return t then v1 else v2) : boolean_if_scope.

Notation "'if' c 'then' v1 'else' v2" :=
  (if c%bool is true in bool return _ then v1 else v2) : boolean_if_scope.

Notation "'if' c 'as' x 'return' t 'then' v1 'else' v2" :=
  (if c%bool is true as x in bool return t then v1 else v2) : boolean_if_scope.

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
Notation "x : T" := (x : T)
  (at level 100, right associativity,
   format "'[hv' x '/ '  :  T ']'") : core_scope.

(**
 Allow the casual use of notations like nat * nat for explicit Type
 declarations. Note that (nat * nat : Type) is NOT equivalent to
 (nat * nat)%%type, whose inferred type is legacy type "Set".                **)
Notation "T : 'Type'" := (T%type : Type)
  (at level 100, only parsing) : core_scope.
(**  Allow similarly Prop annotation for, e.g., rewrite multirules. **)
Notation "P : 'Prop'" := (P%type : Prop)
  (at level 100, only parsing) : core_scope.

(**  Constants for abstract: and #[#: name #]# intro pattern  **)
Definition abstract_lock := unit.
Definition abstract_key := tt.

Definition abstract (statement : Type) (id : nat) (lock : abstract_lock) :=
  let: tt := lock in statement.

Notation "<hidden n >" := (abstract _ n _).
Notation "T (* n *)" := (abstract T n abstract_key).

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
  (at level 0, only parsing) : form_scope.

Notation "[ 'the' sT 'of' v ]" := (get ((fun s : sT => Put v (*coerce*)s s) _))
  (at level 0, only parsing) : form_scope.

(**
 The following are "format only" versions of the above notations. Since Coq
 doesn't provide this facility, we fake it by splitting the "the" keyword.
 We need to do this to prevent the formatter from being be thrown off by
 application collapsing, coercion insertion and beta reduction in the right
 hand side of the notations above.                                           **)

Notation "[ 'th' 'e' sT 'of' v 'by' f ]" := (@get_by _ sT f v _ _)
  (at level 0,  format "[ 'th' 'e'  sT  'of'  v  'by'  f ]") : form_scope.

Notation "[ 'th' 'e' sT 'of' v ]" := (@get _ sT v _ _)
  (at level 0, format "[ 'th' 'e'  sT  'of'  v ]") : form_scope.

(**
 We would like to recognize
Notation " #[# 'th' 'e' sT 'of' v : 'Type' #]#" := (@get Type sT v _ _)
  (at level 0, format " #[# 'th' 'e'  sT   'of'  v  :  'Type' #]#") : form_scope.
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

Notation "{ 'type' 'of' c 'for' s }" := (dependentReturnType c s)
  (at level 0, format "{ 'type'  'of'  c  'for'  s }") : type_scope.

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
  - unkeyed t wiil match any subterm that unifies with t, regardless of
    whether it displays the same head symbol as t.
  - unkeyed t a b will match any application of a term f unifying with t,
    to two arguments unifying with with a and b, repectively, regardless of
    apparent head symbols.
  - unkeyed x where x is a variable will match any subterm with the same
    type as x (when x would raise the 'indeterminate pattern' error).        **)

Notation unkeyed x := (let flex := x in flex).

(**  Ssreflect converse rewrite rule rule idiom.  **)
Definition ssr_converse R (r : R) := (Logic.I, r).
Notation "=^~ r" := (ssr_converse r) (at level 100) : form_scope.

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
    which treats all terms of the form locked t as equal and conpares their
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

Notation "[ 'unlockable' 'of' C ]" := (@Unlockable _ _ C (unlock _))
  (at level 0, format "[ 'unlockable'  'of'  C ]") : form_scope.

Notation "[ 'unlockable' 'fun' C ]" := (@Unlockable _ (fun _ => _) C (unlock _))
  (at level 0, format "[ 'unlockable'  'fun'  C ]") : form_scope.

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

(**  More accurate variant of unlock, and safer alternative to locked_withE.  **)
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
 for reductions occuring in the context, hence
   set here := pattern; vm_compute in (value of here)
 blows up at Qed time.                                        **)
Lemma abstract_context T (P : T -> Type) x :
  (forall Q, Q = P -> Q x) -> P x.
Proof. by move=> /(_ P); apply. Qed.

(*****************************************************************************)
(* Constants for under, to rewrite under binders using "Leibniz eta lemmas". *)

Module Type UNDER.
Parameter Under :
  forall (R : Type), R -> R -> Prop.
Parameter Under_from_eq :
  forall (T : Type) (x y : T), @Under T x y -> x = y.

(** [Over, over, over_done]: for "by rewrite over" *)
Parameter Over :
  forall (R : Type), R -> R -> Prop.
Parameter over :
  forall (T : Type) (x : T) (y : T), @Under T x y = @Over T x y.
Parameter over_done :
  forall (T : Type) (x : T), @Over T x x.
(* We need both hints below, otherwise the test-suite does not pass *)
Hint Extern 0 (@Over _ _ _) => solve [ apply over_done ] : core.
(* => for [test-suite/ssr/under.v:test_big_nested_1] *)
Hint Resolve over_done : core.
(* => for [test-suite/ssr/over.v:test_over_1_1] *)

(** [under_done]: for Ltac-style over *)
Parameter under_done :
  forall (T : Type) (x : T), @Under T x x.
Notation "''Under[' x ]" := (@Under _ x _)
  (at level 8, format "''Under['  x  ]").
End UNDER.

Module Export Under : UNDER.
Definition Under := @eq.
Lemma Under_from_eq (T : Type) (x y : T) :
  @Under T x y -> x = y.
Proof. by []. Qed.
Definition Over := Under.
Lemma over :
  forall (T : Type) (x : T) (y : T), @Under T x y = @Over T x y.
Proof. by []. Qed.
Lemma over_done :
  forall (T : Type) (x : T), @Over T x x.
Proof. by []. Qed.
Lemma under_done :
  forall (T : Type) (x : T), @Under T x x.
Proof. by []. Qed.
End Under.

Register Under as plugins.ssreflect.Under.
Register Under_from_eq as plugins.ssreflect.Under_from_eq.

Ltac beta_expand c e :=
  match e with
  | ?G ?z =>
    let T := type of z in
    match c with
    | context f [z] =>
      let b := constr:(fun x : T => ltac:(let r := context f [x] in refine r)) in
      rewrite -{1}[c]/(b z); beta_expand b G
    | (* constante *) _ =>
      let b := constr:(fun x : T => ltac:(exact c)) in
      rewrite -{1}[c]/(b z); beta_expand b G
    end
  | ?G => idtac
  end.

Ltac unify_helper :=
  move=> *;
  lazymatch goal with
  | [ |- @Under _ ?c ?e ] =>
    beta_expand c e
  end.

Ltac over :=
  solve [ apply Under.under_done
        | by rewrite over
        | unify_helper; eapply Under.under_done
        ].

(* The 2 variants below wouldn't work on [test-suite/ssr/over.v:test_over_2_1]
   (2-var test case with evars).

Ltac over :=
  exact: Under.under_done.

Ltac over :=
  by rewrite over.
 *)
