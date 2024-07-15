(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** N.B.: Lists inductively defined with a dependency on their length,
here called vectors, are popular in dependent type programming:
programs embed their specification and only programs are
manipulated. However, this currently requires mastering advanced
dependent type programming to simultaneously handle the list
manipulation and the specification of its length.

We recommend using lists bundled with, when needed, a proof about
their length rather than vectors. (Thanks to the proof irrelevance of
equality on [nat], any two bundlings of a same list are provably
equal.) This decouples the two aspects above, making it easy to write
code in Gallina and develop proofs with tactics.

Such an implementation can be found for instance in
https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/tuple.v
One can read more about this tuple type in section 7.1 of this book:
https://doi.org/10.5281/zenodo.4282710 .
In particular, this implementation comes with coercion and canonical
structures so that lists and tuples can be transparently mixed most of
the time. For instance, after [From mathcomp Require Import seq tuple.],
in [Context n1 n2 T (v1 : n1.-tuple T) (v2 : n2.-tuple T) (foo : (n1 + n2).-tuple T -> bool).]
one can write [Check foo (v1 ++ v2).], where [++] is the list concatenation,
and Coq will automatically elaborate it, as [Set Printing All.] would show,
to [foo (cat_tuple v1 v2)] where [cat_tuple] is the lifting of [++] on tuples.

Another representation can be found in
https://github.com/mit-plv/coqutil/blob/master/src/coqutil/Datatypes/HList.v
where tuples can be manipulated through the [of_list] and [to_list] functions.
This has to be done manually though as the library doesn't automate it.

To give an example of the difficulties faced with [Vector.t],
writing [VectorDef.rev] constitutes a good exercise. This proves
fairly tricky and requires reimplementing dependent type versions
of functions already written on lists (typing [Vector.rev] even
relies on a tail-recursive version of the addition on natural
numbers whose computational content structurally follows the one
of the auxiliary function [Vector.rev_append] from which
[Vector.rev] is defined; additionally, the computational content
is intertwined with some rewriting steps). In contrast, the
dependent pair encoding reuses functions and lemmas already
written on lists and the definition (called [rev_tuple] in
mathcomp's [tuple.v]) only needs the property that [rev]
preserves the length:

[[
Require Import List.

Record tuple_of (n : nat) T := Tuple
  { tval :> list T; tsize : length tval = n }.

Lemma rev_tupleP [T n] (t : tuple_of n T) : length (rev t) = n.
Proof. now rewrite length_rev, tsize. Qed.
Canonical rev_tuple T n (t : tuple_of n T) := Tuple n T (rev t) (rev_tupleP t).

(* The canonical instance allows to automatically elaborate tuples: *)
Section TestRevTuple.
Variables (T : Type) (n : nat) (t : tuple_of n T).
Check rev t : tuple_of n T.
]]

Thus lemmas about lists are enough in most cases. *)
Attributes warn(cats="stdlib vector", note="Using Vector.t is known to be technically difficult, see <https://github.com/coq/coq/blob/master/theories/Vectors/Vector.v>.").

(** Vectors.

   Initial Author: Pierre Boutillier
   Institution: PPS, INRIA 12/2010

Originally from the contribution bit vector by Jean Duprat (ENS Lyon).

Based on contents from Util/VecUtil of the CoLoR contribution *)

#[local] Set Warnings "-stdlib-vector".
Require Fin.
Require VectorDef.
Require VectorSpec.
Require VectorEq.
Include VectorDef.
Include VectorSpec.
Include VectorEq.
