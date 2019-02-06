(**
A Quick Tour of Coq
by Michael Nahas, and others

------------------------
Special thanks to Brian Kernighan who suggested this.
*)

(** * Introduction *)
(**
Welcome to Coq / Bienvenue a Coq!

This document tries to answer the questions "What is Coq?" and "Is Coq
for you?"  It starts with a quick description of the program.  It then does
two proofs: a math proof and a proof that a program correctly matches
a mathematical description. Lastly, if Coq is right for you, it lists
resources that will help you get started.
*)
(** ** "What is Coq?" *)
(**
Coq is a proof assistant.

A proof assistant helps you write a formal proof.  That is, a proof
that can be read by a computer program and checked for correctness.

In fact, Coq will prevent you from ever writing an incorrect proof.
If you try to write one, it will spit out an error just like a
compiler or interpreter would, if you gave it an incorrect program.
Below, you'll see two of Coq's proofs --- you can try modifying the
proofs, if you want to see the errors.

Coq is based on Type Theory.  Type Theory is related to the type
systems, which is what a compiler or interpreter would use to detect
that you tried to add a string and boolean.  Compared to most
programming languages, Coq's Type Theory is much more expressive and
the type-checker much more powerful.  It will often figure out the
types for you.  For mathematicians, Type Theory is slightly different
from Set Theory, but you should be able to do anything in Coq that you
could do with Set Theory.

Coq is open-source software written by the nice people at INRIA.
INRIA is a research institution funded by the French government.  Vive
la France!  (Actually, the writers come from all over, so there are
many countries to thank.  See the Coq website for details.)

*)

(** * Math Proof *)
(**
To demonstrate Coq, we'll prove the classic theorem: the square root
of 2 is not a rational number.  I'm taking the theorem and proof from
Walter Rudin's classic textbook "Principles of Mathematical Analysis".
(It's on page 2 of my third edition.)  The theorem is stated:

"We now show that the equation p^2 = 2 is not satisfied by any
rational p."

We want to turn this statement into a formal statement and then prove
it correct.  Turning it into a formal statement will take a number of
steps.  The first is to take the human language out of the statement
and replace it with logical operators.  That might look something like
this.

"not (exists p in rationals, p^2 = 2)"

We can't put this into Coq's notation until we import the definition
of rational and the operators on them.  So, let's do that import.
*)

(* REPLACE WITH IMPORT *)

(**
LIST THINGS IMPORTED THAT WILL BE USED LATER

We can now state the theorem we want to prove.
*)

STATE THEOREM

(**
We enter Coq's proving mode with the command "Proof."
*)
Proof.
(**

Coq's proving mode keeps track of the "subgoals" we have yet to prove.
For each subgoal, it keeps the "hypotheses", which are things we know
are true or have assumed to be true.  Right after the "Proof."
command, we have only one subgoal --- the theorem --- and know nothing
to be true.

If you're looking at this file in CoqIDE or Proof General, you can see
the list of subgoals and the "context" of the current subgoal.  The
"context" is the name for all the hypotheses.  To view this, move the
cursor after the line "Proof." and then go to the "Navigation" menu
and select "go to".  In the upper-right panel of CoqIDE, you should
see something like:

INSERT SUBGOAL CONTEXT

Rudin's proof starts "If there were such a p" and ends with "Hence,
[p^2=2] is impossible for rational p".  This is a proof by
contradiction.  We prove this by assuming a rational p exists and
showing that it leads to contradiction.  We assume p exists using
these commands.
*)

(*
If you use CoqIDE to examine the state of the proof after these
commands, you'll see the subgoal has changed and that we have a new
hypothesis, p, which we've assumed exists.

The commands inside the proof mode are called "tactics".  There are a
large number of tactics and this document doesn't try to explain them
all.  Some tactics do very tiny changes to the proof's state.  Some
invoke automatic theorem provers that can take care of most trivial
proofs and many complicated ones.

The next line at the top of Rudin's proof is "we could write p=m/n
where m and n are integers ...".  We have a rational p, which we know
contains 2 integers, the numerator and the demoninator.  One of Coq's
tactics is "destruct" which creates a new subgoal for every different
way of constructing a term like p.  In this case, a rational, has only
one way of being constructed, so we only end up with one new subgoal,
but later we'll see a different case.

*)
DESTRUCT P INTO M AND N

(*
REST OF PROOF:
"If there were such a p, we could write p = m/n where m and n are
integers that are not both even.  Let us assume this is done.  Then
[p^2=2] implies m^2 = 2n^2.  This shows m^2 is even.  Hence m is even
(if m were odd, m^2 would be odd) and so m^2 is divisible by 4.  If
follows that the right side of [m^2 = 2n^2] is divisible by 4, so that
n^2 is even, which imples that n is even.

The assumption that [p^2=2] holds thus leads to the conclusion that
both m and n are even, contrary to our choice of m and n.  Hence,
[p^2=2] is impossible for rational p."

*)

(**
COMMENT ON PROOF.

COMMENT ON WHAT KINDS OF MATHEMATICIANS ARE LIKELY TO USE COQ
*)

(** * Proving a Program Correct *)
(**
In this section, we'll define what ordered linked list is and then
prove that some code produces an ordered linked list. (I'd love to
define a sorted linked list, but that requires proving the linked list
is ordered AND a permutation of another linked list, and I wanted to
keep this short.

We start by importing Coq's definitions of a linked list.
*)
ADD IMPORT STATEMENTS
(**

Coq's standard library has a type called List, but it is special.
List is polymorphic: it requires a type parameter to say what kind of
data it stores.  Thus, "List int" is a list that store integers.  You
don't always have to write "int" because, in most cases, Coq's
powerful typechecker can figure out what type you're storing in the
List.

Coq's defines two ways to make a linked list.  One ways is use "nil",
which takes no parameters.  Without any data, "nil" is an empty list.
The other way to create a linked list is to use "cons".  "cons" takes
a piece of data and another list, and represents a new node added to
the front of the list and storing that piece of data.

Thus, (cons 2 (cons 1 nil)) is a list containing a 2 and a 1.

Coq can define operators for types.  This allowed us to use "+" and
"*" with rational numbers, when we were really calling the functions
"add" and "mult".  Coq defines operators for lists.  In fact, the next
two Coq statements print out the same values.
*)

Print (cons 2 (cons 1 nil)).
Print 2 :: 1 :: nil

(**
A ordered linked list is a new type.  The code below declares the new
type, OrderedList and the 3 ways to construct one.
*)

Inductive OrderedList `{SortData} : list carrier -> Prop :=
  | OL_nil : OrderedList []
  | OL_cons1 a : OrderedList [a]
  | OL_consn a b l :
    leb a b = true -> OrderedList (b :: l) -> OrderedList (a :: b :: l).

(**
EXPLAIN THE 3 CONSTRUCTORS

To create an ordered list, we'll use insertion sort.
*)

(** insert a single element into a list *)
Fixpoint insert `{SortData} (n : carrier) (lst : list carrier)
  : list carrier
:=
  match lst with
    | nil => n :: lst
    | x :: rest =>
      match leb n x with
        | true => n :: x :: rest
        | false => x :: (insert n rest)
      end
  end.

(**
EXPLAIN match ... with ... end
*)

(** sort an entire list using insertion sort *)
Fixpoint insertion_sort `{SortData} (lst : list carrier)
  : list carrier
:=
  match lst with
    | nil => nil
    | x :: rest => (insert x (insertion_sort rest))
  end.

(**
SAY WE CAN DEMONSTRATE ITS OPERATION WITH COMPUTE
*)
Compute insertion_sort (1 :: 3 :: 2 :: nil).

(**
SAY PROOFS ARE COMING
*)

Theorem insert_preserves_OrderedList : forall {sd : SortData} (n : carrier) (lst : list carrier)
    (s : OrderedList lst)
  , OrderedList (insert n  lst).
INSERT PROOF

Theorem insertion_sort_creates_OrderedList {sd : SortData} (lst : list carrier) : OrderedList (insertion_sort lst).
INSERT PROOF

(**
MENTION HOW SECOND PROOF REFERENCES FIRST.

MENTION HOW AUTOMATION KEEPS PROOF SHORT

DISCUSS WHICH PROGRAMMERS WILL WANT TO USE COQ
*)


(** * Further learning *)

COPY FROM Zimmi48
