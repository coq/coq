
(* Bug report 4844 (and 4824):
   The Haskell extraction was erroneously considering [Any] and
   [()] as convertible ([Tunknown] an [Tdummy] internally). *)

(* A value with inner logical parts.
   Its extracted type will be [Sum () ()]. *)

Definition semilogic : True + True := inl I.

(* Higher-order record, whose projection [ST] isn't expressible
   as an Haskell (or OCaml) type. Hence [ST] is extracted as the
   unknown type [Any] in Haskell. *)

Record SomeType := { ST : Type }.

Definition SomeTrue := {| ST := True |}.

(* A first version of the issue:
  [abstrSum] is extracted as [Sum Any Any], so an unsafeCoerce
  is required to cast [semilogic] into [abstrSum SomeTrue]. *)

Definition abstrSum (t : SomeType) := ((ST t) + (ST t))%type.

Definition semilogic' : abstrSum SomeTrue := semilogic.

(* A deeper version of the issue.
   In the previous example, the extraction could have reduced
   [abstrSum SomeTrue] into [True+True], solving the issue.
   It might do so in future versions. But if we put an inductive
   in the way, a reduction isn't helpful. *)

Inductive box (t : SomeType) := Box : ST t + ST t -> box t.

Definition boxed_semilogic : box SomeTrue :=
 Box SomeTrue semilogic.

Require Extraction.
Extraction Language Haskell.
Recursive Extraction semilogic' boxed_semilogic.
(* Warning! To fully check that this bug is still closed,
   you should run ghc on the extracted code:

Extraction "bug4844.hs" semilogic' boxed_semilogic.
ghc bug4844.hs

*)
