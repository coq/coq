(** [Print Assumptions] reports, for an axiom that a proof eliminates with an
    empty [match], WHERE the elimination happens: that is the [ax2ty] map of
    [Assumptions], and it is the only part of the command's answer that
    depends on how many times the traversal reaches a given subterm.

    A traversal that skips subterms it has already walked must not lose any of
    these: an elimination has to be reported in every constant it occurs in,
    once per occurrence, even when hash-consing has made two occurrences one
    subterm, and even when what distinguishes them is only the local context
    they sit under. *)

Axiom bad : False.

(** Two eliminations that differ: both are reported. *)

Lemma two_types : nat * bool.
Proof.
  exact (pair (match bad return nat with end) (match bad return bool with end)).
Qed.

Print Assumptions two_types.

(** The same elimination in two different constants: reported once for each,
    even though the two proofs share the subterm. *)

Lemma first : nat.
Proof. exact (match bad return nat with end). Qed.

Lemma second : nat.
Proof. exact (match bad return nat with end). Qed.

Definition both := pair first second.

Print Assumptions both.

(** The same elimination written twice in ONE proof.  Hash-consing makes that
    a single subterm, reached along two paths; both occurrences are reported. *)

Lemma twice : nat * nat.
Proof.
  exact (pair (match bad return nat with end) (match bad return nat with end)).
Qed.

Print Assumptions twice.

(** Also a single subterm -- both eliminations are [match bad return Rel 1] --
    but the two occurrences sit under different [let]s, so the types reported
    for them differ. *)

Definition contexts :=
  (let x := nat in match bad return x with end,
   let y := bool in match bad return y with end).

Print Assumptions contexts.

(** The [admit] of Stdlib.Compat.AdmitAxiom is this elimination, so the report
    is how one sees which goals were admitted.  Three goals of the SAME type
    are three occurrences and must stay three lines. *)

Ltac admit84 := clear; abstract case bad.

Lemma admitted_thrice : True /\ True /\ True.
Proof. split. admit84. split. admit84. admit84. Qed.

Print Assumptions admitted_thrice.

(** An axiom that is not eliminated this way carries no such report, ... *)

Axiom foo : nat.

Lemma plain : nat * nat.
Proof. exact (pair foo foo). Qed.

Print Assumptions plain.

(** ... and neither does [destruct], which goes through [False_ind]. *)

Lemma by_destruct : nat.
Proof. destruct bad. Qed.

Print Assumptions by_destruct.
