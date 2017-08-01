Known Issues in Coq
===================

> Perfection is achieved, not when there is nothing more to add, but when there is nothing left to take away.

## Known Issues in Coq 8.7

- Parallel Proof processing is disabled by default in Windows. You can
  reenable it with the `-async-proofs on` command line option, but it
  may be unstable. [BZ#5225](https://coq.inria.fr/bugs/show_bug.cgi?id=5225)
- The `Require` command is not properly supported inside proofs; also,
  backtracking such command may not undo its effects or create other
  issues. We recommend users to group all the `Require`s at the
  beginning of the document.
- The `abstract` tactic may be fragile in certain situations, for
  example inside a nested proof. We recommend using it only in
  top-level proofs.
- Interrupting Coq when using the XML protocol may produce ill-formed
  XML. [BZ#5192](https://coq.inria.fr/bugs/show_bug.cgi?id=5192)
- There are some known issues with the XML protocol, we recommend you
  get in touch with the developers if you plan to use it.

### Known Issues in Coq 8.7 beta1, [to be solved before 8.7 final]:

- CoqIDE: Printing of terms may be slow [to be solved before 8.7 final]
- CoqIDE: certain panel sizes may cause a loop: resizing the panel should solve the issue.

## Known Issues in Coq 8.6

- The `abstract` tactic may be fragile in certain situations, for
  example inside a nested proof. We recommend using it only in
  top-level proofs.
- The `Require` command is not properly supported inside proofs; also,
  backtracking such command may not undo its effects or create other
  issues. We recommend users to group all the `Requires` at the
  beginning of the document.
- Parallel Proof processing may be unstable in Windows. If you
  encounter problems, use the `-async-proofs off` command line option.
- Interrupting Coq when using the XML protocol may produce ill-formed
  XML.
