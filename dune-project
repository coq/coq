(lang dune 2.5)
(name coq)
(using coq 0.2)

(formatting
 (enabled_for ocaml))

; Pending on dune 2.8 as to avoid bug with dune subst
; see https://github.com/ocaml/dune/pull/3879 and
; https://github.com/ocaml/dune/pull/3879
; (generate_opam_files true)

(license LGPL-2.1-only)
(maintainers "The Coq development team <coqdev@inria.fr>")
(authors "The Coq development team, INRIA, CNRS, and contributors")
; This generates bug-reports and dev-repo
(source (github coq/coq))
(homepage https://coq.inria.fr/)
(documentation "https://coq.github.io/doc/")
(version dev)

; Note that we use coq.opam.template to have dune add the correct opam
; prefix for configure
(package
 (name coq)
 (depends
  (ocaml (>= 4.05.0))
  (dune  (>= 2.5.0))
  (ocamlfind (>= 1.8.1))
  (zarith (>= 1.10))
  (ounit2 :with-test))
 (synopsis "The Coq Proof Assistant")
 (description "Coq is a formal proof management system. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

Typical applications include the certification of properties of
programming languages (e.g. the CompCert compiler certification
project, or the Bedrock verified low-level programming library), the
formalization of mathematics (e.g. the full formalization of the
Feit-Thompson theorem or homotopy type theory) and teaching."))

(package
 (name coqide-server)
 (depends
  (dune (>= 2.5.0))
  (coq (= :version)))
 (synopsis "The Coq Proof Assistant, XML protocol server")
 (description "Coq is a formal proof management system. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

This package provides the `coqidetop` language server, an
implementation of Coq's [XML protocol](https://github.com/coq/coq/blob/master/dev/doc/xml-protocol.md)
which allows clients, such as CoqIDE, to interact with Coq in a
structured way."))

(package
 (name coqide)
 (depends
  (dune (>= 2.5.0))
  (coqide-server (= :version)))
 (synopsis "The Coq Proof Assistant --- GTK3 IDE")
 (description "Coq is a formal proof management system. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

This package provides the CoqIDE, a graphical user interface for the
development of interactive proofs."))

(package
 (name coq-doc)
 (license "OPL-1.0")
 (depends
  (dune (and :build (>= 2.5.0)))
  (conf-python-3 :build)
  (coq (and :build (= :version))))
 (synopsis "The Coq Proof Assistant --- Reference Manual")
 (description "Coq is a formal proof management system. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

This package provides the Coq Reference Manual."))

