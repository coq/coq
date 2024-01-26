(lang dune 3.6)
(name coq)

; We use directory targets in documentation
(using directory-targets 0.1)

; We need this due to `(coq.pp )` declarations
(using coq 0.3)

(formatting
 (enabled_for ocaml))

(generate_opam_files true)

(license LGPL-2.1-only)
(maintainers "The Coq development team <coqdev@inria.fr>")
(authors "The Coq development team, INRIA, CNRS, and contributors")
; This generates bug-reports and dev-repo
(source (github coq/coq))
(homepage https://coq.inria.fr/)
(documentation "https://coq.github.io/doc/")
(version dev)

; Note that we use coq.opam.template to have dune add the correct opam
; prefix for configure; also note that we manually add the dune >= 3.6.1
; dependency due a dune bug preventing Coq to build in
; 3.6.0. Dune adds `dune >= 3.6` automatically, based on `(lang dune 3.6)`
; above, but that's not enough.
(package
 (name coq-core)
 (depends
  (dune (>= 3.6.1))
  (ocaml (>= 4.09.0))
  (ocamlfind (>= 1.8.1))
  (zarith (>= 1.11))
  (conf-linux-libc-dev (= :os "linux")))
 (depopts coq-native)
 (synopsis "The Coq Proof Assistant -- Core Binaries and Tools")
 (description "Coq is a formal proof management system. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

Typical applications include the certification of properties of
programming languages (e.g. the CompCert compiler certification
project, or the Bedrock verified low-level programming library), the
formalization of mathematics (e.g. the full formalization of the
Feit-Thompson theorem or homotopy type theory) and teaching.

This package includes the Coq core binaries, plugins, and tools, but
not the vernacular standard library.

Note that in this setup, Coq needs to be started with the -boot and
-noinit options, as will otherwise fail to find the regular Coq
prelude, now living in the coq-stdlib package."))

(package
 (name coq-stdlib)
 (depends
  (coq-core (= :version)))
 (depopts coq-native)
 (synopsis "The Coq Proof Assistant -- Standard Library")
 (description "Coq is a formal proof management system. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

Typical applications include the certification of properties of
programming languages (e.g. the CompCert compiler certification
project, or the Bedrock verified low-level programming library), the
formalization of mathematics (e.g. the full formalization of the
Feit-Thompson theorem or homotopy type theory) and teaching.

This package includes the Coq Standard Library, that is to say, the
set of modules usually bound to the Coq.* namespace."))

(package
 (name coqide-server)
 (depends
  (coq-core (= :version)))
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
  (ocamlfind :build)
  (conf-findutils :build)
  conf-adwaita-icon-theme
  (coqide-server (= :version))
  (cairo2 (>= 0.6.4))
  (lablgtk3-sourceview3 (>= 3.1.2)))
 (synopsis "The Coq Proof Assistant --- GTK3 IDE")
 (description "Coq is a formal proof management system. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

This package provides the CoqIDE, a graphical user interface for the
development of interactive proofs."))

(package
 (name coq-doc)
 (license "OPUBL-1.0")
 (depends
  (conf-python-3 :build)
  (coq (and :build (= :version))))
 (synopsis "The Coq Proof Assistant --- Reference Manual")
 (description "Coq is a formal proof management system. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

This package provides the Coq Reference Manual."))

(package
 (name coq)
 (depends
  (coq-core (= :version))
  (coq-stdlib (= :version))
  (coqide-server (= :version))
  (ounit2 :with-test)
  (conf-python-3 :with-test)
  (conf-time :with-test))
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
