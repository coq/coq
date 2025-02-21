(lang dune 3.8)
(name rocq-prover)

; We use directory targets in documentation
(using directory-targets 0.1)

; We need this for when we use the dune.disabled files instead of our rule_gen
(using coq 0.8)

(formatting
 (enabled_for ocaml))

(generate_opam_files true)

(license LGPL-2.1-only)
(maintainers "The Rocq development team <coqdev@inria.fr>")
(authors "The Rocq development team, INRIA, CNRS, and contributors")
; This generates bug-reports and dev-repo
(source (github coq/coq))
(homepage https://coq.inria.fr/)
(documentation "https://coq.github.io/doc/")
(version dev)

; Note that we use coq.opam.template to have dune add the correct opam
; prefix for configure
(package
 (name rocq-runtime)
 (depends
  (ocaml (>= 4.09.0))
  (ocamlfind (>= 1.8.1))
  (zarith (>= 1.11))
  (conf-linux-libc-dev (= :os "linux")))
 (conflicts
  (coq (< 8.17))
  (coq-core (< 8.21)))
 (depopts rocq-native memprof-limits memtrace)
 (synopsis "The Rocq Prover -- Core Binaries and Tools")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

Typical applications include the certification of properties of
programming languages (e.g. the CompCert compiler certification
project, or the Bedrock verified low-level programming library), the
formalization of mathematics (e.g. the full formalization of the
Feit-Thompson theorem or homotopy type theory) and teaching.

This package includes the Rocq Prover core binaries, plugins, and tools, but
not the vernacular standard library.

Note that in this setup, Rocq needs to be started with the -boot and
-noinit options, as will otherwise fail to find the regular Rocq
prelude, now living in the rocq-core package."))

(package
 (name rocq-devtools)
 (depends
  (rocq-runtime (= :version))
   yojson
   camlzip)
 (synopsis "Development tools for Rocq")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

Typical applications include the certification of properties of
programming languages (e.g. the CompCert compiler certification
project, or the Bedrock verified low-level programming library), the
formalization of mathematics (e.g. the full formalization of the
Feit-Thompson theorem or homotopy type theory) and teaching.

This package includes tools to help when developing Rocq projects
(timelog2html)."))

(package
 (name coq-core)
 (depends
  (rocq-runtime (= :version)))
 (synopsis "Compatibility binaries for Coq after the Rocq renaming")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

Typical applications include the certification of properties of
programming languages (e.g. the CompCert compiler certification
project, or the Bedrock verified low-level programming library), the
formalization of mathematics (e.g. the full formalization of the
Feit-Thompson theorem or homotopy type theory) and teaching.

This package includes compatibility binaries to call Rocq
through previous Coq commands like coqc coqtop,..."))

(package
 (name rocq-core)
 (depends
  (rocq-runtime (= :version)))
 (synopsis "The Rocq Prover with its prelude")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

Typical applications include the certification of properties of
programming languages (e.g. the CompCert compiler certification
project, or the Bedrock verified low-level programming library), the
formalization of mathematics (e.g. the full formalization of the
Feit-Thompson theorem or homotopy type theory) and teaching.

This package includes the Rocq prelude, that is loaded automatically
by Rocq in every .v file, as well as other modules bound to the
Corelib.* and Ltac2.* namespaces."))

(package
 (name coqide-server)
 (depends
  (rocq-runtime (= :version)))
 (synopsis "The Rocq Prover, XML protocol server")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

This package provides the `coqidetop` language server, an
implementation of Rocq's [XML protocol](https://github.com/coq/coq/blob/master/dev/doc/xml-protocol.md)
which allows clients, such as RocqIDE, to interact with the Rocq Prover in a
structured way."))

(package
 (name rocqide)
 (depends
  (ocamlfind :build)
  (conf-findutils :build)
  conf-adwaita-icon-theme
  (coqide-server (= :version))
  (cairo2 (>= 0.6.4))
  (lablgtk3-sourceview3 (and (>= 3.1.2) (or (>= 3.1.5) (<> :os "windows")))))
 (synopsis "The Rocq Prover --- GTK3 IDE")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

This package provides the RocqIDE, a graphical user interface for the
development of interactive proofs."))

(package
 (name coq-doc)
 (license "OPUBL-1.0")
 (depends
  (conf-python-3 :build)
  (coq (and :build (= :version))))
 (synopsis "The Rocq Prover --- Reference Manual")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

This package provides the Rocq Reference Manual."))

(package
 (name rocq-prover)
 (allow_empty)
 (depends
  (rocq-core (= :version))
  rocq-stdlib
  (ounit2 :with-test)
  (conf-python-3 :with-test)
  (conf-time :with-test))
 (synopsis "The Rocq Prover with Stdlib")
 (description "The Rocq Prover is an interactive theorem prover, or proof assistant. It provides
a formal language to write mathematical definitions, executable
algorithms and theorems together with an environment for
semi-interactive development of machine-checked proofs.

Typical applications include the certification of properties of
programming languages (e.g. the CompCert compiler certification
project, or the Bedrock verified low-level programming library), the
formalization of mathematics (e.g. the full formalization of the
Feit-Thompson theorem or homotopy type theory) and teaching.

This package is a virtual package gathering the rocq-core and rocq-stdlib packages."))

(package
 (name coq)
 (allow_empty)
 (depends
  (rocq-prover (= :version))
  (coq-core (= :version))
  coq-stdlib
  (coqide-server (= :version)))
 (synopsis "Compatibility metapackage for Coq after the Rocq renaming"))
