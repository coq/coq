How to write plugins in Coq
===========================
  # Working environment : merlin, tuareg (open question)
  
  ## OCaml & related tools

  These instructions use [OPAM](http://opam.ocaml.org/doc/Install.html)

```shell
opam init --root=$PWD/CIW2018 --compiler=4.06.0 -j2
eval `opam config env --root=$PWD/CIW2018`
opam install camlp5 ocamlfind num # Coq's dependencies
opam install lablgtk              # Coqide's dependencies (optional)
opam install merlin               # prints instructions for vim and emacs
```

  ## Coq

```shell
git clone git@github.com:coq/coq.git
cd coq
./configure -profile devel
make -j2
cd ..
export PATH=$PWD/coq/bin:$PATH
```

  ## This tutorial

```shell
git clone git@github.com:ybertot/plugin_tutorials.git
cd plugin_tutorials/tuto0
make .merlin                # run before opening .ml files in your editor
make                        # build
```
  
  
  
  # tuto0 : basics of project organization
  package a ml4 file in a plugin, organize a `Makefile`, `_CoqProject`
  - Example of syntax to add a new toplevel command
  - Example of function call to print a simple message
  - Example of syntax to add a simple tactic
      (that does nothing and prints a message)
  - To use it:

```bash
    cd tuto0; make
    coqtop -I src -R theories Tuto0
```

  In the Coq session type:
```coq
    Require Import Tuto0.Loader. HelloWorld.
```

  # tuto1 : Ocaml to Coq communication
  Explore the memory of Coq, modify it
  - Commands that take arguments: strings, symbols, expressions of the calculus of constructions
  - Commands that interact with type-checking in Coq
  - A command that adds a new definition or theorem
  - A command that uses a name and exploits the existing definitions
    or theorems
  - A command that exploits an existing ongoing proof
  - A command that defines a new tactic

  Compilation and loading must be performed as for `tuto0`.
  
  # tuto2 : Ocaml to Coq communication
  A more step by step introduction to writing commands
  - Explanation of the syntax of entries
  - Adding a new type to and parsing to the available choices
  - Handling commands that store information in user-chosen registers and tables

  Compilation and loading must be performed as for `tuto1`.

  # tuto3 : manipulating terms of the calculus of constructions
  Manipulating terms, inside commands and tactics.
  - Obtaining existing values from memory
  - Composing values
  - Verifying types
  - Using these terms in commands
  - Using these terms in tactics
  - Automatic proofs without tactics using type classes and canonical structures

  compilation and loading must be performed as for `tuto0`.
