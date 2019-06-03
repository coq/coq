How to write plugins in Coq
===========================
  # Working environment

  In addition to installing OCaml and Coq, it can help to install several tools for development.
  
  ## Merlin

  These instructions use [OPAM](http://opam.ocaml.org/doc/Install.html)

```shell
opam install merlin               # prints instructions for vim and emacs
```

  ## This tutorial

```shell
cd plugin_tutorials/tuto0
make .merlin                # run before opening .ml files in your editor
make                        # build
```
  
  
  
  # tuto0 : basics of project organization
  package a ml4 file in a plugin, organize a `Makefile`, `_CoqProject`
  - Example of syntax to add a new toplevel command
  - Example of function call to print a simple message
  - Example of function call to print a simple warning
  - Example of function call to raise a simple error to the user
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

  You can also modify and run `theories/Demo.v`.

  # tuto1 : OCaml to Coq communication
  Explore the memory of Coq, modify it
  - Commands that take arguments: strings, integers, symbols, expressions of the calculus of constructions
  - Examples of using environments correctly
  - Examples of using state (the evar_map) correctly
  - Commands that interact with type-checking in Coq
  - A command that checks convertibility between two terms
  - A command that adds a new definition or theorem
  - A command that uses a name and exploits the existing definitions or theorems
  - A command that exploits an existing ongoing proof
  - A command that defines a new tactic

  Compilation and loading must be performed as for `tuto0`.
  
  # tuto2 : OCaml to Coq communication
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
