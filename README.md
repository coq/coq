How to write plugins in Coq
===========================
  # Working environment : merlin, tuareg (open question)
  # tuto0 : basics of project organization
  * package a ml4 file in a plugin, organize a `Makefile`, `_CoqProject`
    - Example of syntax to add a new toplevel command
    - Example of function call to print a simple message.
    - To use it:

    `cd tuto0; make`
    `coqtop -I src -R theories Tuto0`

    In the Coq session type:  `Require Tuto0.Loader. HelloWorld.`

  # tuto1 : Ocaml to Coq communication
  * Explore the memory of Coq, modify it
    - Commands that take arguments: strings, symbols, expressions of the calculus of constructions
    - Commands that interact with type-checking in Coq
    - A command that adds a new definition or theorem
    - A command that uses a name and exploits the existing definitions
      or theorems
    - A command that exploits an existing ongoing proof
    - A commandthat defines a new tactic

