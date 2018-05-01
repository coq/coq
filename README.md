How to write plugins in Coq
===========================

  * tuto0 : package a ml4 file in a plugin, organize a `Makefile`, `_CoqProject`
    Example of syntax to add a new toplevel command
    Example of function call to print a simple message.
    To use it:

    `cd tuto0; make`
    `coqtop -I src`

    Dans la session Coq, taper `Require ML Module "tuto0_plugin". HelloWorld.`
