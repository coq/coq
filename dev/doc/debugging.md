Debugging from Coq toplevel using OCaml toplevel
======================================================

1. Launch bytecode version of Coq (`dune exec -- dev/shim/coqtop.byte`)
2. Access OCaml toplevel using vernacular command `Drop.`
3. Use `#trace` to tell which function(s) to trace,
   or type any other OCaml toplevel commands or OCaml expressions
4. Go back to Coq toplevel with `#quit;;` or `#go;;`
5. Test your Coq command and observe the result of tracing your functions
6. Freely switch from Coq to OCaml toplevels with `Drop.` and `#quit;;`/`#go;;`

> [!NOTE]
> To access plugin modules in the OCaml toplevel, you have to
> use names such as `Ltac_plugin__Tacinterp`.

> [!TIP]
> To remove high-level pretty-printing features (coercions,
> notations, ...), use `Set Printing All`. It will affect the `#trace`
> printers too.


Debugging with ocamldebug from Emacs or command line
====================================================

See [build-system.dune.md#ocamldebug](build-system.dune.md#ocamldebug)

Global gprof-based profiling
============================

Coq must be configured with option `-profile`.

1. Run native Coq which must end normally (use `Quit` or option `-batch`)
2. `gprof ./coqtop gmon.out`

Per function profiling
======================

See the documentation in `lib/newProfile.mli`.
