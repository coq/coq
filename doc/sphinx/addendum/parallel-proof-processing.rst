.. _asynchronousandparallelproofprocessing:

Asynchronous and Parallel Proof Processing
==========================================

:Author: Enrico Tassi

This chapter explains how proofs can be asynchronously processed by
|Coq|. This feature improves the reactivity of the system when used in
interactive mode via |CoqIDE|. In addition, it allows |Coq| to take
advantage of parallel hardware when used as a batch compiler by
decoupling the checking of statements and definitions from the
construction and checking of proofs objects.

This feature is designed to help dealing with huge libraries of
theorems characterized by long proofs. In the current state, it may
not be beneficial on small sets of short files.

This feature has some technical limitations that may make it
unsuitable for some use cases.

For example, in interactive mode, some errors coming from the kernel
of |Coq| are signaled late. The type of errors belonging to this
category are universe inconsistencies.

At the time of writing, only opaque proofs (ending with ``Qed`` or
``Admitted``) can be processed asynchronously.

Finally, asynchronous processing is disabled when running |CoqIDE| in
Windows. The current implementation of the feature is not stable on
Windows. It can be enabled, as described below at :ref:`interactive-mode`,
though doing so is not recommended.

Proof annotations
----------------------

To process a proof asynchronously |Coq| needs to know the precise
statement of the theorem without looking at the proof. This requires
some annotations if the theorem is proved inside a Section (see
Section :ref:`section-mechanism`).

When a section ends, |Coq| looks at the proof object to decide which
section variables are actually used and hence have to be quantified in
the statement of the theorem. To avoid making the construction of
proofs mandatory when ending a section, one can start each proof with
the ``Proof using`` command (Section :ref:`proof-editing-mode`) that
declares which section variables the theorem uses.

The presence of ``Proof`` using is needed to process proofs asynchronously
in interactive mode.

It is not strictly mandatory in batch mode if it is not the first time
the file is compiled and if the file itself did not change. When the
proof does not begin with Proof using, the system records in an
auxiliary file, produced along with the `.vo` file, the list of section
variables used.

Automatic suggestion of proof annotations
`````````````````````````````````````````

The flag :flag:`Suggest Proof Using` makes |Coq| suggest, when a ``Qed``
command is processed, a correct proof annotation. It is up to the user
to modify the proof script accordingly.


Proof blocks and error resilience
--------------------------------------

|Coq| 8.6 introduced a mechanism for error resilience: in interactive
mode |Coq| is able to completely check a document containing errors
instead of bailing out at the first failure.

Two kind of errors are supported: errors occurring in vernacular
commands and errors occurring in proofs.

To properly recover from a failing tactic, |Coq| needs to recognize the
structure of the proof in order to confine the error to a sub proof.
Proof block detection is performed by looking at the syntax of the
proof script (i.e. also looking at indentation). |Coq| comes with four
kind of proof blocks, and an ML API to add new ones.

:curly: blocks are delimited by { and }, see Chapter :ref:`proofhandling`
:par: blocks are atomic, i.e. just one tactic introduced by the `par:`
  goal selector
:indent: blocks end with a tactic indented less than the previous one
:bullet: blocks are delimited by two equal bullet signs at the same
  indentation level

Caveats
````````

When a vernacular command fails the subsequent error messages may be
bogus, i.e. caused by the first error. Error resilience for vernacular
commands can be switched off by passing ``-async-proofs-command-error-resilience off``
to |CoqIDE|.

An incorrect proof block detection can result into an incorrect error
recovery and hence in bogus errors. Proof block detection cannot be
precise for bullets or any other non well parenthesized proof
structure. Error resilience can be turned off or selectively activated
for any set of block kind passing to |CoqIDE| one of the following
options:

- ``-async-proofs-tactic-error-resilience off``
- ``-async-proofs-tactic-error-resilience all``
- ``-async-proofs-tactic-error-resilience`` :n:`{*, blocktype}`

Valid proof block types are: “curly”, “par”, “indent”, and “bullet”.

.. _interactive-mode:

Interactive mode
---------------------

At the time of writing the only user interface supporting asynchronous
proof processing is |CoqIDE|.

When |CoqIDE| is started, two |Coq| processes are created. The master one
follows the user, giving feedback as soon as possible by skipping
proofs, which are delegated to the worker process. The worker process,
whose state can be seen by clicking on the button in the lower right
corner of the main |CoqIDE| window, asynchronously processes the proofs.
If a proof contains an error, it is reported in red in the label of
the very same button, that can also be used to see the list of errors
and jump to the corresponding line.

If a proof is processed asynchronously the corresponding Qed command
is colored using a lighter color than usual. This signals that the
proof has been delegated to a worker process (or will be processed
lazily if the ``-async-proofs lazy`` option is used). Once finished, the
worker process will provide the proof object, but this will not be
automatically checked by the kernel of the main process. To force the
kernel to check all the proof objects, one has to click the button
with the gears (Fully check the document) on the top bar.
Only then all the universe constraints are checked.

Caveats
```````

The number of worker processes can be increased by passing |CoqIDE|
the ``-async-proofs-j n`` flag. Note that the memory consumption increases too,
since each worker requires the same amount of memory as the master
process. Also note that increasing the number of workers may reduce
the reactivity of the master process to user commands.

To disable this feature, one can pass the ``-async-proofs off`` flag to
|CoqIDE|. Conversely, on Windows, where the feature is disabled by
default, pass the ``-async-proofs on`` flag to enable it.

Proofs that are known to take little time to process are not delegated
to a worker process. The threshold can be configured with
``-async-proofs-delegation-threshold``. Default is 0.03 seconds.

Batch mode
---------------

When |Coq| is used as a batch compiler by running `coqc` or `coqtop`
-compile, it produces a `.vo` file for each `.v` file. A `.vo` file contains,
among other things, theorem statements and proofs. Hence to produce a
.vo |Coq| need to process all the proofs of the `.v` file.

The asynchronous processing of proofs can decouple the generation of a
compiled file (like the `.vo` one) that can be loaded by ``Require`` from the
generation and checking of the proof objects. The ``-quick`` flag can be
passed to `coqc` or `coqtop` to produce, quickly, `.vio` files.
Alternatively, when using a Makefile produced by `coq_makefile`,
the ``quick`` target can be used to compile all files using the ``-quick`` flag.

A `.vio` file can be loaded using ``Require`` exactly as a `.vo` file but
proofs will not be available (the Print command produces an error).
Moreover, some universe constraints might be missing, so universes
inconsistencies might go unnoticed. A `.vio` file does not contain proof
objects, but proof tasks, i.e. what a worker process can transform
into a proof object.

Compiling a set of files with the ``-quick`` flag allows one to work,
interactively, on any file without waiting for all the proofs to be
checked.

When working interactively, one can fully check all the `.v` files by
running `coqc` as usual.

Alternatively one can turn each `.vio` into the corresponding `.vo`. All
.vio files can be processed in parallel, hence this alternative might
be faster. The command ``coqtop -schedule-vio2vo 2 a b c`` can be used to
obtain a good scheduling for two workers to produce `a.vo`, `b.vo`, and
`c.vo`. When using a Makefile produced by `coq_makefile`, the ``vio2vo`` target
can be used for that purpose. Variable `J` should be set to the number
of workers, e.g. ``make vio2vo J=2``. The only caveat is that, while the
.vo files obtained from `.vio` files are complete (they contain all proof
terms and universe constraints), the satisfiability of all universe
constraints has not been checked globally (they are checked to be
consistent for every single proof). Constraints will be checked when
these `.vo` files are (recursively) loaded with ``Require``.

There is an extra, possibly even faster, alternative: just check the
proof tasks stored in `.vio` files without producing the `.vo` files. This
is possibly faster because all the proof tasks are independent, hence
one can further partition the job to be done between workers. The
``coqtop -schedule-vio-checking 6 a b c`` command can be used to obtain a
good scheduling for 6 workers to check all the proof tasks of `a.vio`,
`b.vio`, and `c.vio`. Auxiliary files are used to predict how long a proof
task will take, assuming it will take the same amount of time it took
last time. When using a Makefile produced by coq_makefile, the
``checkproofs`` target can be used to check all `.vio` files. Variable `J`
should be set to the number of workers, e.g. ``make checkproofs J=6``. As
when converting `.vio` files to `.vo` files, universe constraints are not
checked to be globally consistent. Hence this compilation mode is only
useful for quick regression testing and on developments not making
heavy use of the `Type` hierarchy.

Limiting the number of parallel workers
--------------------------------------------

Many |Coq| processes may run on the same computer, and each of them may
start many additional worker processes. The `coqworkmgr` utility lets
one limit the number of workers, globally.

The utility accepts the ``-j`` argument to specify the maximum number of
workers (defaults to 2). `coqworkmgr` automatically starts in the
background and prints an environment variable assignment
like ``COQWORKMGR_SOCKET=localhost:45634``. The user must set this variable
in all the shells from which |Coq| processes will be started. If one
uses just one terminal running the bash shell, then
``export ‘coqworkmgr -j 4‘`` will do the job.

After that, all |Coq| processes, e.g. `coqide` and `coqc`, will respect the
limit, globally.
