.. _asynchronousandparallelproofprocessing:

Asynchronous and Parallel Proof Processing
==========================================

:Author: Enrico Tassi

This chapter explains how proofs can be asynchronously processed by
Coq. This feature improves the reactivity of the system when used in
interactive mode via CoqIDE. In addition, it allows Coq to take
advantage of parallel hardware when used as a batch compiler by
decoupling the checking of statements and definitions from the
construction and checking of proofs objects.

This feature is designed to help dealing with huge libraries of
theorems characterized by long proofs. In the current state, it may
not be beneficial on small sets of short files.

This feature has some technical limitations that may make it
unsuitable for some use cases.

For example, in interactive mode, some errors coming from the kernel
of Coq are signaled late. The type of errors belonging to this
category are universe inconsistencies.

At the time of writing, only opaque proofs (ending with :cmd:`Qed` or
:cmd:`Admitted`) can be processed asynchronously.

Finally, asynchronous processing is disabled when running CoqIDE in
Windows. The current implementation of the feature is not stable on
Windows. It can be enabled, as described below at :ref:`interactive-mode`,
though doing so is not recommended.

.. _proof-annotations:

Proof annotations
----------------------

To process a proof asynchronously Coq needs to know the precise
statement of the theorem without looking at the proof. This requires
some annotations if the theorem is proved inside a Section (see
Section :ref:`section-mechanism`).

When a :ref:`section <section-mechanism>` ends, Coq looks at the proof object to decide which
section variables are actually used and hence have to be quantified in
the statement of the theorem. To avoid making the construction of
proofs mandatory when ending a section, one can start each proof with
the :cmd:`Proof using` command (Section :ref:`proof-editing-mode`) that
declares which section variables the theorem uses.

The presence of :cmd:`Proof using` is needed to process proofs asynchronously
in interactive mode.

It is not strictly mandatory in batch mode if it is not the first time
the file is compiled and if the file itself did not change. When the
proof does not begin with :cmd:`Proof using`, the system records in an
auxiliary file, produced along with the ``.vo`` file, the list of section
variables used.

If a theorem has an incorrect annotation that omits a needed variable, you may see
a message like this:

   .. code-block::

      File "./Pff.v", line 2372, characters 0-4:
      Error: The following section variable is used but not declared:
      precisionNotZero.

      You can either update your proof to not depend on precisionNotZero, or you can
      update your Proof line from
      Proof using FtoRradix b pGivesBound precision radix radixMoreThanOne radixMoreThanZERO
      to
      Proof using FtoRradix b pGivesBound precision precisionNotZero radix radixMoreThanOne radixMoreThanZERO

In this case the minimal annotation suggested by the :flag:`Suggest Proof Using` flag is
`Print Using pGivesBound precisionNotZero radixMoreThanOne.`  The other variables
in the suggestion are unnecessary because they will be transitively included from
the minimal annotation.

Alternatively, if the :cmd:`Proof using` included unneeded variables, they become
extra parameters of the theorem, which may generate errors.
This :ref:`example <example-print-using>` shows an example of an unneeded variable.
One possible error is `(in proof <theorem name>) Attempt to save an incomplete proof`,
which may indicate that the named theorem refers to an an earlier theorem that has
an incorrect annotation.

Automatic suggestion of proof annotations
`````````````````````````````````````````

The :flag:`Suggest Proof Using` flag makes Coq suggest, when a :cmd:`Qed`
command is processed, a correct proof annotation. It is up to the user
to modify the proof script accordingly.


Proof blocks and error resilience
--------------------------------------

In interactive
mode Coq is able to completely check a document containing errors
instead of bailing out at the first failure.

Two kind of errors are handled: errors occurring in
commands and errors occurring in proofs.

To properly recover from a failing tactic, Coq needs to recognize the
structure of the proof in order to confine the error to a sub proof.
Proof block detection is performed by looking at the syntax of the
proof script (i.e. also looking at indentation). Coq comes with four
kind of proof blocks, and an ML API to add new ones.

:curly: blocks are delimited by { and }, see Chapter :ref:`proofhandling`
:par: blocks are atomic, i.e. just one tactic introduced by the `par:`
  goal selector
:indent: blocks end with a tactic indented less than the previous one
:bullet: blocks are delimited by two equal bullet signs at the same
  indentation level

Caveats
````````

When a command fails the subsequent error messages may be
bogus, i.e. caused by the first error. Error resilience for
commands can be switched off by passing ``-async-proofs-command-error-resilience off``
to CoqIDE.

An incorrect proof block detection can result into an incorrect error
recovery and hence in bogus errors. Proof block detection cannot be
precise for bullets or any other non-well parenthesized proof
structure. Error resilience can be turned off or selectively activated
for any set of block kind passing to CoqIDE one of the following
options:

- ``-async-proofs-tactic-error-resilience off``
- ``-async-proofs-tactic-error-resilience all``
- ``-async-proofs-tactic-error-resilience`` :n:`{*, blocktype}`

Valid proof block types are: “curly”, “par”, “indent”, and “bullet”.

.. _interactive-mode:

Interactive mode
---------------------

.. todo: How about PG and coqtail?

CoqIDE and VsCoq support asynchronous proof processing.

When CoqIDE is started and async mode is enabled, two or more Coq processes
are created. The master one
follows the user, giving feedback as soon as possible by skipping
proofs, which are delegated to the worker processes. The worker processes
asynchronously processes the proofs.  The *Jobs panel* in the main CoqIDE
window shows the status of each worker process.
If a proof contains an error, it's reported in red in the label of
the very same button, that can also be used to see the list of errors
and jump to the corresponding line.

If a proof is processed asynchronously the corresponding :cmd:`Qed` command
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

The number of worker processes can be increased by passing CoqIDE
the ``-async-proofs-j n`` flag. Note that the memory consumption increases too,
since each worker requires the same amount of memory as the master
process. Also note that increasing the number of workers may reduce
the reactivity of the master process to user commands.

To disable this feature, one can pass the ``-async-proofs off`` flag to
CoqIDE. Conversely, on Windows, where the feature is disabled by
default, pass the ``-async-proofs on`` flag to enable it.

Proofs that are known to take little time to process are not delegated
to a worker process. The threshold can be configured with
``-async-proofs-delegation-threshold``. Default is 0.03 seconds.
