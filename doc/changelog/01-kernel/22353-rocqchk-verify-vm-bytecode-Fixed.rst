- **Fixed:**
  ``rocqchk`` with ``-bytecode-compiler yes`` no longer trusts the VM bytecode
  serialized in a ``.vo``: it does not read the ``vmlibrary`` segment at all, and
  recompiles the bytecode of every constant from the body it typechecks, so that
  the code the VM runs and the checked body agree by construction; a crafted
  ``.vo`` whose serialized bytecode disagreed with its body could previously make
  a VM conversion prove ``False`` and still pass the checker
  (`#22353 <https://github.com/rocq-prover/rocq/pull/22353>`_,
  fixes `#22352 <https://github.com/rocq-prover/rocq/issues/22352>`_,
  by Archana Burra and Jason Gross).
