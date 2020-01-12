- **Fixed:**
  Implicit arguments were ignored in :cmd:`Context`

  .. warning::

     This has been observed to be a breaking change in a couple of
     projects. This can be fixed either by removing the implicit
     argument annotations, or by taking into account the new presence of
     implicit arguments for the corresponding declarations. The first
     approach provides backward compatibility. If needed, the second
     approach can be made backward compatible too by adding an extra
     (eventually superflous) :n:`Local Arguments` declaration right
     after :cmd:`Context`.

  (`#11390 <https://github.com/coq/coq/pull/11390>`_,
  by Hugo Herbelin, fixing `#9412 <https://github.com/coq/coq/pull/9412>`_).
