- **Changed:**
  the requirement prefix of the standard library from ``Coq`` to
  ``Stdlib``. For backward compatibility with older versions of Coq
  ``Coq`` is immediatly translated to ``Stdlib`` with a warning. It is
  thus not recommended to name anything ``Coq`` or ``Coq.*``. When
  droping support for Coq <= 8.20, a simple script such as ``for f in
  $(find . -name "*.v") ; do sed -i $f -e 's/From Coq Require/From
  Stdlib Require/;s/Coq[.]\([a-zA-Z]\)/Stdlib[.]\1/g' ; done`` should
  be enough to adapt your code. Meanwhile, adding the two lines
  ``-arg -w -arg -deprecated-from-Coq`` and
  ``-arg -w -arg -deprecated-dirpath-Coq``
  to your ``_CoqProject`` will silence the warnings
  (`#19310 <https://github.com/coq/coq/pull/19310>`_,
  by Pierre Roux).
