- **Changed:**
  Configure will now detect the Dune version, and will correctly pass
  ``-etcdir`` and ``-docdir`` to the install procedure if Dune >= 2.9 is available.
  Note that the ``-docdir`` configure option now refers to root path for documentation.
  If you would like to install Coq documentation in ``foo/coq``, use
  ``-docdir foo``.
  (`#14844 <https://github.com/coq/coq/pull/14844>`_,
  by Emilio Jesus Gallego Arias).
