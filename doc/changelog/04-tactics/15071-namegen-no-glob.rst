- **Changed:** Name generation no longer avoids names of references
  except for those from the current module and its ancestors (`#15071
  <https://github.com/coq/coq/pull/15071>`_, fixes `#3523
  <https://github.com/coq/coq/issues/3523>`_, by Gaëtan Gilbert).
  The old behaviour can be restored using :flag:`Avoid Local Imported Names`.
