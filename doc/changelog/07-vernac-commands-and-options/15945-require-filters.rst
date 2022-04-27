- **Added:** All commands which can import modules (e.g. ``Module
  Import M.``, ``Module F (Import X : T).``, ``Require Import M.``,
  etc) now support :token:`import_categories`. :cmd:`Require Import`
  and :cmd:`Require Export` also support :token:`filtered_import`.
  (`#15945 <https://github.com/coq/coq/pull/15945>`_, fixes `#14872
  <https://github.com/coq/coq/issues/14872>`_, by Gaëtan Gilbert).
