- **Fixed:** interaction of Program's obligation state and modules and
  sections: obligations started in a parent module or section are not
  available to be solved until the submodules and subsections are
  closed (`#14780 <https://github.com/coq/coq/pull/14780>`_, fixes
  `#14446 <https://github.com/coq/coq/issues/14446>`_, by Gaëtan
  Gilbert).
