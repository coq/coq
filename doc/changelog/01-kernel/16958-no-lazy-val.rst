- **Fixed:**
  inconsistency linked to ``vm_compute``. The fix removes a vulnerable cache which may result in slowdowns when ``vm_compute`` is used repeatedly, if you encounter such slowdowns please report your use case
  (`#16958 <https://github.com/coq/coq/pull/16958>`_,
  fixes `#16957 <https://github.com/coq/coq/issues/16957>`_,
  by Gaëtan Gilbert).
