- **Fixed:**
  Tactic `subst` over a section variable was failing if the section
  variable was only indirectly dependent in the goal
  (`#12143 <https://github.com/coq/coq/pull/12143>`_,
  by Hugo Herbelin; fixes `#12139 <https://github.com/coq/coq/pull/12139>`_).

- **Fixed:**
  Tactic `subst` over a section variable was not clearing the rewritten equality
  if the section variable was indirectly dependent in the goal
  (`#12143 <https://github.com/coq/coq/pull/12143>`_,
  by Hugo Herbelin; fixes `#10812 <https://github.com/coq/coq/pull/10812>`_).
