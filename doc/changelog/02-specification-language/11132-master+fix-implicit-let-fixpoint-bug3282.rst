- Fixed bugs sometimes preventing to define valid (co)fixpoints with implicit arguments
  in the presence of local definitions, see `#3282 <https://github.com/coq/coq/issues/3282>`_
  (`#11132 <https://github.com/coq/coq/pull/11132>`_, by Hugo Herbelin).

  .. example::

     The following features an implicit argument after a local
     definition. It was wrongly rejected.

     .. coqtop:: in

        Definition f := fix f (o := true) {n : nat} m {struct m} :=
          match m with 0 => 0 | S m' => f (n:=n+1) m' end.
