- **Changed:**
  Tactics with qualified name of the form ``Coq.Init.Notations`` are
  now qualified with prefix ``Coq.Init.Ltac``; users of the -noinit
  option should now import Coq.Init.Ltac if they want to use Ltac
  (`#12023 <https://github.com/coq/coq/pull/12023>`_,
  by Hugo Herbelin; minor source of incompatibilities).
