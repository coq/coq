- **Changed:**
  default character encoding is UTF8 (it was locale dependent on non-windows OSes),
  and when the configured encoding is not UTF8 RocqIDE will attempt to convert input files even if they are already valid UTF8
  (`#20256 <https://github.com/coq/coq/pull/20256>`_,
  fixes `#11526 <https://github.com/coq/coq/issues/11526>`_,
  by Gaëtan Gilbert).
