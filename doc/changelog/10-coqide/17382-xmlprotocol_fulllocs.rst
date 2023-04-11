- **Changed:**
  XML Protocol now sends (and expects) full Coq locations, including
  line and column information. This makes some IDE operations (such as
  UTF-8 decoding) more efficient. Clients of the XML protocol can just
  ignore the new fields if they are not useful for them.
  (`#17382 <https://github.com/coq/coq/pull/17382>`_,
  fixes `#17023 <https://github.com/coq/coq/issues/17023>`_,
  by Emilio Jesus Gallego Arias).
