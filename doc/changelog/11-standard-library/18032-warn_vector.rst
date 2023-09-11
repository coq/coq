- **Added:**
  A warning on :g:`Vector.t` to make its new users aware that using
  this dependently typed representation of fixed-length lists is more
  technically difficult, compared to bundling lists with a proof of their
  length. This is not a deprecation and there is no intent to remove it
  from the standard library. Use option `-w -stdlib-vector`
  to silence the warning
  (`#18032 <https://github.com/coq/coq/pull/18032>`_,
  by Pierre Roux, reviewed by Andres Erbsen, Jim Fehrle, Emilio Jesús Gallego Arias, Gaëtan Gilbert, Hugo Herbelin, Olivier Laurent, Yishuai Li, Pierre-Marie Pédrot and Michael Soegtrop).
