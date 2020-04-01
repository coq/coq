- **Changed:**
  Cleanup of names in the Reals theory: replaced `tan_is_inj` with `tan_inj` and replaced `atan_right_inv` with `tan_atan` -
  compatibility notations are provided. Moved various auxiliary lemmas from `Ratan.v` to more appropriate places.
  (`#9803 <https://github.com/coq/coq/pull/9803>`_,
  by Laurent Théry and Michael Soegtrop).

- **Added:** to the Reals theory:
  inverse trigonometric functions `asin` and `acos` with lemmas for the derivatives, bounds and special values of these functions;
  an extensive set of identities between trigonometric functions and their inverse functions;
  lemmas for the injectivity of sine and cosine;
  lemmas on the derivative of the inverse of decreasing functions and on the derivative of horizontally mirrored functions;
  various generic auxiliary lemmas and definitions for Rsqr, sqrt, posreal an others.
  (`#9803 <https://github.com/coq/coq/pull/9803>`_,
  by Laurent Théry and Michael Soegtrop).
