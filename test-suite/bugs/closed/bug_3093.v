Require Import FunctionalExtensionality.

Goal forall y, @f_equal = y.
  intro.
  apply functional_extensionality_dep.
Abort.
