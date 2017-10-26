Require Import MSetPositive.
Require Import MSetProperties.

Module Pos := MSetPositive.PositiveSet.
Module PPPP := MSetProperties.WPropertiesOn(Pos).
Print Module PPPP.
