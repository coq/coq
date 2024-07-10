From Stdlib Require Import MSetPositive.
From Stdlib Require Import MSetProperties.

Module Pos := MSetPositive.PositiveSet.
Module PPPP := MSetProperties.WPropertiesOn(Pos).
Print Module PPPP.
