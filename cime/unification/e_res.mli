(***************************************************************************

This module provides a function which implements the E-Resolution,
that is solves an elementary (pure) problem according to its theory.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Signatures
open Problems

val general_E_resolution : 
  'symbol #signature -> (*i Variables.user_variables -> i*) 
    'symbol problem -> 'symbol problem list



