(***************************************************************************

  Boolean unification with Buttner-Simonis' algorithm.

CiME Project - D�mons research team - LRI - Universit� Paris XI

$Id$

***************************************************************************)

open Signatures
open Gen_terms
open Problems

val solve : 
  'symbol #signature -> 'symbol elem_pb -> 
    ('symbol term * 'symbol term) list list

