
(* $Id$ *)

open Names
open Sign

type 'a unsafe_env = {
  context : context;
  sigma : 'a evar_map }
  
