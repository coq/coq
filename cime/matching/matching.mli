
open Gen_terms
open Substitution

exception No_match

val matching : 
  'symbol #Signatures.signature -> 'symbol term -> 'symbol term -> 
    'symbol substitution

val all_matchs :
  'symbol #Signatures.signature -> Variables.user_variables -> 
    'symbol term -> 'symbol term -> unit
  
