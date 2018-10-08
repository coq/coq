(* A wish granted by the new support for patterns in notations *)

Local Notation mkmatch0 e p
  := match e with
     | p => true
     | _ => false
     end.
Local Notation "'mkmatch' [[ e ]] [[ p ]]"
  := match e with
     | p => true
     | _ => false
     end
       (at level 0, p pattern).
Check mkmatch0 _ ((0, 0)%core).
Check mkmatch [[ _ ]] [[ ((0, 0)%core) ]].
