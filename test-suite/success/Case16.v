(**********************************************************************)
(* Test dependencies in constructors                                  *)
(**********************************************************************)

Check [x : {b:bool|if b then True else False}]
   <[x]let (b,_) = x in if b then True else False>Cases x of
   | (exist true y)  => y
   | (exist false z) => z
   end.
