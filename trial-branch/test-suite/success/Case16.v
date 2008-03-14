(**********************************************************************)
(* Test dependencies in constructors                                  *)
(**********************************************************************)

Check
  (fun x : {b : bool | if b then True else False} =>
   match x return (let (b, _) := x in if b then True else False) with
   | exist true y => y
   | exist false z => z
   end).
