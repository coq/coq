(**********************************************************************)
(* Test dependencies in constructors                                  *)
(**********************************************************************)

Check
  (fun x : {b : bool | if b then True else False} =>
   match x return (let (b, _) := x in if b then True else False) with
   | exist _ true y => y
   | exist _ false z => z
   end).
