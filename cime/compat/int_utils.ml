(*

  a few arithmetic useful functions

*)

let power x y = 
  let rec pow x y =
    match y with
      | 0 -> 1
      | 1 -> x 
      | _ ->
	  let z = pow x (y/2) in
	  if y mod 2 = 0
	  then z*z
	  else z*z*x
  in
  if y < 0 then invalid_arg "Int_utils.power"
  else pow x y
;;

let rec pgcd n m =
  if m=0 
  then n
  else pgcd m (n mod m);;

let rec full_pgcd n m =
  if m=0 
  then (n,1,0)
  else 
    let q = n/m and r = n mod m in
    let (d,k1,k2) = full_pgcd m r in
    (* 
       here we have m = k1 * d  and r = k2 * d so
       n = q * m + r = q * k1 * d + k2 * d
    *)
    (d,q*k1+k2,k1)
    
let ppcm n m = (n * m) / (pgcd n m);;


