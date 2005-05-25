type nat = int

let (+) (x : nat) (y : nat) = x + y
let (-) (x : nat) (y : nat) = 
  if y > x then raise (Invalid_argument "in substraction")
  else x - y
    
let succ (x : nat) = succ x
  
let (<) (x : nat) (y : nat) = x < y
