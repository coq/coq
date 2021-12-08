(* Was raising an anomaly *)
Notation "'[#' ] f '|' x .. z '=n>' b" :=
  (fun x => .. (fun z => f b) ..)
    (at level 201, x binder, z binder,
     format "'[  ' [# ] '[' f  | ']'  x  ..  z  =n>  '[' b ']' ']'"
    ).
