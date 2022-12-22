type 'a key = 'a

let create x = x
let get x = x
let default x _ = x
let clean () = ()

exception InvalidKey
