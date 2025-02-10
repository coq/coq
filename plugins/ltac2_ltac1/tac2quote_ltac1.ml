open Ltac2_plugin.Tac2dyn

let wit_ltac1 = Arg.create "ltac1"
let wit_ltac1val = Arg.create "ltac1val"

let val_ltac1 : Geninterp.Val.t Val.tag = Val.create "ltac1"

let ltac1 = Ltac2_plugin.Tac2ffi.repr_ext val_ltac1
