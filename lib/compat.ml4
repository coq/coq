IFDEF OCAML308 THEN
type loc = Token.flocation
let dummy_loc = Token.dummy_loc
let unloc (b,e) = (b.Lexing.pos_cnum,e.Lexing.pos_cnum)
let make_loc loc = Token.make_loc loc
ELSE
type loc = int * int
let dummy_loc = (0,0)
let unloc x = x
let make_loc x = x
END
