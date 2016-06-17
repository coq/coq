(* An example one would like to see succeeding *)

Record T := BT { t : Set }.
Record U (x : T) := BU { u : t x -> Prop }.
Fail Definition A (H : unit -> Prop) : U (BT unit) := BU _ H.
