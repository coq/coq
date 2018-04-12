Require Import Program.Tactics.

Record T := BT { t : Set }.
Record U (x : T) := BU { u : t x -> Prop }.
Program Definition A (H : unit -> Prop) : U (BT unit) := BU _ H.
