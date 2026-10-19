(* The entries are cleared at the start of a query when they weigh more than
   twice the heaviest earlier query in the environment. An entry weighs one
   plus the size of the set it keeps (none for a constant without a body), and
   a block's shared set counts once; a query weighs what it records plus what
   it replays, counted the same way.
   Each part starts after declarations, which clear the entries and every
   weight. The numbers below are the entries' weight at the start of each
   query. Each part places a clearing, or the absence of one, at the
   boundary, so weighing recorded objects, replays or blocks differently
   changes the list of replays and clearings. *)

Set Debug "assumptions-cache".

(* Recorded objects. A query over a definition and its axiom weighs 3 (a: 1,
   g: 2). Starts: 0, 3, 6 (not more than 2 * 3), then 9: cleared, g0 is walked
   again, and replayed on the last query. *)
Axiom a0 : Prop.
Axiom a1 : Prop.
Axiom a2 : Prop.
Definition g0 := a0.
Definition g1 := a1.
Definition g2 := a2.
Print Assumptions g0.
Print Assumptions g1.
Print Assumptions g2.
Print Assumptions g0.
Print Assumptions g0.

(* Replayed entries. The query on k records P (1) and k (4) and replays h0
   and h1 (3 each: 2 objects and 1 edge), so it weighs 11. Starts: 0, 3, 6,
   then 11, 14, 17, 20, none more than 2 * 11, and h0 is replayed on the last
   query. Counting k without its replays (5), or its replays without their
   objects (7) or their edges (9), clears the entries before h2, h4 or the
   last query. *)
Axiom c0 : Prop.
Axiom c1 : Prop.
Axiom c2 : Prop.
Axiom c3 : Prop.
Axiom c4 : Prop.
Definition P (x y : Prop) : Prop := x.
Definition h0 := c0.
Definition h1 := c1.
Definition h2 := c2.
Definition h3 := c3.
Definition h4 := c4.
Definition k := P h0 h1.
Print Assumptions h0.
Print Assumptions h1.
Print Assumptions k.
Print Assumptions h2.
Print Assumptions h3.
Print Assumptions h4.
Print Assumptions h0.

(* Recorded blocks. The query on J records b0 (1) and J's block: its two
   members plus one edge set of three (b0, J, j), 5 in all, so it weighs 6.
   Starts: 0, 6, 9, then 12 (not more than 2 * 6): J is replayed; 12, then
   15: cleared, J is walked again, and replayed on the last query. *)
Axiom b0 : Prop.
Inductive J : Prop := j : b0 -> J.
Axiom d0 : Prop.
Axiom d1 : Prop.
Axiom d2 : Prop.
Definition e0 := d0.
Definition e1 := d1.
Definition e2 := d2.
Print Assumptions J.
Print Assumptions e0.
Print Assumptions e1.
Print Assumptions J.
Print Assumptions e2.
Print Assumptions J.
Print Assumptions J.
