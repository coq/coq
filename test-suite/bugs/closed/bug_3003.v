(* This used to raise an anomaly in 8.4 and trunk up to 17 April 2013 *)

Set Implicit Arguments.

Inductive path (V : Type) (E : V -> V -> Type) (s : V) : V -> Type :=
  | NoEdges : path E s s
  | AddEdge : forall d d' : V, path E s d -> E d d' -> path E s d'.
Inductive G_Vertex := G_v0 | G_v1.
Inductive G_Edge : G_Vertex -> G_Vertex -> Set := G_e : G_Edge G_v0 G_v1.
Goal forall x1 : G_Edge G_v1 G_v1, @AddEdge _ G_Edge G_v1 _ _ (NoEdges _ _) x1 = NoEdges _ _.
intro x1.
try destruct x1. (* now raises a typing error *)
