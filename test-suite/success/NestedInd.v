Unset Elimination Schemes.

Definition Decision (P : Prop) := {P} + {~ P}.

Definition RelDecision {A B : Type} (R : A -> B -> Prop) :=
   forall (x : A) (y : B), Decision (R x y) : Type.

Inductive gmap_dep_ne (A : Type) : Type :=
    GNode001 : gmap_dep_ne A -> gmap_dep_ne A
  | GNode010 : A -> gmap_dep_ne A
  | GNode011 : A -> gmap_dep_ne A -> gmap_dep_ne A
  | GNode100 : gmap_dep_ne A -> gmap_dep_ne A
  | GNode101 : gmap_dep_ne A -> gmap_dep_ne A -> gmap_dep_ne A
  | GNode110 : gmap_dep_ne A -> A -> gmap_dep_ne A
  | GNode111 : gmap_dep_ne A -> A -> gmap_dep_ne A -> gmap_dep_ne A.

Variant gmap_dep (A : Type) : Type :=
    GEmpty : gmap_dep A | GNodes : gmap_dep_ne A -> gmap_dep A.

Arguments GEmpty {A}.
Arguments GNodes {A}.

Record gmap {K : Type} (EqDecision0 : RelDecision (@eq K))
  (A : Type) : Type := GMap { gmap_car : gmap_dep A }.

Inductive gtest {K : Type} (H : RelDecision (@eq K)) := GTest : gmap H (gtest H) -> gtest H.
Arguments GTest {_ _} _.

Definition option_union_with (A : Type) (f : A -> A -> option A) (mx my : option A) :=
  match mx with
  | Some x => match my with
              | Some y => f x y
              | None => Some x
              end
  | None => match my with
            | Some y => Some y
            | None => None
            end
  end.

Definition gmap_dep_ne_case (A : Type) (B : Type) (t : gmap_dep_ne A)
  (f : gmap_dep A -> option A -> gmap_dep A -> B) :=
  match t with
  | GNode001 _ r => f GEmpty None (GNodes r)
  | GNode010 _ x => f GEmpty (Some (x)) GEmpty
  | GNode011 _ x r => f GEmpty (Some (x)) (GNodes r)
  | GNode100 _ l => f (GNodes l) None GEmpty
  | GNode101 _ l r => f (GNodes l) None (GNodes r)
  | GNode110 _ l x => f (GNodes l) (Some (x)) GEmpty
  | GNode111 _ l x r => f (GNodes l) (Some (x)) (GNodes r)
  end.

Definition gmap_dep_omap_aux {A B : Type} (go : gmap_dep_ne A -> gmap_dep B)
  (tm : gmap_dep A) :=
  match tm with
  | GEmpty => GEmpty
  | GNodes t' => go t'
  end.

Definition option_bind {A B : Type} (f : A -> option B) (mx : option A) :=
  match mx with
  | Some x => f x
  | None => None
  end.

Definition GNode (A : Type)
  (ml : gmap_dep A)
  (mx : option (A))
  (mr : gmap_dep A) :=
  match ml with
  | GEmpty =>
      match mx with
      | Some x =>
          match mr with
          | GEmpty => GNodes (GNode010 _ x)
          | GNodes r => GNodes (GNode011 _ x r)
          end
      | None =>
          match mr with
          | GEmpty => GEmpty
          | GNodes r => GNodes (GNode001 _ r)
          end
      end
  | GNodes l =>
      match mx with
      | Some (x) =>
          match mr with
          | GEmpty => GNodes (GNode110 _ l x)
          | GNodes r => GNodes (GNode111 _ l x r)
          end
      | None =>
          match mr with
          | GEmpty => GNodes (GNode100 _ l)
          | GNodes r => GNodes (GNode101 _ l r)
          end
      end
  end.

Definition gmap_dep_ne_omap (A B : Type) (f : A -> option B) :=
  fix go (t : gmap_dep_ne A) {struct t} : gmap_dep B :=
    gmap_dep_ne_case _ _ t
      (fun (ml : gmap_dep A) (mx : option A) (mr : gmap_dep A) =>
         GNode _
           (gmap_dep_omap_aux (go) ml)
           (option_bind f mx)
           (gmap_dep_omap_aux (go) mr)).

Definition gmap_merge_aux (A B C : Type) (go : gmap_dep_ne A
                                             -> gmap_dep_ne B -> gmap_dep C)
  (f : option A -> option B -> option C) (mt1 : gmap_dep A)
  (mt2 : gmap_dep B) :=
  match mt1 with
  | GEmpty =>
      match mt2 with
      | GEmpty => GEmpty
      | GNodes t2' => gmap_dep_ne_omap _ _ (fun x : B => f None (Some x)) t2'
      end
  | GNodes t1' =>
      match mt2 with
      | GEmpty => gmap_dep_ne_omap _ _ (fun x : A => f (Some x) None) t1'
      | GNodes t2' => go t1' t2'
      end
  end.

Definition diag_None' {A B C : Type} (f : option A -> option B -> option C)
  (mx : option (A)) (my : option (B)) :=
  match mx with
  | Some (x) =>
      match my with
      | Some (y) => f (Some x) (Some y)
      | None => f (Some x) None
      end
  | None =>
      match my with
      | Some (y) => f None (Some y)
      | None => None
      end
  end.

Definition gmap_dep_ne_merge {A B C : Type} (f : option A -> option B -> option C) :=
  fix go
   (t1 : gmap_dep_ne A) (t2 : gmap_dep_ne B)
    {struct t1} : gmap_dep C :=
    gmap_dep_ne_case _ _ t1
      (fun (ml1 : gmap_dep A)
         (mx1 : option (A)) (mr1 : gmap_dep A) =>
         gmap_dep_ne_case _ _ t2
           (fun (ml2 : gmap_dep B)
              (mx2 : option (B)) (mr2 : gmap_dep B) =>
              GNode _
                (gmap_merge_aux _ _ _ go
                   f ml1 ml2) (diag_None' f mx1 mx2)
                (gmap_merge_aux _ _ _ go
                   f mr1 mr2))).

Definition gmap_dep_merge {A B C : Type}
  (f : option A -> option B -> option C) :=
  gmap_merge_aux _ _ _ (gmap_dep_ne_merge f) f
     : gmap_dep A -> gmap_dep B -> gmap_dep C.

Definition gmap_merge (K : Type) (H : RelDecision (@eq K))
  (A B C : Type) (f : option A -> option B -> option C) := (fun '{| gmap_car := mt1 |} '{| gmap_car := mt2 |} =>
  {| gmap_car := gmap_dep_merge f mt1 mt2 |})
     : (gmap H A) -> (gmap H B) -> (gmap H C).

Fixpoint gtest_merge {K : Type} (H : RelDecision (@eq K)) (t1 t2 : gtest H) {struct t1} : gtest H :=
  match t1, t2 with
  | GTest ts1, GTest ts2 =>
     GTest (gmap_merge K H _ _ _ (@option_union_with _ (fun t1 t2 => Some (gtest_merge H t1 t2))) ts1 ts2)
  end.

(* An example from metacoq (simplified) *)

Notation "x .π2" := (projT2 x) (at level 0).

Parameter term : Type.

Inductive All (P :  term -> Type) : Type :=
  | All_cons : {x:term & P x} -> All P -> All P.

Inductive inferring  (Σ : unit) : term -> Type :=
| infer x : All (inferring Σ) -> inferring Σ x.

Fixpoint inferring_size  {Σ t} (d : inferring Σ t) {struct d} : nat :=
  match d with
  | infer _ _ (All_cons _ p _) => inferring_size p.π2
  end.
