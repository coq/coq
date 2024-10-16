Inductive Inner : Type :=
| innerI_nat : forall (x:nat), Inner
| innerI_fun : forall (f:nat->Type), Inner
| innerI_inner : forall (i:Inner), Inner
| innerI_Type : forall (T:Type), Inner
| innerI_extra : Inner.

Inductive ExtractTest (A:Type) (F:nat->Type) (I:Inner): Inner -> Inner -> unit -> Type :=
| extract_f_x_from_index : forall (x:nat) (f:nat->Type) (t:f x),
    ExtractTest A F I (innerI_inner (innerI_nat x)) (innerI_fun f) tt
| extract_F_from_param_x_from_index : forall (x:nat) (f:nat->Type) (t:F x),
    ExtractTest A F I (innerI_inner (innerI_nat x)) innerI_extra tt
| extract_fail : forall (x y: nat) (f : nat -> Type) (t : f x),
    ExtractTest A F I (innerI_nat y) (innerI_fun f) tt
| extract_fx_from_index : forall (x:nat) (f:nat->Type) (t:f x),
    ExtractTest A F I (innerI_Type (f x)) innerI_extra tt
| extract_t_match : forall (b:bool) (t:if b then unit else nat),
    ExtractTest A F I (innerI_Type (if b then unit else nat)) innerI_extra tt
.

(* This still dosn't work, because the fields type isn't composeable from extracteable parts of its inductive type.*)
Lemma test_extract_fail A F x y f t1 t2 : extract_fail A F innerI_extra x y f t1 = extract_fail A F innerI_extra x y f t2 -> t1 = t2.
Proof.
    Fail congruence.
Abort.

(* I think this should also work when the whole match statement is part of the inductive type, but something with universes is wrong because A is Type but if b then unit else nat is Set below is the projection that is getting created but it doesn't work *)
Lemma test_extract_t_match_success (A:Set) (F:nat->Type) (b:bool) (t1 t2: if b then unit else nat) :
extract_t_match A F innerI_extra b t1 = extract_t_match A F innerI_extra b t2 -> t1 = t2.
Proof.
    intros H.
    Fail congruence.
Abort.


Fail Definition proj (A:Type) (F:nat->Type) (b:bool) (t1:if b then unit else nat):=
    (fun
    e : ExtractTest A F innerI_extra
          (innerI_Type (if b then unit else nat)) innerI_extra tt =>
  match
    e in (ExtractTest _ _ _ i i0 u)
    return
      (match i with
       | innerI_Type T => T
       | _ => if b then unit else nat
       end ->
       match i with
       | innerI_Type T => T
       | _ => if b then unit else nat
       end)
  with
  | extract_f_x_from_index _ _ _ x f _ =>
      fun
        t : match innerI_inner (innerI_nat x) with
            | innerI_Type T => T
            | _ => if b then unit else nat
            end =>
      t
  | extract_F_from_param_x_from_index _ _ _ x _ _ =>
      fun
        t : match innerI_inner (innerI_nat x) with
            | innerI_Type T => T
            | _ => if b then unit else nat
            end =>
      t
  | extract_fail _ _ _ x y f _ =>
      fun
        t : match innerI_nat y with
            | innerI_Type T => T
            | _ => if b then unit else nat
            end =>
      t
  | extract_fx_from_index _ _ _ x f _ =>
      fun
        t : match innerI_Type (f x) with
            | innerI_Type T => T
            | _ => if b then unit else nat
            end =>
      t
  | extract_t_match _ _ _ b0 t =>
      fun
        _ : match innerI_Type (if b0 then unit else nat) with
            | innerI_Type T => T
            | _ => if b then unit else nat
            end =>
      t
  end t1).
