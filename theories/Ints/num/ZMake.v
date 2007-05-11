Require Import ZArith.

Module Type NType.

 Parameter t : Set.
 
 Parameter zero : t.
 Parameter one : t.

 Parameter of_N : N -> t.
 Parameter to_Z : t -> Z.

 Parameter compare : t -> t -> comparison.
 Parameter eq_bool : t -> t -> bool.

 Parameter succ : t -> t.
 Parameter add  : t -> t -> t.
 Parameter pred : t -> t.
 Parameter sub  : t -> t -> t.

 Parameter mul       : t -> t -> t.
 Parameter square    : t -> t.
 Parameter power_pos : t -> positive -> t.
 Parameter sqrt      : t -> t.

 Parameter div_eucl : t -> t -> t * t.
 Parameter div      : t -> t -> t.
 Parameter modulo   : t -> t -> t.
 Parameter gcd      : t -> t -> t.

End NType.

Module Make (N:NType).
 
 Inductive t_ : Set := 
  | Pos : N.t -> t_
  | Neg : N.t -> t_.
 
 Definition t := t_.

 Definition zero := Pos N.zero.
 Definition one  := Pos N.one.
 Definition minus_one := Neg N.one.

 Definition of_Z x := 
  match x with
  | Zpos x => Pos (N.of_N (Npos x))
  | Z0 => zero
  | Zneg x => Neg (N.of_N (Npos x))
  end.
 
 Definition to_Z x :=
  match x with
  | Pos nx => N.to_Z nx
  | Neg nx => Zopp (N.to_Z nx)
  end.

 Definition compare x y :=
  match x, y with
  | Pos nx, Pos ny => N.compare nx ny
  | Pos nx, Neg ny =>
    match N.compare nx N.zero with
    | Gt => Gt
    | _ => N.compare ny N.zero
    end
  | Neg nx, Pos ny =>
    match N.compare N.zero nx with
    | Lt => Lt
    | _ => N.compare N.zero ny
    end
  | Neg nx, Neg ny => N.compare ny nx
  end.

 Definition eq_bool x y := 
  match compare x y with
  | Eq => true
  | _ => false
  end.

 Definition cmp_sign x y :=
  match x, y with
  | Pos nx, Neg ny => 
    if N.eq_bool ny N.zero then Eq else Gt 
  | Neg nx, Pos ny => 
    if N.eq_bool nx N.zero then Eq else Lt
  | _, _ => Eq
  end.
 
 Definition to_N x :=
  match x with
  | Pos nx => nx
  | Neg nx => nx
  end.

 Definition abs x := Pos (to_N x).
 
 Definition opp x := 
  match x with 
  | Pos nx => Neg nx
  | Neg nx => Pos nx
  end.
    
 Definition succ x :=
  match x with
  | Pos n => Pos (N.succ n)
  | Neg n =>
    match N.compare N.zero n with
    | Lt => Neg (N.pred n)
    | _ => one
    end
  end.

 Definition add x y :=
  match x, y with
  | Pos nx, Pos ny => Pos (N.add nx ny)
  | Pos nx, Neg ny =>
    match N.compare nx ny with
    | Gt => Pos (N.sub nx ny)
    | Eq => zero
    | Lt => Neg (N.sub ny nx)
    end
  | Neg nx, Pos ny =>
    match N.compare nx ny with
    | Gt => Neg (N.sub nx ny)
    | Eq => zero
    | Lt => Pos (N.sub ny nx)
    end
  | Neg nx, Neg ny => Neg (N.add nx ny)
  end.

 Definition pred x :=
  match x with
  | Pos nx =>
    match N.compare N.zero nx with
    | Lt => Pos (N.pred nx)
    | _ => minus_one
    end
  | Neg nx => Neg (N.succ nx)
  end.

 Definition sub x y :=
  match x, y with
  | Pos nx, Pos ny => 
    match N.compare nx ny with
    | Gt => Pos (N.sub nx ny)
    | Eq => zero
    | Lt => Neg (N.sub ny nx)
    end
  | Pos nx, Neg ny => Pos (N.add nx ny)
  | Neg nx, Pos ny => Neg (N.add nx ny)
  | Neg nx, Neg ny => 
    match N.compare nx ny with
    | Gt => Neg (N.sub nx ny)
    | Eq => zero
    | Lt => Pos (N.sub ny nx)
    end
  end.

 Definition mul x y := 
  match x, y with
  | Pos nx, Pos ny => Pos (N.mul nx ny)
  | Pos nx, Neg ny => Neg (N.mul nx ny)
  | Neg nx, Pos ny => Neg (N.mul nx ny)
  | Neg nx, Neg ny => Pos (N.mul nx ny)
  end.

 Definition square x := 
  match x with
  | Pos nx => Pos (N.square nx)
  | Neg nx => Pos (N.square nx)
  end.

 Definition power_pos x p :=
  match x with
  | Pos nx => Pos (N.power_pos nx p)
  | Neg nx => 
    match p with
    | xH => x
    | xO _ => Pos (N.power_pos nx p)
    | xI _ => Neg (N.power_pos nx p)
    end
  end.

 Definition sqrt x :=
  match x with
  | Pos nx => Pos (N.sqrt nx)
  | Neg nx => Neg N.zero
  end.

 Definition div_eucl x y :=
  match x, y with
  | Pos nx, Pos ny =>
    let (q, r) := N.div_eucl nx ny in
    (Pos q, Pos r)
  | Pos nx, Neg ny =>
    let (q, r) := N.div_eucl nx ny in
    (Neg q, Pos r)
  | Neg nx, Pos ny =>
    let (q, r) := N.div_eucl nx ny in
    match N.compare N.zero r with
    | Eq => (Neg q, zero)
    | _ => (Neg (N.succ q), Pos (N.sub ny r))
    end
  | Neg nx, Neg ny =>
    let (q, r) := N.div_eucl nx ny in
    match N.compare N.zero r with
    | Eq => (Pos q, zero)
    | _ => (Pos (N.succ q), Pos (N.sub ny r))
    end
  end.

 Definition div x y := fst (div_eucl x y).

 Definition modulo x y := snd (div_eucl x y).

 Definition gcd x y :=
  match x, y with
  | Pos nx, Pos ny => Pos (N.gcd nx ny)
  | Pos nx, Neg ny => Pos (N.gcd nx ny)
  | Neg nx, Pos ny => Pos (N.gcd nx ny)
  | Neg nx, Neg ny => Pos (N.gcd nx ny) 
  end.

End Make.
