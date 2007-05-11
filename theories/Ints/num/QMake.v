Require Import Bool.
Require Import ZArith.
Require Import Arith.

Inductive q_type : Set := 
 | Qz : Z.t -> q_type
 | Qq : Z.t -> N.t -> q_type.

Definition print_type x := 
 match x with
 | Qz _ => Z
 | _ => (Z*Z)%type
 end.

Definition print x :=
 match x return print_type x with
 | Qz zx => Z.to_Z zx
 | Qq nx dx => (Z.to_Z nx, N.to_Z dx)
 end.

Module Qp.

 Definition t := q_type.

 Definition zero := Qz Z.zero.
 Definition one  := Qz Z.one.
 Definition minus_one := Qz Z.minus_one.

 Definition of_Z x := Qz (Z.of_Z x).

 Definition d_to_Z d := Z.Pos (N.succ d).

 Definition compare x y :=
  match x, y with
  | Qz zx, Qz zy => Z.compare zx zy
  | Qz zx, Qq ny dy => Z.compare (Z.mul zx (d_to_Z dy)) ny
  | Qq nx dy, Qz zy => Z.compare nx (Z.mul zy (d_to_Z dy))
  | Qq nx dx, Qq ny dy =>
    Z.compare (Z.mul nx (d_to_Z dy)) (Z.mul ny (d_to_Z dx))
  end.

 Definition opp x :=
  match x with
  | Qz zx => Qz (Z.opp zx)
  | Qq nx dx => Qq (Z.opp nx) dx
  end.

(* Inv d > 0, Pour la forme normal unique on veut d > 1 *)
 Definition norm n d :=
  if Z.eq_bool n Z.zero then zero
  else
    let gcd := N.gcd (Z.to_N n) d in
    if N.eq_bool gcd N.one then Qq n (N.pred d)
    else	
      let n := Z.div n (Z.Pos gcd) in
      let d := N.div d gcd in
      if N.eq_bool d N.one then Qz n
      else Qq n (N.pred d).
   
 Definition add x y :=
  match x, y with
  | Qz zx, Qz zy => Qz (Z.add zx zy)
  | Qz zx, Qq ny dy => Qq (Z.add (Z.mul zx (d_to_Z dy)) ny) dy
  | Qq nx dx, Qz zy => Qq (Z.add nx (Z.mul zy (d_to_Z dx))) dx
  | Qq nx dx, Qq ny dy => 
    let dx' := N.succ dx in
    let dy' := N.succ dy in
    let n := Z.add (Z.mul nx (Z.Pos dy')) (Z.mul ny (Z.Pos dx')) in
    let d := N.pred (N.mul dx' dy') in
    Qq n d
  end.

 Definition add_norm x y := 
  match x, y with
  | Qz zx, Qz zy => Qz (Z.add zx zy)
  | Qz zx, Qq ny dy => 
    let d := N.succ dy in
    norm (Z.add (Z.mul zx (Z.Pos d)) ny) d 
  | Qq nx dx, Qz zy =>
    let d := N.succ dx in
    norm (Z.add (Z.mul zy (Z.Pos d)) nx) d
  | Qq nx dx, Qq ny dy =>
    let dx' := N.succ dx in
    let dy' := N.succ dy in
    let n := Z.add (Z.mul nx (Z.Pos dy')) (Z.mul ny (Z.Pos dx')) in
    let d := N.mul dx' dy' in
    norm n d 
  end.
 
 Definition sub x y := add x (opp y).

 Definition sub_norm x y := add_norm x (opp y).

 Definition mul x y :=
  match x, y with
  | Qz zx, Qz zy => Qz (Z.mul zx zy)
  | Qz zx, Qq ny dy => Qq (Z.mul zx ny) dy
  | Qq nx dx, Qz zy => Qq (Z.mul nx zy) dx
  | Qq nx dx, Qq ny dy => 
    Qq (Z.mul nx ny) (N.pred (N.mul (N.succ dx) (N.succ dy)))
  end.

 Definition mul_norm x y := 
  match x, y with
  | Qz zx, Qz zy => Qz (Z.mul zx zy)
  | Qz zx, Qq ny dy =>
    if Z.eq_bool zx Z.zero then zero
    else	
      let d := N.succ dy in
      let gcd := N.gcd (Z.to_N zx) d in
      if N.eq_bool gcd N.one then Qq (Z.mul zx ny) dy
      else 
        let zx := Z.div zx (Z.Pos gcd) in
        let d := N.div d gcd in
        if N.eq_bool d N.one then Qz (Z.mul zx ny)
        else Qq (Z.mul zx ny) (N.pred d)
  | Qq nx dx, Qz zy =>   
    if Z.eq_bool zy Z.zero then zero
    else	
      let d := N.succ dx in
      let gcd := N.gcd (Z.to_N zy) d in
      if N.eq_bool gcd N.one then Qq (Z.mul zy nx) dx
      else 
        let zy := Z.div zy (Z.Pos gcd) in
        let d := N.div d gcd in
        if N.eq_bool d N.one then Qz (Z.mul zy nx)
        else Qq (Z.mul zy nx) (N.pred d)
  | Qq nx dx, Qq ny dy => 
    norm (Z.mul nx ny) (N.mul (N.succ dx) (N.succ dy))
  end.

 Definition inv x := 
  match x with
  | Qz (Z.Pos n) => 
    if N.eq_bool n N.zero then zero else Qq Z.one (N.pred n)
  | Qz (Z.Neg n) => 
    if N.eq_bool n N.zero then zero else Qq Z.minus_one (N.pred n)
  | Qq (Z.Pos n) d => 
    if N.eq_bool n N.zero then zero else Qq (Z.Pos (N.succ d)) (N.pred n)
  | Qq (Z.Neg n) d => 
    if N.eq_bool n N.zero then zero else Qq (Z.Neg (N.succ d)) (N.pred n)
  end.

Definition inv_norm x := 
 match x with
 | Qz (Z.Pos n) => 
      if N.eq_bool n N.zero then zero else
      if N.eq_bool n N.one then x else Qq Z.one (N.pred n)
 | Qz (Z.Neg n) => 
      if N.eq_bool n N.zero then zero  else
      if N.eq_bool n N.one then x else Qq Z.minus_one n
 | Qq (Z.Pos n) d => let d := N.succ d in 
                  if N.eq_bool n N.one then Qz (Z.Pos d) 
                     else Qq (Z.Pos d) (N.pred n)
 | Qq (Z.Neg n) d => let d := N.succ d in 
                  if N.eq_bool n N.one then Qz (Z.Neg d) 
                     else Qq (Z.Pos d) (N.pred n)
 end.


 Definition square x :=
  match x with
  | Qz zx => Qz (Z.square zx)
  | Qq nx dx => Qq (Z.square nx) (N.pred (N.square (N.succ dx)))
  end.

 Definition power_pos x p :=
  match x with
  | Qz zx => Qz (Z.power_pos zx p)
  | Qq nx dx => Qq (Z.power_pos nx p) (N.pred (N.power_pos (N.succ dx) p))
  end.

End Qp.


Module Qv.

 (* /!\  Invariant maintenu par les fonctions :
         - le denominateur n'est jamais nul *)

 Definition t := q_type.

 Definition zero := Qz Z.zero.
 Definition one  := Qz Z.one.
 Definition minus_one := Qz Z.minus_one.

 Definition of_Z x := Qz (Z.of_Z x).

 Definition is_valid x := 
  match x with
  | Qz _ => True
  | Qq n d => if N.eq_bool d N.zero then False else True
  end.
 (* Les fonctions doivent assurer que si leur arguments sont valides alors
    le resultat est correct et valide (si c'est un Q) 
 *)

 Definition compare x y :=
  match x, y with
  | Qz zx, Qz zy => Z.compare zx zy
  | Qz zx, Qq ny dy => Z.compare (Z.mul zx (Z.Pos dy)) ny
  | Qq nx dx, Qz zy => Z.compare Z.zero zy 
  | Qq nx dx, Qq ny dy => Z.compare (Z.mul nx (Z.Pos dy)) (Z.mul ny (Z.Pos dx))
  end.

 Definition opp x :=
  match x with
  | Qz zx => Qz (Z.opp zx)
  | Qq nx dx => Qq (Z.opp nx) dx
  end.

 Definition norm n d :=
  if Z.eq_bool n Z.zero then zero
  else
    let gcd := N.gcd (Z.to_N n) d in
    if N.eq_bool gcd N.one then Qq n d
    else	
      let n := Z.div n (Z.Pos gcd) in
      let d := N.div d gcd in
      if N.eq_bool d N.one then Qz n
      else Qq n d.
   
 Definition add x y :=
  match x, y with
  | Qz zx, Qz zy => Qz (Z.add zx zy)
  | Qz zx, Qq ny dy => Qq (Z.add (Z.mul zx (Z.Pos dy)) ny) dy
  | Qq nx dx, Qz zy => Qq (Z.add nx (Z.mul zy (Z.Pos dx))) dx
  | Qq nx dx, Qq ny dy => 
    let n := Z.add (Z.mul nx (Z.Pos dy)) (Z.mul ny (Z.Pos dx)) in
    let d := N.mul dx dy in
    Qq n d
  end.

 Definition add_norm x y := 
  match x, y with
  | Qz zx, Qz zy => Qz (Z.add zx zy)
  | Qz zx, Qq ny dy => 
    norm (Z.add (Z.mul zx (Z.Pos dy)) ny) dy 
  | Qq nx dx, Qz zy =>
    norm (Z.add (Z.mul zy (Z.Pos dx)) nx) dx
  | Qq nx dx, Qq ny dy =>
    let n := Z.add (Z.mul nx (Z.Pos dy)) (Z.mul ny (Z.Pos dx)) in
    let d := N.mul dx dy in
    norm n d 
  end.
 
 Definition sub x y := add x (opp y).

 Definition sub_norm x y := add_norm x (opp y).

 Definition mul x y :=
  match x, y with
  | Qz zx, Qz zy => Qz (Z.mul zx zy)
  | Qz zx, Qq ny dy => Qq (Z.mul zx ny) dy
  | Qq nx dx, Qz zy => Qq (Z.mul nx zy) dx
  | Qq nx dx, Qq ny dy => 
    Qq (Z.mul nx ny) (N.mul dx dy)
  end.

 Definition mul_norm x y := 
  match x, y with
  | Qz zx, Qz zy => Qz (Z.mul zx zy)
  | Qz zx, Qq ny dy =>
    if Z.eq_bool zx Z.zero then zero
    else	
      let gcd := N.gcd (Z.to_N zx) dy in
      if N.eq_bool gcd N.one then Qq (Z.mul zx ny) dy
      else 
        let zx := Z.div zx (Z.Pos gcd) in
        let d := N.div dy gcd in
        if N.eq_bool d N.one then Qz (Z.mul zx ny)
        else Qq (Z.mul zx ny) d
  | Qq nx dx, Qz zy =>   
    if Z.eq_bool zy Z.zero then zero
    else	
      let gcd := N.gcd (Z.to_N zy) dx in
      if N.eq_bool gcd N.one then Qq (Z.mul zy nx) dx
      else 
        let zy := Z.div zy (Z.Pos gcd) in
        let d := N.div dx gcd in
        if N.eq_bool d N.one then Qz (Z.mul zy nx)
        else Qq (Z.mul zy nx) d
  | Qq nx dx, Qq ny dy => norm (Z.mul nx ny) (N.mul dx dy)
  end.

 Definition inv x := 
  match x with
  | Qz (Z.Pos n) => 
    if N.eq_bool n N.zero then zero else Qq Z.one n
  | Qz (Z.Neg n) => 
    if N.eq_bool n N.zero then zero else Qq Z.minus_one n
  | Qq (Z.Pos n) d => 
    if N.eq_bool n N.zero then zero else Qq (Z.Pos d) n
  | Qq (Z.Neg n) d => 
    if N.eq_bool n N.zero then zero else Qq (Z.Neg d) n
  end.

 Definition square x :=
  match x with
  | Qz zx => Qz (Z.square zx)
  | Qq nx dx => Qq (Z.square nx) (N.square dx)
  end.

 Definition power_pos x p :=
  match x with
  | Qz zx => Qz (Z.power_pos zx p)
  | Qq nx dx => Qq (Z.power_pos nx p) (N.power_pos dx p)
  end.

End Qv.

Module Q.

 (* Troisieme solution :
    0 a de nombreuse representation :
         0, -0, 1/0, ... n/0,
    il faut alors faire attention avec la comparaison et l'addition 
 *)

 Definition t := q_type.

 Definition zero := Qz Z.zero.
 Definition one  := Qz Z.one.
 Definition minus_one := Qz Z.minus_one.

 Definition of_Z x := Qz (Z.of_Z x).

 Definition compare x y :=
  match x, y with
  | Qz zx, Qz zy => Z.compare zx zy
  | Qz zx, Qq ny dy => 
    if N.eq_bool dy N.zero then Z.compare zx Z.zero
    else Z.compare (Z.mul zx (Z.Pos dy)) ny
  | Qq nx dx, Qz zy => 
    if N.eq_bool dx N.zero then Z.compare Z.zero zy 
    else Z.compare nx (Z.mul zy (Z.Pos dx))
  | Qq nx dx, Qq ny dy =>
    match N.eq_bool dx N.zero, N.eq_bool dy N.zero with
    | true, true => Eq
    | true, false => Z.compare Z.zero ny
    | false, true => Z.compare nx Z.zero
    | false, false => Z.compare (Z.mul nx (Z.Pos dy)) (Z.mul ny (Z.Pos dx))
    end
  end.

 Definition opp x :=
  match x with
  | Qz zx => Qz (Z.opp zx)
  | Qq nx dx => Qq (Z.opp nx) dx
  end.

(* Je pense que cette fonction normalise bien ... *)
 Definition norm n d :=
  let gcd := N.gcd (Z.to_N n) d in 
  match N.compare N.one gcd with
  | Lt => 
    let n := Z.div n (Z.Pos gcd) in
    let d := N.div d gcd in
    match N.compare d N.one with
    | Gt => Qq n d
    | Eq => Qz n
    | Lt => zero
    end
  | Eq => Qq n d
  | Gt => zero (* gcd = 0 => both numbers are 0 *)
  end.
   
 Definition add x y :=
  match x with
  | Qz zx =>
    match y with
    | Qz zy => Qz (Z.add zx zy)
    | Qq ny dy => 
      if N.eq_bool dy N.zero then x 
      else Qq (Z.add (Z.mul zx (Z.Pos dy)) ny) dy
    end
  | Qq nx dx =>
    if N.eq_bool dx N.zero then y 
    else match y with
    | Qz zy => Qq (Z.add nx (Z.mul zy (Z.Pos dx))) dx
    | Qq ny dy =>
      if N.eq_bool dy N.zero then x
      else
       let n := Z.add (Z.mul nx (Z.Pos dy)) (Z.mul ny (Z.Pos dx)) in
       let d := N.mul dx dy in
       Qq n d
    end
  end.

 Definition add_norm x y :=
  match x with
  | Qz zx =>
    match y with
    | Qz zy => Qz (Z.add zx zy)
    | Qq ny dy =>  
      if N.eq_bool dy N.zero then x 
      else norm (Z.add (Z.mul zx (Z.Pos dy)) ny) dy
    end
  | Qq nx dx =>
    if N.eq_bool dx N.zero then y 
    else match y with
    | Qz zy => norm (Z.add nx (Z.mul zy (Z.Pos dx))) dx
    | Qq ny dy =>
      if N.eq_bool dy N.zero then x
      else
       let n := Z.add (Z.mul nx (Z.Pos dy)) (Z.mul ny (Z.Pos dx)) in
       let d := N.mul dx dy in
       norm n d
    end
  end.
 
 Definition sub x y := add x (opp y).

 Definition sub_norm x y := add_norm x (opp y).

 Definition mul x y :=
  match x, y with
  | Qz zx, Qz zy => Qz (Z.mul zx zy)
  | Qz zx, Qq ny dy => Qq (Z.mul zx ny) dy
  | Qq nx dx, Qz zy => Qq (Z.mul nx zy) dx
  | Qq nx dx, Qq ny dy => Qq (Z.mul nx ny) (N.mul dx dy)
  end.

Definition mul_norm x y := 
 match x, y with
 | Qz zx, Qz zy => Qz (Z.mul zx zy)
 | Qz zx, Qq ny dy =>
   if Z.eq_bool zx Z.zero then zero
   else	
     let d := N.succ dy in
     let gcd := N.gcd (Z.to_N zx) d in
     if N.eq_bool gcd N.one then Qq (Z.mul zx ny) dy
     else 
       let zx := Z.div zx (Z.Pos gcd) in
       let d := N.div d gcd in
       if N.eq_bool d N.one then Qz (Z.mul zx ny)
       else Qq (Z.mul zx ny) (N.pred d)
 | Qq nx dx, Qz zy =>   
   if Z.eq_bool zy Z.zero then zero
   else	
     let d := N.succ dx in
     let gcd := N.gcd (Z.to_N zy) d in
     if N.eq_bool gcd N.one then Qq (Z.mul zy nx) dx
     else 
       let zy := Z.div zy (Z.Pos gcd) in
       let d := N.div d gcd in
       if N.eq_bool d N.one then Qz (Z.mul zy nx)
       else Qq (Z.mul zy nx) (N.pred d)
 | Qq nx dx, Qq ny dy => 
     let dx := N.succ dx in
     let dy := N.succ dy in
     let (nx, dy) := 
       let gcd := N.gcd (Z.to_N nx) dy in
       if N.eq_bool gcd N.one then (nx, dy)
       else (Z.div nx (Z.Pos gcd), N.div dy gcd) in
     let (ny, dx) := 
       let gcd := N.gcd (Z.to_N ny) dx in
       if N.eq_bool gcd N.one then (ny, dx)
       else (Z.div ny (Z.Pos gcd), N.div dx gcd) in
     let d := (N.mul dx dy) in
     if N.eq_bool d N.one then Qz (Z.mul ny nx) 
     else Qq (Z.mul ny nx) (N.pred d)
 end.


Definition inv x := 
 match x with
 | Qz (Z.Pos n) => Qq Z.one (N.pred n)
 | Qz (Z.Neg n) => Qq Z.minus_one (N.pred n)
 | Qq (Z.Pos n) d => Qq (Z.Pos (N.succ d)) (N.pred n)
 | Qq (Z.Neg n) d => Qq (Z.Neg (N.succ d)) (N.pred n)
 end.


Definition inv_norm x := 
 match x with
 | Qz (Z.Pos n) => if N.eq_bool n N.one then x else Qq Z.one (N.pred n)
 | Qz (Z.Neg n) => if N.eq_bool n N.one then x else Qq Z.minus_one n
 | Qq (Z.Pos n) d => let d := N.succ d in 
                  if N.eq_bool n N.one then Qz (Z.Pos d) 
                     else Qq (Z.Pos d) (N.pred n)
 | Qq (Z.Neg n) d => let d := N.succ d in 
                  if N.eq_bool n N.one then Qz (Z.Neg d) 
                     else Qq (Z.Pos d) (N.pred n)
 end.

 Definition square x :=
  match x with
  | Qz zx => Qz (Z.square zx)
  | Qq nx dx => Qq (Z.square nx) (N.square dx)
  end.

 Definition power_pos x p :=
  match x with
  | Qz zx => Qz (Z.power_pos zx p)
  | Qq nx dx => Qq (Z.power_pos nx p) (N.power_pos dx p)
  end.

End Q.

Module Qif.

 (* Troisieme solution :
    0 a de nombreuse representation :
         0, -0, 1/0, ... n/0,
    il faut alors faire attention avec la comparaison et l'addition 
    
    Les fonctions de normalization s'effectue seulement si les
    nombres sont grands.
 *)

 Definition t := q_type.

 Definition zero := Qz Z.zero.
 Definition one  := Qz Z.one.
 Definition minus_one := Qz Z.minus_one.

 Definition of_Z x := Qz (Z.of_Z x).

 Definition compare x y :=
  match x, y with
  | Qz zx, Qz zy => Z.compare zx zy
  | Qz zx, Qq ny dy => 
    if N.eq_bool dy N.zero then Z.compare zx Z.zero
    else Z.compare (Z.mul zx (Z.Pos dy)) ny
  | Qq nx dx, Qz zy => 
    if N.eq_bool dx N.zero then Z.compare Z.zero zy 
    else Z.compare nx (Z.mul zy (Z.Pos dx))
  | Qq nx dx, Qq ny dy =>
    match N.eq_bool dx N.zero, N.eq_bool dy N.zero with
    | true, true => Eq
    | true, false => Z.compare Z.zero ny
    | false, true => Z.compare nx Z.zero
    | false, false => Z.compare (Z.mul nx (Z.Pos dy)) (Z.mul ny (Z.Pos dx))
    end
  end.

 Definition opp x :=
  match x with
  | Qz zx => Qz (Z.opp zx)
  | Qq nx dx => Qq (Z.opp nx) dx
  end.


 Definition do_norm_n n := 
  match n with
  | N.N0 _ => false
  | N.N1 _ => false
  | N.N2 _ => false
  | N.N3 _ => false
  | N.N4 _ => false
  | N.N5 _ => false
  | N.N6 _ => false
  | N.N7 _ => false
  | N.N8 _ => false
  | N.N9 _ => true 
  | N.N10 _ => true
  | N.N11 _ => true
  | N.N12 _ => true
  | N.Nn n _ => true
  end.

 Definition do_norm_z z :=
  match z with
  | Z.Pos n => do_norm_n n
  | Z.Neg n => do_norm_n n
  end.

Require Import Bool.
(* Je pense que cette fonction normalise bien ... *)
 Definition norm n d :=
  if andb (do_norm_z n) (do_norm_n d) then
  let gcd := N.gcd (Z.to_N n) d in 
  match N.compare N.one gcd with
  | Lt => 
    let n := Z.div n (Z.Pos gcd) in
    let d := N.div d gcd in
    match N.compare d N.one with
    | Gt => Qq n d
    | Eq => Qz n
    | Lt => zero
    end
  | Eq => Qq n d
  | Gt => zero (* gcd = 0 => both numbers are 0 *)
  end
 else Qq n d.


   
 Definition add x y :=
  match x with
  | Qz zx =>
    match y with
    | Qz zy => Qz (Z.add zx zy)
    | Qq ny dy => 
      if N.eq_bool dy N.zero then x 
      else Qq (Z.add (Z.mul zx (Z.Pos dy)) ny) dy
    end
  | Qq nx dx =>
    if N.eq_bool dx N.zero then y 
    else match y with
    | Qz zy => Qq (Z.add nx (Z.mul zy (Z.Pos dx))) dx
    | Qq ny dy =>
      if N.eq_bool dy N.zero then x
      else
       let n := Z.add (Z.mul nx (Z.Pos dy)) (Z.mul ny (Z.Pos dx)) in
       let d := N.mul dx dy in
       Qq n d
    end
  end.

 Definition add_norm x y :=
  match x with
  | Qz zx =>
    match y with
    | Qz zy => Qz (Z.add zx zy)
    | Qq ny dy =>  
      if N.eq_bool dy N.zero then x 
      else norm (Z.add (Z.mul zx (Z.Pos dy)) ny) dy
    end
  | Qq nx dx =>
    if N.eq_bool dx N.zero then y 
    else match y with
    | Qz zy => norm (Z.add nx (Z.mul zy (Z.Pos dx))) dx
    | Qq ny dy =>
      if N.eq_bool dy N.zero then x
      else
       let n := Z.add (Z.mul nx (Z.Pos dy)) (Z.mul ny (Z.Pos dx)) in
       let d := N.mul dx dy in
       norm n d
    end
  end.
 
 Definition sub x y := add x (opp y).

 Definition sub_norm x y := add_norm x (opp y).

 Definition mul x y :=
  match x, y with
  | Qz zx, Qz zy => Qz (Z.mul zx zy)
  | Qz zx, Qq ny dy => Qq (Z.mul zx ny) dy
  | Qq nx dx, Qz zy => Qq (Z.mul nx zy) dx
  | Qq nx dx, Qq ny dy => Qq (Z.mul nx ny) (N.mul dx dy)
  end.

 Definition mul_norm x y := 
  match x, y with
  | Qz zx, Qz zy => Qz (Z.mul zx zy)
  | Qz zx, Qq ny dy => norm (Z.mul zx ny) dy
  | Qq nx dx, Qz zy => norm (Z.mul nx zy) dx
  | Qq nx dx, Qq ny dy => norm (Z.mul nx ny) (N.mul dx dy)
  end.

 Definition inv x := 
  match x with
  | Qz (Z.Pos n) => Qq Z.one n
  | Qz (Z.Neg n) => Qq Z.minus_one n
  | Qq (Z.Pos n) d => Qq (Z.Pos d) n
  | Qq (Z.Neg n) d => Qq (Z.Neg d) n
  end.

 Definition inv_norm x := 
  match x with
  | Qz (Z.Pos n) => 
    if N.eq_bool n N.zero then zero else Qq Z.one n
  | Qz (Z.Neg n) => 
    if N.eq_bool n N.zero then zero else Qq Z.minus_one n
  | Qq (Z.Pos n) d => 
    if N.eq_bool n N.zero then zero else Qq (Z.Pos d) n
  | Qq (Z.Neg n) d => 
    if N.eq_bool n N.zero then zero else Qq (Z.Neg d) n
  end.

 Definition square x :=
  match x with
  | Qz zx => Qz (Z.square zx)
  | Qq nx dx => Qq (Z.square nx) (N.square dx)
  end.

 Definition power_pos x p :=
  match x with
  | Qz zx => Qz (Z.power_pos zx p)
  | Qq nx dx => Qq (Z.power_pos nx p) (N.power_pos dx p)
  end.

End Qif.

Module Qbi.

 (* Troisieme solution :
    0 a de nombreuse representation :
         0, -0, 1/0, ... n/0,
    il faut alors faire attention avec la comparaison et l'addition 
    
    Les fonctions de normalization s'effectue seulement si les
    nombres sont grands.
 *)

 Definition t := q_type.

 Definition zero := Qz Z.zero.
 Definition one  := Qz Z.one.
 Definition minus_one := Qz Z.minus_one.

 Definition of_Z x := Qz (Z.of_Z x).

 Definition compare x y :=
  match x, y with
  | Qz zx, Qz zy => Z.compare zx zy
  | Qz zx, Qq ny dy => 
    if N.eq_bool dy N.zero then Z.compare zx Z.zero
    else
      match Z.cmp_sign zx ny with
      | Lt => Lt 
      | Gt => Gt
      | Eq => Z.compare (Z.mul zx (Z.Pos dy)) ny
      end
  | Qq nx dx, Qz zy =>
    if N.eq_bool dx N.zero then Z.compare Z.zero zy     
    else
      match Z.cmp_sign nx zy with
      | Lt => Lt
      | Gt => Gt
      | Eq => Z.compare nx (Z.mul zy (Z.Pos dx))
      end
  | Qq nx dx, Qq ny dy =>
    match N.eq_bool dx N.zero, N.eq_bool dy N.zero with
    | true, true => Eq
    | true, false => Z.compare Z.zero ny
    | false, true => Z.compare nx Z.zero
    | false, false =>
      match Z.cmp_sign nx ny with
      | Lt => Lt
      | Gt => Gt
      | Eq => Z.compare (Z.mul nx (Z.Pos dy)) (Z.mul ny (Z.Pos dx))
      end
    end
  end.

 Definition opp x :=
  match x with
  | Qz zx => Qz (Z.opp zx)
  | Qq nx dx => Qq (Z.opp nx) dx
  end.


 Definition do_norm_n n := 
  match n with
  | N.N0 _ => false
  | N.N1 _ => false
  | N.N2 _ => false
  | N.N3 _ => false
  | N.N4 _ => false
  | N.N5 _ => false
  | N.N6 _ => false
  | N.N7 _ => false
  | N.N8 _ => false
  | N.N9 _ => true 
  | N.N10 _ => true
  | N.N11 _ => true
  | N.N12 _ => true
  | N.Nn n _ => true
  end.
 
 Definition do_norm_z z :=
  match z with
  | Z.Pos n => do_norm_n n
  | Z.Neg n => do_norm_n n
  end.

(* Je pense que cette fonction normalise bien ... *)
 Definition norm n d :=
  if andb (do_norm_z n) (do_norm_n d) then
  let gcd := N.gcd (Z.to_N n) d in 
  match N.compare N.one gcd with
  | Lt => 
    let n := Z.div n (Z.Pos gcd) in
    let d := N.div d gcd in
    match N.compare d N.one with
    | Gt => Qq n d
    | Eq => Qz n
    | Lt => zero
    end
  | Eq => Qq n d
  | Gt => zero (* gcd = 0 => both numbers are 0 *)
  end
 else Qq n d.

   
 Definition add x y :=
  match x with
  | Qz zx =>
    match y with
    | Qz zy => Qz (Z.add zx zy)
    | Qq ny dy => 
      if N.eq_bool dy N.zero then x 
      else Qq (Z.add (Z.mul zx (Z.Pos dy)) ny) dy
    end
  | Qq nx dx =>
    if N.eq_bool dx N.zero then y 
    else match y with
    | Qz zy => Qq (Z.add nx (Z.mul zy (Z.Pos dx))) dx
    | Qq ny dy =>
      if N.eq_bool dy N.zero then x
      else
       if N.eq_bool dx dy then
         let n := Z.add nx ny in
         Qq n dx
       else
         let n := Z.add (Z.mul nx (Z.Pos dy)) (Z.mul ny (Z.Pos dx)) in
         let d := N.mul dx dy in
         Qq n d
    end
  end.

 Definition add_norm x y :=
  match x with
  | Qz zx =>
    match y with
    | Qz zy => Qz (Z.add zx zy)
    | Qq ny dy =>  
      if N.eq_bool dy N.zero then x 
      else 
        norm (Z.add (Z.mul zx (Z.Pos dy)) ny) dy
    end
  | Qq nx dx =>
    if N.eq_bool dx N.zero then y 
    else match y with
    | Qz zy => norm (Z.add nx (Z.mul zy (Z.Pos dx))) dx
    | Qq ny dy =>
      if N.eq_bool dy N.zero then x
      else
       if N.eq_bool dx dy then
         let n := Z.add nx ny in
         norm n dx
       else
         let n := Z.add (Z.mul nx (Z.Pos dy)) (Z.mul ny (Z.Pos dx)) in
         let d := N.mul dx dy in
         norm n d
    end
  end.
 
 Definition sub x y := add x (opp y).

 Definition sub_norm x y := add_norm x (opp y).

 Definition mul x y :=
  match x, y with
  | Qz zx, Qz zy => Qz (Z.mul zx zy)
  | Qz zx, Qq ny dy => Qq (Z.mul zx ny) dy
  | Qq nx dx, Qz zy => Qq (Z.mul nx zy) dx
  | Qq nx dx, Qq ny dy => Qq (Z.mul nx ny) (N.mul dx dy)
  end.

 Definition mul_norm x y := 
  match x, y with
  | Qz zx, Qz zy => Qz (Z.mul zx zy)
  | Qz zx, Qq ny dy => mul (Qz ny) (norm zx dy)
  | Qq nx dx, Qz zy => mul (Qz nx) (norm zy dx)
  | Qq nx dx, Qq ny dy => mul (norm nx dy) (norm ny dx)
  end.

 Definition inv x := 
  match x with
  | Qz (Z.Pos n) => Qq Z.one n
  | Qz (Z.Neg n) => Qq Z.minus_one n
  | Qq (Z.Pos n) d => Qq (Z.Pos d) n
  | Qq (Z.Neg n) d => Qq (Z.Neg d) n
  end.

 Definition inv_norm x := 
  match x with
  | Qz (Z.Pos n) => 
    if N.eq_bool n N.zero then zero else Qq Z.one n
  | Qz (Z.Neg n) => 
    if N.eq_bool n N.zero then zero else Qq Z.minus_one n
  | Qq (Z.Pos n) d => 
    if N.eq_bool n N.zero then zero else Qq (Z.Pos d) n
  | Qq (Z.Neg n) d => 
    if N.eq_bool n N.zero then zero else Qq (Z.Neg d) n
  end.

 Definition square x :=
  match x with
  | Qz zx => Qz (Z.square zx)
  | Qq nx dx => Qq (Z.square nx) (N.square dx)
  end.

 Definition power_pos x p :=
  match x with
  | Qz zx => Qz (Z.power_pos zx p)
  | Qq nx dx => Qq (Z.power_pos nx p) (N.power_pos dx p)
  end.

End Qbi.




