Require Import Bool.
Require Import ZArith.
Require Import Arith.
Require Export BigN.
Require Export BigZ.

Inductive q_type : Set := 
 | Qz : BigZ.t -> q_type
 | Qq : BigZ.t -> BigN.t -> q_type.

Definition print_type x := 
 match x with
 | Qz _ => Z
 | _ => (Z*Z)%type
 end.

Definition print x :=
 match x return print_type x with
 | Qz zx => BigZ.to_Z zx
 | Qq nx dx => (BigZ.to_Z nx, BigN.to_Z dx)
 end.

Module Qp.

 Definition t := q_type.

 Definition zero := Qz BigZ.zero.
 Definition one  := Qz BigZ.one.
 Definition minus_one := Qz BigZ.minus_one.

 Definition of_Z x := Qz (BigZ.of_Z x).

 Definition d_to_Z d := BigZ.Pos (BigN.succ d).

 Definition compare x y :=
  match x, y with
  | Qz zx, Qz zy => BigZ.compare zx zy
  | Qz zx, Qq ny dy => BigZ.compare (BigZ.mul zx (d_to_Z dy)) ny
  | Qq nx dy, Qz zy => BigZ.compare nx (BigZ.mul zy (d_to_Z dy))
  | Qq nx dx, Qq ny dy =>
    BigZ.compare (BigZ.mul nx (d_to_Z dy)) (BigZ.mul ny (d_to_Z dx))
  end.

 Definition opp x :=
  match x with
  | Qz zx => Qz (BigZ.opp zx)
  | Qq nx dx => Qq (BigZ.opp nx) dx
  end.

(* Inv d > 0, Pour la forme normal unique on veut d > 1 *)
 Definition norm n d :=
  if BigZ.eq_bool n BigZ.zero then zero
  else
    let gcd := BigN.gcd (BigZ.to_N n) d in
    if BigN.eq_bool gcd BigN.one then Qq n (BigN.pred d)
    else	
      let n := BigZ.div n (BigZ.Pos gcd) in
      let d := BigN.div d gcd in
      if BigN.eq_bool d BigN.one then Qz n
      else Qq n (BigN.pred d).
   
 Definition add x y :=
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.add zx zy)
  | Qz zx, Qq ny dy => Qq (BigZ.add (BigZ.mul zx (d_to_Z dy)) ny) dy
  | Qq nx dx, Qz zy => Qq (BigZ.add nx (BigZ.mul zy (d_to_Z dx))) dx
  | Qq nx dx, Qq ny dy => 
    let dx' := BigN.succ dx in
    let dy' := BigN.succ dy in
    let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy')) (BigZ.mul ny (BigZ.Pos dx')) in
    let d := BigN.pred (BigN.mul dx' dy') in
    Qq n d
  end.

 Definition add_norm x y := 
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.add zx zy)
  | Qz zx, Qq ny dy => 
    let d := BigN.succ dy in
    norm (BigZ.add (BigZ.mul zx (BigZ.Pos d)) ny) d 
  | Qq nx dx, Qz zy =>
    let d := BigN.succ dx in
    norm (BigZ.add (BigZ.mul zy (BigZ.Pos d)) nx) d
  | Qq nx dx, Qq ny dy =>
    let dx' := BigN.succ dx in
    let dy' := BigN.succ dy in
    let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy')) (BigZ.mul ny (BigZ.Pos dx')) in
    let d := BigN.mul dx' dy' in
    norm n d 
  end.
 
 Definition sub x y := add x (opp y).

 Definition sub_norm x y := add_norm x (opp y).

 Definition mul x y :=
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.mul zx zy)
  | Qz zx, Qq ny dy => Qq (BigZ.mul zx ny) dy
  | Qq nx dx, Qz zy => Qq (BigZ.mul nx zy) dx
  | Qq nx dx, Qq ny dy => 
    Qq (BigZ.mul nx ny) (BigN.pred (BigN.mul (BigN.succ dx) (BigN.succ dy)))
  end.

 Definition mul_norm x y := 
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.mul zx zy)
  | Qz zx, Qq ny dy =>
    if BigZ.eq_bool zx BigZ.zero then zero
    else	
      let d := BigN.succ dy in
      let gcd := BigN.gcd (BigZ.to_N zx) d in
      if BigN.eq_bool gcd BigN.one then Qq (BigZ.mul zx ny) dy
      else 
        let zx := BigZ.div zx (BigZ.Pos gcd) in
        let d := BigN.div d gcd in
        if BigN.eq_bool d BigN.one then Qz (BigZ.mul zx ny)
        else Qq (BigZ.mul zx ny) (BigN.pred d)
  | Qq nx dx, Qz zy =>   
    if BigZ.eq_bool zy BigZ.zero then zero
    else	
      let d := BigN.succ dx in
      let gcd := BigN.gcd (BigZ.to_N zy) d in
      if BigN.eq_bool gcd BigN.one then Qq (BigZ.mul zy nx) dx
      else 
        let zy := BigZ.div zy (BigZ.Pos gcd) in
        let d := BigN.div d gcd in
        if BigN.eq_bool d BigN.one then Qz (BigZ.mul zy nx)
        else Qq (BigZ.mul zy nx) (BigN.pred d)
  | Qq nx dx, Qq ny dy => 
    norm (BigZ.mul nx ny) (BigN.mul (BigN.succ dx) (BigN.succ dy))
  end.

 Definition inv x := 
  match x with
  | Qz (BigZ.Pos n) => 
    if BigN.eq_bool n BigN.zero then zero else Qq BigZ.one (BigN.pred n)
  | Qz (BigZ.Neg n) => 
    if BigN.eq_bool n BigN.zero then zero else Qq BigZ.minus_one (BigN.pred n)
  | Qq (BigZ.Pos n) d => 
    if BigN.eq_bool n BigN.zero then zero else Qq (BigZ.Pos (BigN.succ d)) (BigN.pred n)
  | Qq (BigZ.Neg n) d => 
    if BigN.eq_bool n BigN.zero then zero else Qq (BigZ.Neg (BigN.succ d)) (BigN.pred n)
  end.

Definition inv_norm x := 
 match x with
 | Qz (BigZ.Pos n) => 
      if BigN.eq_bool n BigN.zero then zero else
      if BigN.eq_bool n BigN.one then x else Qq BigZ.one (BigN.pred n)
 | Qz (BigZ.Neg n) => 
      if BigN.eq_bool n BigN.zero then zero  else
      if BigN.eq_bool n BigN.one then x else Qq BigZ.minus_one n
 | Qq (BigZ.Pos n) d => let d := BigN.succ d in 
                  if BigN.eq_bool n BigN.one then Qz (BigZ.Pos d) 
                     else Qq (BigZ.Pos d) (BigN.pred n)
 | Qq (BigZ.Neg n) d => let d := BigN.succ d in 
                  if BigN.eq_bool n BigN.one then Qz (BigZ.Neg d) 
                     else Qq (BigZ.Pos d) (BigN.pred n)
 end.


 Definition square x :=
  match x with
  | Qz zx => Qz (BigZ.square zx)
  | Qq nx dx => Qq (BigZ.square nx) (BigN.pred (BigN.square (BigN.succ dx)))
  end.

 Definition power_pos x p :=
  match x with
  | Qz zx => Qz (BigZ.power_pos zx p)
  | Qq nx dx => Qq (BigZ.power_pos nx p) (BigN.pred (BigN.power_pos (BigN.succ dx) p))
  end.

End Qp.


Module Qv.

 (* /!\  Invariant maintenu par les fonctions :
         - le denominateur n'est jamais nul *)

 Definition t := q_type.

 Definition zero := Qz BigZ.zero.
 Definition one  := Qz BigZ.one.
 Definition minus_one := Qz BigZ.minus_one.

 Definition of_Z x := Qz (BigZ.of_Z x).

 Definition is_valid x := 
  match x with
  | Qz _ => True
  | Qq n d => if BigN.eq_bool d BigN.zero then False else True
  end.
 (* Les fonctions doivent assurer que si leur arguments sont valides alors
    le resultat est correct et valide (si c'est un Q) 
 *)

 Definition compare x y :=
  match x, y with
  | Qz zx, Qz zy => BigZ.compare zx zy
  | Qz zx, Qq ny dy => BigZ.compare (BigZ.mul zx (BigZ.Pos dy)) ny
  | Qq nx dx, Qz zy => BigZ.compare BigZ.zero zy 
  | Qq nx dx, Qq ny dy => BigZ.compare (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx))
  end.

 Definition opp x :=
  match x with
  | Qz zx => Qz (BigZ.opp zx)
  | Qq nx dx => Qq (BigZ.opp nx) dx
  end.

 Definition norm n d :=
  if BigZ.eq_bool n BigZ.zero then zero
  else
    let gcd := BigN.gcd (BigZ.to_N n) d in
    if BigN.eq_bool gcd BigN.one then Qq n d
    else	
      let n := BigZ.div n (BigZ.Pos gcd) in
      let d := BigN.div d gcd in
      if BigN.eq_bool d BigN.one then Qz n
      else Qq n d.
   
 Definition add x y :=
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.add zx zy)
  | Qz zx, Qq ny dy => Qq (BigZ.add (BigZ.mul zx (BigZ.Pos dy)) ny) dy
  | Qq nx dx, Qz zy => Qq (BigZ.add nx (BigZ.mul zy (BigZ.Pos dx))) dx
  | Qq nx dx, Qq ny dy => 
    let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx)) in
    let d := BigN.mul dx dy in
    Qq n d
  end.

 Definition add_norm x y := 
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.add zx zy)
  | Qz zx, Qq ny dy => 
    norm (BigZ.add (BigZ.mul zx (BigZ.Pos dy)) ny) dy 
  | Qq nx dx, Qz zy =>
    norm (BigZ.add (BigZ.mul zy (BigZ.Pos dx)) nx) dx
  | Qq nx dx, Qq ny dy =>
    let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx)) in
    let d := BigN.mul dx dy in
    norm n d 
  end.
 
 Definition sub x y := add x (opp y).

 Definition sub_norm x y := add_norm x (opp y).

 Definition mul x y :=
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.mul zx zy)
  | Qz zx, Qq ny dy => Qq (BigZ.mul zx ny) dy
  | Qq nx dx, Qz zy => Qq (BigZ.mul nx zy) dx
  | Qq nx dx, Qq ny dy => 
    Qq (BigZ.mul nx ny) (BigN.mul dx dy)
  end.

 Definition mul_norm x y := 
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.mul zx zy)
  | Qz zx, Qq ny dy =>
    if BigZ.eq_bool zx BigZ.zero then zero
    else	
      let gcd := BigN.gcd (BigZ.to_N zx) dy in
      if BigN.eq_bool gcd BigN.one then Qq (BigZ.mul zx ny) dy
      else 
        let zx := BigZ.div zx (BigZ.Pos gcd) in
        let d := BigN.div dy gcd in
        if BigN.eq_bool d BigN.one then Qz (BigZ.mul zx ny)
        else Qq (BigZ.mul zx ny) d
  | Qq nx dx, Qz zy =>   
    if BigZ.eq_bool zy BigZ.zero then zero
    else	
      let gcd := BigN.gcd (BigZ.to_N zy) dx in
      if BigN.eq_bool gcd BigN.one then Qq (BigZ.mul zy nx) dx
      else 
        let zy := BigZ.div zy (BigZ.Pos gcd) in
        let d := BigN.div dx gcd in
        if BigN.eq_bool d BigN.one then Qz (BigZ.mul zy nx)
        else Qq (BigZ.mul zy nx) d
  | Qq nx dx, Qq ny dy => norm (BigZ.mul nx ny) (BigN.mul dx dy)
  end.

 Definition inv x := 
  match x with
  | Qz (BigZ.Pos n) => 
    if BigN.eq_bool n BigN.zero then zero else Qq BigZ.one n
  | Qz (BigZ.Neg n) => 
    if BigN.eq_bool n BigN.zero then zero else Qq BigZ.minus_one n
  | Qq (BigZ.Pos n) d => 
    if BigN.eq_bool n BigN.zero then zero else Qq (BigZ.Pos d) n
  | Qq (BigZ.Neg n) d => 
    if BigN.eq_bool n BigN.zero then zero else Qq (BigZ.Neg d) n
  end.

 Definition square x :=
  match x with
  | Qz zx => Qz (BigZ.square zx)
  | Qq nx dx => Qq (BigZ.square nx) (BigN.square dx)
  end.

 Definition power_pos x p :=
  match x with
  | Qz zx => Qz (BigZ.power_pos zx p)
  | Qq nx dx => Qq (BigZ.power_pos nx p) (BigN.power_pos dx p)
  end.

End Qv.

Module Q.

 (* Troisieme solution :
    0 a de nombreuse representation :
         0, -0, 1/0, ... n/0,
    il faut alors faire attention avec la comparaison et l'addition 
 *)

 Definition t := q_type.

 Definition zero := Qz BigZ.zero.
 Definition one  := Qz BigZ.one.
 Definition minus_one := Qz BigZ.minus_one.

 Definition of_Z x := Qz (BigZ.of_Z x).

 Definition compare x y :=
  match x, y with
  | Qz zx, Qz zy => BigZ.compare zx zy
  | Qz zx, Qq ny dy => 
    if BigN.eq_bool dy BigN.zero then BigZ.compare zx BigZ.zero
    else BigZ.compare (BigZ.mul zx (BigZ.Pos dy)) ny
  | Qq nx dx, Qz zy => 
    if BigN.eq_bool dx BigN.zero then BigZ.compare BigZ.zero zy 
    else BigZ.compare nx (BigZ.mul zy (BigZ.Pos dx))
  | Qq nx dx, Qq ny dy =>
    match BigN.eq_bool dx BigN.zero, BigN.eq_bool dy BigN.zero with
    | true, true => Eq
    | true, false => BigZ.compare BigZ.zero ny
    | false, true => BigZ.compare nx BigZ.zero
    | false, false => BigZ.compare (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx))
    end
  end.

 Definition opp x :=
  match x with
  | Qz zx => Qz (BigZ.opp zx)
  | Qq nx dx => Qq (BigZ.opp nx) dx
  end.

(* Je pense que cette fonction normalise bien ... *)
 Definition norm n d :=
  let gcd := BigN.gcd (BigZ.to_N n) d in 
  match BigN.compare BigN.one gcd with
  | Lt => 
    let n := BigZ.div n (BigZ.Pos gcd) in
    let d := BigN.div d gcd in
    match BigN.compare d BigN.one with
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
    | Qz zy => Qz (BigZ.add zx zy)
    | Qq ny dy => 
      if BigN.eq_bool dy BigN.zero then x 
      else Qq (BigZ.add (BigZ.mul zx (BigZ.Pos dy)) ny) dy
    end
  | Qq nx dx =>
    if BigN.eq_bool dx BigN.zero then y 
    else match y with
    | Qz zy => Qq (BigZ.add nx (BigZ.mul zy (BigZ.Pos dx))) dx
    | Qq ny dy =>
      if BigN.eq_bool dy BigN.zero then x
      else
       let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx)) in
       let d := BigN.mul dx dy in
       Qq n d
    end
  end.

 Definition add_norm x y :=
  match x with
  | Qz zx =>
    match y with
    | Qz zy => Qz (BigZ.add zx zy)
    | Qq ny dy =>  
      if BigN.eq_bool dy BigN.zero then x 
      else norm (BigZ.add (BigZ.mul zx (BigZ.Pos dy)) ny) dy
    end
  | Qq nx dx =>
    if BigN.eq_bool dx BigN.zero then y 
    else match y with
    | Qz zy => norm (BigZ.add nx (BigZ.mul zy (BigZ.Pos dx))) dx
    | Qq ny dy =>
      if BigN.eq_bool dy BigN.zero then x
      else
       let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx)) in
       let d := BigN.mul dx dy in
       norm n d
    end
  end.
 
 Definition sub x y := add x (opp y).

 Definition sub_norm x y := add_norm x (opp y).

 Definition mul x y :=
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.mul zx zy)
  | Qz zx, Qq ny dy => Qq (BigZ.mul zx ny) dy
  | Qq nx dx, Qz zy => Qq (BigZ.mul nx zy) dx
  | Qq nx dx, Qq ny dy => Qq (BigZ.mul nx ny) (BigN.mul dx dy)
  end.

Definition mul_norm x y := 
 match x, y with
 | Qz zx, Qz zy => Qz (BigZ.mul zx zy)
 | Qz zx, Qq ny dy =>
   if BigZ.eq_bool zx BigZ.zero then zero
   else	
     let d := BigN.succ dy in
     let gcd := BigN.gcd (BigZ.to_N zx) d in
     if BigN.eq_bool gcd BigN.one then Qq (BigZ.mul zx ny) dy
     else 
       let zx := BigZ.div zx (BigZ.Pos gcd) in
       let d := BigN.div d gcd in
       if BigN.eq_bool d BigN.one then Qz (BigZ.mul zx ny)
       else Qq (BigZ.mul zx ny) d
 | Qq nx dx, Qz zy =>   
   if BigZ.eq_bool zy BigZ.zero then zero
   else	
     let d := BigN.succ dx in
     let gcd := BigN.gcd (BigZ.to_N zy) d in
     if BigN.eq_bool gcd BigN.one then Qq (BigZ.mul zy nx) dx
     else 
       let zy := BigZ.div zy (BigZ.Pos gcd) in
       let d := BigN.div d gcd in
       if BigN.eq_bool d BigN.one then Qz (BigZ.mul zy nx)
       else Qq (BigZ.mul zy nx) d
 | Qq nx dx, Qq ny dy => 
     let (nx, dy) := 
       let gcd := BigN.gcd (BigZ.to_N nx) dy in
       if BigN.eq_bool gcd BigN.one then (nx, dy)
       else (BigZ.div nx (BigZ.Pos gcd), BigN.div dy gcd) in
     let (ny, dx) := 
       let gcd := BigN.gcd (BigZ.to_N ny) dx in
       if BigN.eq_bool gcd BigN.one then (ny, dx)
       else (BigZ.div ny (BigZ.Pos gcd), BigN.div dx gcd) in
     let d := (BigN.mul dx dy) in
     if BigN.eq_bool d BigN.one then Qz (BigZ.mul ny nx) 
     else Qq (BigZ.mul ny nx) d
 end.


Definition inv x := 
 match x with
 | Qz (BigZ.Pos n) => Qq BigZ.one (BigN.pred n)
 | Qz (BigZ.Neg n) => Qq BigZ.minus_one (BigN.pred n)
 | Qq (BigZ.Pos n) d => Qq (BigZ.Pos (BigN.succ d)) (BigN.pred n)
 | Qq (BigZ.Neg n) d => Qq (BigZ.Neg (BigN.succ d)) (BigN.pred n)
 end.


Definition inv_norm x := 
 match x with
 | Qz (BigZ.Pos n) => if BigN.eq_bool n BigN.one then x else Qq BigZ.one (BigN.pred n)
 | Qz (BigZ.Neg n) => if BigN.eq_bool n BigN.one then x else Qq BigZ.minus_one n
 | Qq (BigZ.Pos n) d => let d := BigN.succ d in 
                  if BigN.eq_bool n BigN.one then Qz (BigZ.Pos d) 
                     else Qq (BigZ.Pos d) (BigN.pred n)
 | Qq (BigZ.Neg n) d => let d := BigN.succ d in 
                  if BigN.eq_bool n BigN.one then Qz (BigZ.Neg d) 
                     else Qq (BigZ.Pos d) (BigN.pred n)
 end.

 Definition square x :=
  match x with
  | Qz zx => Qz (BigZ.square zx)
  | Qq nx dx => Qq (BigZ.square nx) (BigN.square dx)
  end.

 Definition power_pos x p :=
  match x with
  | Qz zx => Qz (BigZ.power_pos zx p)
  | Qq nx dx => Qq (BigZ.power_pos nx p) (BigN.power_pos dx p)
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

 Definition zero := Qz BigZ.zero.
 Definition one  := Qz BigZ.one.
 Definition minus_one := Qz BigZ.minus_one.

 Definition of_Z x := Qz (BigZ.of_Z x).

 Definition compare x y :=
  match x, y with
  | Qz zx, Qz zy => BigZ.compare zx zy
  | Qz zx, Qq ny dy => 
    if BigN.eq_bool dy BigN.zero then BigZ.compare zx BigZ.zero
    else BigZ.compare (BigZ.mul zx (BigZ.Pos dy)) ny
  | Qq nx dx, Qz zy => 
    if BigN.eq_bool dx BigN.zero then BigZ.compare BigZ.zero zy 
    else BigZ.compare nx (BigZ.mul zy (BigZ.Pos dx))
  | Qq nx dx, Qq ny dy =>
    match BigN.eq_bool dx BigN.zero, BigN.eq_bool dy BigN.zero with
    | true, true => Eq
    | true, false => BigZ.compare BigZ.zero ny
    | false, true => BigZ.compare nx BigZ.zero
    | false, false => BigZ.compare (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx))
    end
  end.

 Definition opp x :=
  match x with
  | Qz zx => Qz (BigZ.opp zx)
  | Qq nx dx => Qq (BigZ.opp nx) dx
  end.


 Definition do_norm_n n := 
  match n with
  | BigN.N0 _ => false
  | BigN.N1 _ => false
  | BigN.N2 _ => false
  | BigN.N3 _ => false
  | BigN.N4 _ => false
  | BigN.N5 _ => false
  | BigN.N6 _ => false
  | BigN.N7 _ => false
  | BigN.N8 _ => false
  | BigN.N9 _ => true 
  | BigN.N10 _ => true
  | BigN.N11 _ => true
  | BigN.N12 _ => true
  | BigN.N13 _ => true
  | BigN.Nn n _ => true
  end.

 Definition do_norm_z z :=
  match z with
  | BigZ.Pos n => do_norm_n n
  | BigZ.Neg n => do_norm_n n
  end.

Require Import Bool.
(* Je pense que cette fonction normalise bien ... *)
 Definition norm n d :=
  if andb (do_norm_z n) (do_norm_n d) then
  let gcd := BigN.gcd (BigZ.to_N n) d in 
  match BigN.compare BigN.one gcd with
  | Lt => 
    let n := BigZ.div n (BigZ.Pos gcd) in
    let d := BigN.div d gcd in
    match BigN.compare d BigN.one with
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
    | Qz zy => Qz (BigZ.add zx zy)
    | Qq ny dy => 
      if BigN.eq_bool dy BigN.zero then x 
      else Qq (BigZ.add (BigZ.mul zx (BigZ.Pos dy)) ny) dy
    end
  | Qq nx dx =>
    if BigN.eq_bool dx BigN.zero then y 
    else match y with
    | Qz zy => Qq (BigZ.add nx (BigZ.mul zy (BigZ.Pos dx))) dx
    | Qq ny dy =>
      if BigN.eq_bool dy BigN.zero then x
      else
       let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx)) in
       let d := BigN.mul dx dy in
       Qq n d
    end
  end.

 Definition add_norm x y :=
  match x with
  | Qz zx =>
    match y with
    | Qz zy => Qz (BigZ.add zx zy)
    | Qq ny dy =>  
      if BigN.eq_bool dy BigN.zero then x 
      else norm (BigZ.add (BigZ.mul zx (BigZ.Pos dy)) ny) dy
    end
  | Qq nx dx =>
    if BigN.eq_bool dx BigN.zero then y 
    else match y with
    | Qz zy => norm (BigZ.add nx (BigZ.mul zy (BigZ.Pos dx))) dx
    | Qq ny dy =>
      if BigN.eq_bool dy BigN.zero then x
      else
       let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx)) in
       let d := BigN.mul dx dy in
       norm n d
    end
  end.
 
 Definition sub x y := add x (opp y).

 Definition sub_norm x y := add_norm x (opp y).

 Definition mul x y :=
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.mul zx zy)
  | Qz zx, Qq ny dy => Qq (BigZ.mul zx ny) dy
  | Qq nx dx, Qz zy => Qq (BigZ.mul nx zy) dx
  | Qq nx dx, Qq ny dy => Qq (BigZ.mul nx ny) (BigN.mul dx dy)
  end.

 Definition mul_norm x y := 
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.mul zx zy)
  | Qz zx, Qq ny dy => norm (BigZ.mul zx ny) dy
  | Qq nx dx, Qz zy => norm (BigZ.mul nx zy) dx
  | Qq nx dx, Qq ny dy => norm (BigZ.mul nx ny) (BigN.mul dx dy)
  end.

 Definition inv x := 
  match x with
  | Qz (BigZ.Pos n) => Qq BigZ.one n
  | Qz (BigZ.Neg n) => Qq BigZ.minus_one n
  | Qq (BigZ.Pos n) d => Qq (BigZ.Pos d) n
  | Qq (BigZ.Neg n) d => Qq (BigZ.Neg d) n
  end.

 Definition inv_norm x := 
  match x with
  | Qz (BigZ.Pos n) => 
    if BigN.eq_bool n BigN.zero then zero else Qq BigZ.one n
  | Qz (BigZ.Neg n) => 
    if BigN.eq_bool n BigN.zero then zero else Qq BigZ.minus_one n
  | Qq (BigZ.Pos n) d => 
    if BigN.eq_bool n BigN.zero then zero else Qq (BigZ.Pos d) n
  | Qq (BigZ.Neg n) d => 
    if BigN.eq_bool n BigN.zero then zero else Qq (BigZ.Neg d) n
  end.

 Definition square x :=
  match x with
  | Qz zx => Qz (BigZ.square zx)
  | Qq nx dx => Qq (BigZ.square nx) (BigN.square dx)
  end.

 Definition power_pos x p :=
  match x with
  | Qz zx => Qz (BigZ.power_pos zx p)
  | Qq nx dx => Qq (BigZ.power_pos nx p) (BigN.power_pos dx p)
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

 Definition zero := Qz BigZ.zero.
 Definition one  := Qz BigZ.one.
 Definition minus_one := Qz BigZ.minus_one.

 Definition of_Z x := Qz (BigZ.of_Z x).

 Definition compare x y :=
  match x, y with
  | Qz zx, Qz zy => BigZ.compare zx zy
  | Qz zx, Qq ny dy => 
    if BigN.eq_bool dy BigN.zero then BigZ.compare zx BigZ.zero
    else
      match BigZ.cmp_sign zx ny with
      | Lt => Lt 
      | Gt => Gt
      | Eq => BigZ.compare (BigZ.mul zx (BigZ.Pos dy)) ny
      end
  | Qq nx dx, Qz zy =>
    if BigN.eq_bool dx BigN.zero then BigZ.compare BigZ.zero zy     
    else
      match BigZ.cmp_sign nx zy with
      | Lt => Lt
      | Gt => Gt
      | Eq => BigZ.compare nx (BigZ.mul zy (BigZ.Pos dx))
      end
  | Qq nx dx, Qq ny dy =>
    match BigN.eq_bool dx BigN.zero, BigN.eq_bool dy BigN.zero with
    | true, true => Eq
    | true, false => BigZ.compare BigZ.zero ny
    | false, true => BigZ.compare nx BigZ.zero
    | false, false =>
      match BigZ.cmp_sign nx ny with
      | Lt => Lt
      | Gt => Gt
      | Eq => BigZ.compare (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx))
      end
    end
  end.

 Definition opp x :=
  match x with
  | Qz zx => Qz (BigZ.opp zx)
  | Qq nx dx => Qq (BigZ.opp nx) dx
  end.


 Definition do_norm_n n := 
  match n with
  | BigN.N0 _ => false
  | BigN.N1 _ => false
  | BigN.N2 _ => false
  | BigN.N3 _ => false
  | BigN.N4 _ => false
  | BigN.N5 _ => false
  | BigN.N6 _ => false
  | BigN.N7 _ => false
  | BigN.N8 _ => false
  | BigN.N9 _ => true 
  | BigN.N10 _ => true
  | BigN.N11 _ => true
  | BigN.N12 _ => true
  | BigN.N13 _ => true
  | BigN.Nn n _ => true
  end.
 
 Definition do_norm_z z :=
  match z with
  | BigZ.Pos n => do_norm_n n
  | BigZ.Neg n => do_norm_n n
  end.

(* Je pense que cette fonction normalise bien ... *)
 Definition norm n d :=
  if andb (do_norm_z n) (do_norm_n d) then
  let gcd := BigN.gcd (BigZ.to_N n) d in 
  match BigN.compare BigN.one gcd with
  | Lt => 
    let n := BigZ.div n (BigZ.Pos gcd) in
    let d := BigN.div d gcd in
    match BigN.compare d BigN.one with
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
    | Qz zy => Qz (BigZ.add zx zy)
    | Qq ny dy => 
      if BigN.eq_bool dy BigN.zero then x 
      else Qq (BigZ.add (BigZ.mul zx (BigZ.Pos dy)) ny) dy
    end
  | Qq nx dx =>
    if BigN.eq_bool dx BigN.zero then y 
    else match y with
    | Qz zy => Qq (BigZ.add nx (BigZ.mul zy (BigZ.Pos dx))) dx
    | Qq ny dy =>
      if BigN.eq_bool dy BigN.zero then x
      else
       if BigN.eq_bool dx dy then
         let n := BigZ.add nx ny in
         Qq n dx
       else
         let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx)) in
         let d := BigN.mul dx dy in
         Qq n d
    end
  end.

 Definition add_norm x y :=
  match x with
  | Qz zx =>
    match y with
    | Qz zy => Qz (BigZ.add zx zy)
    | Qq ny dy =>  
      if BigN.eq_bool dy BigN.zero then x 
      else 
        norm (BigZ.add (BigZ.mul zx (BigZ.Pos dy)) ny) dy
    end
  | Qq nx dx =>
    if BigN.eq_bool dx BigN.zero then y 
    else match y with
    | Qz zy => norm (BigZ.add nx (BigZ.mul zy (BigZ.Pos dx))) dx
    | Qq ny dy =>
      if BigN.eq_bool dy BigN.zero then x
      else
       if BigN.eq_bool dx dy then
         let n := BigZ.add nx ny in
         norm n dx
       else
         let n := BigZ.add (BigZ.mul nx (BigZ.Pos dy)) (BigZ.mul ny (BigZ.Pos dx)) in
         let d := BigN.mul dx dy in
         norm n d
    end
  end.
 
 Definition sub x y := add x (opp y).

 Definition sub_norm x y := add_norm x (opp y).

 Definition mul x y :=
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.mul zx zy)
  | Qz zx, Qq ny dy => Qq (BigZ.mul zx ny) dy
  | Qq nx dx, Qz zy => Qq (BigZ.mul nx zy) dx
  | Qq nx dx, Qq ny dy => Qq (BigZ.mul nx ny) (BigN.mul dx dy)
  end.

 Definition mul_norm x y := 
  match x, y with
  | Qz zx, Qz zy => Qz (BigZ.mul zx zy)
  | Qz zx, Qq ny dy => mul (Qz ny) (norm zx dy)
  | Qq nx dx, Qz zy => mul (Qz nx) (norm zy dx)
  | Qq nx dx, Qq ny dy => mul (norm nx dy) (norm ny dx)
  end.

 Definition inv x := 
  match x with
  | Qz (BigZ.Pos n) => Qq BigZ.one n
  | Qz (BigZ.Neg n) => Qq BigZ.minus_one n
  | Qq (BigZ.Pos n) d => Qq (BigZ.Pos d) n
  | Qq (BigZ.Neg n) d => Qq (BigZ.Neg d) n
  end.

 Definition inv_norm x := 
  match x with
  | Qz (BigZ.Pos n) => 
    if BigN.eq_bool n BigN.zero then zero else Qq BigZ.one n
  | Qz (BigZ.Neg n) => 
    if BigN.eq_bool n BigN.zero then zero else Qq BigZ.minus_one n
  | Qq (BigZ.Pos n) d => 
    if BigN.eq_bool n BigN.zero then zero else Qq (BigZ.Pos d) n
  | Qq (BigZ.Neg n) d => 
    if BigN.eq_bool n BigN.zero then zero else Qq (BigZ.Neg d) n
  end.

 Definition square x :=
  match x with
  | Qz zx => Qz (BigZ.square zx)
  | Qq nx dx => Qq (BigZ.square nx) (BigN.square dx)
  end.

 Definition power_pos x p :=
  match x with
  | Qz zx => Qz (BigZ.power_pos zx p)
  | Qq nx dx => Qq (BigZ.power_pos nx p) (BigN.power_pos dx p)
  end.

End Qbi.




