(* Was raising an anomaly before 8.13 *)
Check let 'tt := tt in
      let X := nat in
      let b : bool := _ in
      (fun n : nat => 0 : X) : _.

(* Was raising an ill-typed instance error before 8.13 *)
Check let 'tt := tt in
      let X := nat in
      let b : bool := true in
      (fun n : nat => 0 : X) : _.
