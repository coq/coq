
Definition Berry := [x,y,z:bool] 
  Cases x y z of 
     true false _ => O
   | false _ true => (S O)
   | _ true false => (S (S O))
end.
