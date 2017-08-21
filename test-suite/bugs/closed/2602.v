Goal exists m, S m > 0.
eexists.
match goal with
 | |- context [ S ?a ] =>
     match goal with
       | |- S a > 0 => idtac
     end
end.
