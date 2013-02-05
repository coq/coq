Check let TTT := Type in (fun (a b : @sigT TTT (fun A : TTT => A))
             (f : @projT1 TTT (fun A : TTT => A) a ->
                  @projT1 TTT (fun A : TTT => A) b) =>
           @eq_refl
             (@projT1 TTT (fun A : TTT => A) a ->
              @projT1 TTT (fun A : TTT => A) b)
             (fun x : @projT1 TTT (fun A : TTT => A) a => f x)) :
           forall (a b : @sigT TTT (fun A : TTT => A))
             (f : @projT1 TTT (fun A : TTT => A) a ->
                  @projT1 TTT (fun A : TTT => A) b),
           @eq
             (@projT1 TTT (fun A : TTT => A) a ->
              @projT1 TTT (fun A : TTT => A) b)
             (fun x : @projT1 TTT (fun A : TTT => A) a => f x) f.

