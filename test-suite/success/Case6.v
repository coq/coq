Fixpoint eqdec [n:nat] : (m:nat) n=m \/ ~n=m := 
[m:nat]
 <[n,m:nat] n=m \/ ~n=m>Cases n m of
      O   O   => (or_introl ? ~O=O (refl_equal ? O))

   |  O (S x) => (or_intror O=(S x) ? (discr_r x))

   | (S x) O  => (or_intror ? ~(S x)=O (discr_l x))

   | ((S x) as N) ((S y) as M) =>  
      <N=M\/~N=M>Cases (eqdec x y) of
        (or_introl h) => (or_introl  ? ~N=M (f_equal nat nat S x y h))
      | (or_intror h) => (or_intror N=M ? (ff x y h))   
      end
 end.
