
Inductive eqlong : (List nat)-> (List nat)-> Prop :=
 eql_cons : (n,m:nat)(x,y:(List nat)) 
            (eqlong x y) -> (eqlong (Cons nat n x) (Cons nat m y))
| eql_nil :  (eqlong (Nil nat) (Nil nat)).


Parameter V1 : (eqlong (Nil nat) (Nil nat))\/ ~(eqlong (Nil nat) (Nil nat)).
Parameter V2 : (a:nat)(x:(List nat))
      (eqlong (Nil nat) (Cons nat a x))\/ ~(eqlong (Nil nat)(Cons nat a x)).
Parameter V3 : (a:nat)(x:(List nat))
      (eqlong  (Cons nat a x)  (Nil nat))\/ ~(eqlong (Cons nat a x) (Nil nat)).
Parameter V4 : (a:nat)(x:(List nat))(b:nat)(y:(List nat))
      (eqlong  (Cons nat a x)(Cons nat b y))
        \/ ~(eqlong (Cons nat a x) (Cons nat b y)).

Parameter nff : (n,m:nat)(x,y:(List nat)) 
               ~(eqlong x y)-> ~(eqlong (Cons nat n x) (Cons nat m y)).
Parameter inv_r : (n:nat)(x:(List nat)) ~(eqlong (Nil nat) (Cons nat n x)).
Parameter inv_l : (n:nat)(x:(List nat)) ~(eqlong (Cons nat n x) (Nil nat)).

Fixpoint eqlongdec [x:(List nat)]: (y:(List nat))(eqlong x y)\/~(eqlong x y) :=
[y:(List nat)]
 <[x,y:(List nat)](eqlong x y)\/~(eqlong x y)>Cases x y of
      Nil Nil   => (or_introl ? ~(eqlong (Nil nat) (Nil nat))  eql_nil)

   |  Nil ((Cons a x) as L) =>(or_intror (eqlong (Nil nat) L)  ? (inv_r a x))

   |  ((Cons a x) as L) Nil => (or_intror (eqlong L (Nil nat)) ? (inv_l a x))

   | ((Cons a x) as L1) ((Cons b y) as L2) =>  
      <(eqlong L1 L2) \/~(eqlong L1 L2)>Cases (eqlongdec x y) of
        (or_introl h) => (or_introl  ? ~(eqlong L1 L2) (eql_cons a b x y h))
      | (or_intror h) => (or_intror (eqlong L1 L2) ? (nff a b x y h))   
      end
 end.


Type
 <[x,y:(List nat)](eqlong x y)\/~(eqlong x y)>Cases (Nil nat) (Nil nat) of
      Nil Nil   => (or_introl ? ~(eqlong (Nil nat) (Nil nat))  eql_nil)

   |  Nil ((Cons a x) as L) =>(or_intror (eqlong (Nil nat) L)  ? (inv_r a x))

   |  ((Cons a x) as L) Nil => (or_intror (eqlong L (Nil nat)) ? (inv_l a x))

   | ((Cons a x) as L1) ((Cons b y) as L2) =>  
      <(eqlong L1 L2) \/~(eqlong L1 L2)>Cases (eqlongdec x y) of
        (or_introl h) => (or_introl  ? ~(eqlong L1 L2) (eql_cons a b x y h))
      | (or_intror h) => (or_intror (eqlong L1 L2) ? (nff a b x y h))   
      end
 end.

