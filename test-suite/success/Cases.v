(****************************************************************************)
(* Pattern-matching when non inductive terms occur                          *)

(* Dependent form of annotation *)
Check <[n:nat]nat>Cases O eq of O x => O | (S x) y => x end.
Check <[_,_:nat]nat>Cases O eq O of O x y => O | (S x) y z => x end.

(* Non dependent form of annotation *)
Check <nat>Cases O eq of O x => O | (S x) y => x end.

(****************************************************************************)
(* All remaining examples come from Cristina Cornes' V6 TESTS/MultCases.v   *)

Inductive IFExpr : Set := 
          Var  : nat -> IFExpr
        | Tr   : IFExpr
        | Fa   : IFExpr
        | IfE   : IFExpr -> IFExpr -> IFExpr -> IFExpr.

Inductive List [A:Set] :Set := 
 Nil:(List A) | Cons:A->(List A)->(List A).

Inductive listn : nat-> Set := 
  niln : (listn O) 
| consn : (n:nat)nat->(listn n) -> (listn (S n)).

Inductive Listn [A:Set] : nat-> Set := 
  Niln : (Listn A O) 
| Consn : (n:nat)nat->(Listn A n) -> (Listn A (S n)).

Inductive Le : nat->nat->Set :=
  LeO: (n:nat)(Le O n) 
| LeS: (n,m:nat)(Le n m) -> (Le (S n) (S m)).

Inductive LE [n:nat] : nat->Set := 
    LE_n : (LE n n) | LE_S : (m:nat)(LE n m)->(LE n (S m)).

Require Bool.



Inductive PropForm : Set := 
          Fvar : nat -> PropForm
        | Or   : PropForm -> PropForm -> PropForm .

Section testIFExpr.
Definition  Assign:= nat->bool.
Parameter Prop_sem : Assign -> PropForm -> bool.

Check [A:Assign][F:PropForm] 
    <bool>Cases F of
           (Fvar n)   => (A n)
         | (Or F G)   => (orb (Prop_sem A F) (Prop_sem A G))
    end.

Check [A:Assign][H:PropForm] 
    <bool>Cases H of
           (Fvar n)   => (A n)
         | (Or F G)   => (orb (Prop_sem A F) (Prop_sem A G))
    end.
End testIFExpr.



Check [x:nat]<nat>Cases x of O => O | x => x end.

Section testlist.
Parameter A:Set.
Inductive list : Set := nil : list | cons : A->list->list.
Parameter inf: A->A->Prop.


Definition list_Lowert2 :=
   [a:A][l:list](<Prop>Cases l of nil => True 
                               | (cons b l) =>(inf a b) end).

Definition titi :=
   [a:A][l:list](<list>Cases l of nil => l
                               | (cons b l) => l end).
Reset list.
End testlist.


(* To test translation *)
(* ------------------- *)


Check  <nat>Cases O of O => O | _ => O end.

Check <nat>Cases O of
               (O as b) => b 
             | (S O)  => O
             | (S (S x)) => x end.

Check Cases O of
               (O as b) => b 
             | (S O)  => O
             | (S (S x)) => x end.


Check [x:nat]<nat>Cases x of
                          (O as b) => b 
                        | (S x)  => x end.

Check              [x:nat]Cases x of
                          (O as b) => b 
                        | (S x)  => x end.

Check <nat>Cases O of 
                          (O as b) => b 
                        | (S x)  => x end.

Check <nat>Cases O of 
                          x  => x 
                       end.

Check  Cases O of 
                          x  => x 
                       end.

Check <nat>Cases O of
                              O => O
                         | ((S x) as b) => b
                        end.

Check [x:nat]<nat>Cases x of
                              O => O
                         | ((S x) as b) => b
                        end.

Check [x:nat] Cases x of
                              O => O
                         | ((S x) as b) => b
                        end.


Check <nat>Cases O of
         O => O
    | (S x) => O
      end.


Check <nat*nat>Cases O of
                              O => (O,O)
                         | (S x) =>  (x,O)
                        end.

Check                    Cases O of
                              O => (O,O)
                         | (S x) =>  (x,O)
                        end.

Check <nat->nat>Cases O of
                              O => [n:nat]O
                         | (S x) =>  [n:nat]O
                        end.

Check                   Cases O of
                              O => [n:nat]O
                         | (S x) =>  [n:nat]O
                        end.


Check <nat->nat>Cases O of
                              O => [n:nat]O
                         | (S x) =>  [n:nat](plus x n)
                        end.

Check                    Cases O of
                              O => [n:nat]O
                         | (S x) =>  [n:nat](plus x n)
                        end.


Check <nat>Cases O of
                              O => O
                         | ((S x) as b) => (plus b x)
                         end.

Check <nat>Cases O of
              O => O
          | ((S (x as a)) as b) => (plus b a)
                         end.
Check  Cases O of
              O => O
          | ((S (x as a)) as b) => (plus b a)
                         end.


Check  Cases O of
                              O => O
                         |  _  => O
                        end.

Check <nat>Cases O of
                  O => O
               |  x => x
                 end.

Check                     Cases O of
                             x => O
                           | O => (S O)
                        end.
Check <nat>Cases O (S O) of
                             x  y => (plus x y)
                        end.

Check      Cases O (S O) of
                             x  y => (plus x y)
                        end.
 
Check <nat>Cases O (S O) of
                             O  y => y
                          | (S x) y => (plus x y) 
                        end.

Check              Cases O (S O) of
                             O  y => y
                          | (S x) y => (plus x y) 
                        end.


Check    <nat>Cases O (S O) of
                      O  x =>  x
             |      (S y) O =>  y
             |        x y  => (plus x y)
           end.




Check        Cases O (S O) of
                      O  x => (plus x O)
             |      (S y) O =>  (plus y O)
             |        x y  => (plus x y)
           end.

Check 
          <nat>Cases O (S O) of
                      O  x => (plus x O)
             |      (S y) O =>  (plus y O)
             |        x y  => (plus x y)
           end.


Check 
          <nat>Cases O (S O) of
                      O  x =>  x 
             | ((S x) as b) (S y) => (plus (plus b x) y)
             |    x y  => (plus x y)
           end.


Check         Cases O (S O) of
                    O  x =>  x 
             | ((S x) as b) (S y) => (plus (plus b x) y)
             |    x y  => (plus x y)
           end.


Check [l:(List nat)]<(List nat)>Cases l of 
                         Nil => (Nil nat)
                      | (Cons  a l) => l
                      end.

Check [l:(List nat)]  Cases l of 
                         Nil => (Nil nat)
                      | (Cons  a l) => l
                      end.

Check <nat>Cases (Nil nat) of 
                         Nil =>O
                      | (Cons  a l) => (S a)
                      end.
Check Cases (Nil nat) of 
                         Nil =>O
                      | (Cons  a l) => (S a)
                      end.

Check <(List nat)>Cases (Nil nat) of 
                        (Cons  a l) => l
                       | x => x
                      end.

Check              Cases (Nil nat) of 
                        (Cons  a l) => l
                       | x => x
                      end.

Check <(List nat)>Cases (Nil nat) of 
                         Nil => (Nil nat)
                      | (Cons  a l) => l
                      end.

Check             Cases (Nil nat) of 
                         Nil => (Nil nat)
                      | (Cons  a l) => l
                      end.


Check 
   <nat>Cases O of 
      O => O
    | (S x) => <nat>Cases (Nil nat) of 
                         Nil => x
                      | (Cons  a l) => (plus x a)
                      end
     end.

Check 
   Cases O of 
      O => O
    | (S x) => Cases (Nil nat) of 
                         Nil => x
                      | (Cons  a l) => (plus x a)
                      end
     end.

Check 
 [y:nat]Cases y of 
      O => O
    | (S x) => Cases (Nil nat) of 
                         Nil => x
                      | (Cons  a l) => (plus x a)
                      end
     end.


Check 
   <nat>Cases O (Nil nat) of 
      O       x => O
    | (S x)  Nil => x
    | (S x) (Cons  a l) => (plus x a)      
     end.



Check [n:nat][l:(listn n)]<[_:nat]nat>Cases l of 
                         niln => O
                      |    x  => O
                      end.

Check [n:nat][l:(listn n)]
                     Cases l of 
                         niln => O
                      |    x  => O
                      end.


Check <[_:nat]nat>Cases niln of 
                         niln => O
                      |    x  => O
                      end.

Check               Cases niln of 
                         niln => O
                      |    x  => O
                      end.


Check <[_:nat]nat>Cases niln of 
                         niln => O
                      |  (consn n a l)  => a
                      end.
Check                Cases niln of 
                         niln => O
                      |  (consn n a l)  => a
                      end.


Check [n:nat][x:nat][l:(listn n)]<[_:nat]nat>Cases x l of 
                         O niln => O
                      |  y  x  => O
                      end.

Check <[_:nat]nat>Cases O niln of 
                         O niln => O
                      |  y  x  => O
                      end.


Check <[_:nat]nat>Cases niln O of 
                         niln O => O
                      |  y  x  => O
                      end.

Check               Cases niln O of 
                         niln O => O
                      |  y  x  => O
                      end.

Check <[_:nat][_:nat]nat>Cases niln niln of 
                         niln niln => O
                      |    x  y  => O
                      end.

Check               Cases niln niln of 
                         niln niln => O
                      |    x  y  => O
                      end.

Check <[_,_,_:nat]nat>Cases niln niln niln of 
                         niln niln niln => O
                      |    x  y z  => O
                      end.


Check                 Cases niln niln niln of 
                         niln niln niln => O
                      |    x  y z  => O
                      end.



Check <[_:nat]nat>Cases (niln) of 
                         niln  => O
                      | (consn n a l) => O
                      end.

Check         Cases (niln) of 
                         niln  => O
                      | (consn n a l) => O
                      end.


Check <[_:nat][_:nat]nat>Cases niln niln of 
                         niln niln => O
                      |  niln (consn n a l) => n
                      |  (consn n a l)  x  => a
                      end.


Check                Cases niln niln of 
                         niln niln => O
                      |  niln (consn n a l) => n
                      |  (consn n a l)  x  => a
                      end.


Check [n:nat][l:(listn n)]<[_:nat]nat>Cases l of 
                         niln => O
                      |    x  => O
                      end.

Check [c:nat;s:bool]
  <[_:nat;_:bool]nat>Cases c s of
        | O _ => O
        | _ _ => c
        end.

Check [c:nat;s:bool]
  <[_:nat;_:bool]nat>Cases c s of
        | O _ => O
        | (S _) _ => c
        end.
         

(* Rows of pattern variables: some tricky cases *)
Axiom P:nat->Prop; f:(n:nat)(P n).

Check [i:nat]
  <[_:bool;n:nat](P n)>Cases true i of
        | true k => (f k)
        | _    k => (f k)
        end.

Check [i:nat]
  <[n:nat;_:bool](P n)>Cases i true of
        | k true => (f k)
        | k _ => (f k)
        end.

(* Nested Cases: the SYNTH of the Cases on n used to make Multcase believe
 * it has to synthtize the predicate on O (which he can't)
 *)
Check <[n]Cases n of O => bool | (S _) => nat end>Cases O of
    O => true
  | (S _) => O
  end.

Check [n:nat][l:(listn n)]Cases l of 
                         niln => O
                      |    x  => O
                      end.

Check [n:nat][l:(listn n)]<[_:nat]nat>Cases l of 
                         niln  => O
                      | (consn n a niln) => O
                      | (consn n a (consn m b l)) => (plus n m)
                      end.


Check [n:nat][l:(listn n)]Cases l of 
                         niln  => O
                      | (consn n a niln) => O
                      | (consn n a (consn m b l)) => (plus n m)
                      end.



Check [n:nat][l:(listn n)]<[_:nat]nat>Cases l of 
                         niln  => O
                      | (consn n a niln) => O
                      | (consn n a (consn m b l)) => (plus n m)
                      end.

Check [n:nat][l:(listn n)]Cases l of 
                         niln  => O
                      | (consn n a niln) => O
                      | (consn n a (consn m b l)) => (plus n m)
                      end.


Check [A:Set][n:nat][l:(Listn A n)]<[_:nat]nat>Cases l of 
                         Niln   => O
                      | (Consn n a Niln) => O
                      | (Consn n a (Consn m b l)) => (plus n m)
                      end.

Check [A:Set][n:nat][l:(Listn A n)]Cases l of 
                         Niln   => O
                      | (Consn n a Niln) => O
                      | (Consn n a (Consn m b l)) => (plus n m)
                      end.

(*
Check [A:Set][n:nat][l:(Listn A n)]
                   <[_:nat](Listn A O)>Cases l of 
                         (Niln  as b) => b
                      | (Consn  n a (Niln  as b))=> (Niln A)
                      | (Consn  n a (Consn m b l)) => (Niln A)
                      end.

Check [A:Set][n:nat][l:(Listn A n)]
                    Cases l of 
                         (Niln  as b) => b
                      | (Consn  n a (Niln  as b))=> (Niln A)
                      | (Consn  n a (Consn m b l)) => (Niln A)
                      end.
*)
(******** This example rises an error unconstrained_variables!
Check [A:Set][n:nat][l:(Listn A n)]
                    Cases l of 
                         (Niln  as b) => (Consn A O O b)
                      | ((Consn  n a Niln) as L) =>  L 
                      | (Consn  n a _)  =>  (Consn A O O (Niln A))
                      end.
**********)

(* To test tratement of as-patterns in depth *)
Check [A:Set] [l:(List A)]
                    Cases l of 
                         (Nil  as b) => (Nil A)
                      | ((Cons a Nil)  as L) => L
                      | ((Cons a (Cons b m)) as L) => L
                      end.


Check [n:nat][l:(listn n)]
             <[_:nat](listn n)>Cases l of 
                         niln  => l 
                      | (consn n a c) => l
                      end.
Check [n:nat][l:(listn n)]
                      Cases l of 
                         niln  => l 
                      | (consn n a c) => l
                      end.


Check [n:nat][l:(listn n)]
             <[_:nat](listn n)>Cases l of 
                         (niln as b) => l 
                      |  _  => l
                      end.


Check [n:nat][l:(listn n)]
                     Cases l of 
                         (niln as b) => l 
                      |  _  => l
                      end.

Check [n:nat][l:(listn n)]
             <[_:nat](listn n)>Cases l of 
                         (niln as b) => l
                      |  x  => l
                      end.


Check [A:Set][n:nat][l:(Listn A n)]
                       Cases l of 
                         (Niln  as b) => l 
                      |   _ => l
                      end.

Check [A:Set][n:nat][l:(Listn A n)]
             <[_:nat](Listn A n)>Cases l of 
                         Niln  => l 
                      | (Consn  n a Niln) => l
                      | (Consn  n a (Consn  m b c)) => l 
                      end.

Check [A:Set][n:nat][l:(Listn A n)]
                      Cases l of 
                         Niln  => l 
                      | (Consn  n a Niln) => l
                      | (Consn  n a (Consn  m b c)) => l 
                      end.

Check [A:Set][n:nat][l:(Listn A n)]
             <[_:nat](Listn A n)>Cases l of 
                         (Niln as b) => l 
                      | (Consn  n a (Niln as b)) => l
                      | (Consn  n a (Consn  m b _)) => l 
                      end.

Check [A:Set][n:nat][l:(Listn A n)]
                     Cases l of 
                         (Niln as b) => l 
                      | (Consn  n a (Niln as b)) => l
                      | (Consn  n a (Consn  m b _)) => l 
                      end.


Check <[_:nat]nat>Cases (niln) of 
                         niln  => O
                      | (consn n a niln) => O
                      | (consn n a (consn m b l)) => (plus n m)
                      end.


Check               Cases (niln) of 
                         niln  => O
                      | (consn n a niln) => O
                      | (consn n a (consn m b l)) => (plus n m)
                      end.

Check <[_,_:nat]nat>Cases (LeO O) of 
                         (LeO x)  => x
                      | (LeS n m h) => (plus n m) 
                      end.


Check               Cases (LeO O) of 
                         (LeO x)  => x
                      | (LeS n m h) => (plus n m) 
                      end.

Check [n:nat][l:(Listn nat n)]
                     <[_:nat]nat>Cases l of 
                         Niln  => O
                      | (Consn n a l) => O
                      end.


Check [n:nat][l:(Listn nat n)]
                      Cases l of 
                         Niln  => O
                      | (Consn n a l) => O
                      end.


Check                Cases (Niln nat) of 
                         Niln  => O
                      | (Consn n a l) => O
                      end.

Check <[_:nat]nat>Cases (LE_n O) of 
                         LE_n   => O 
                      | (LE_S m h) => O
                      end.


Check               Cases (LE_n O) of 
                         LE_n   => O 
                      | (LE_S m h) => O
                      end.



Check               Cases (LE_n O) of 
                         LE_n   => O 
                      | (LE_S m h) => O
                      end.



Check <[_:nat]nat>Cases (niln ) of 
                         niln   => O
                      | (consn  n a niln) => n
                      | (consn  n a (consn  m b l)) => (plus n m)
                      end.

Check               Cases (niln ) of 
                         niln   => O
                      | (consn  n a niln) => n
                      | (consn  n a (consn  m b l)) => (plus n m)
                      end.


Check <[_:nat]nat>Cases (Niln nat) of 
                         Niln  => O
                      | (Consn  n a Niln) => n
                      | (Consn   n a (Consn  m b l)) => (plus n m)
                      end.

Check                Cases (Niln nat) of 
                         Niln  => O
                      | (Consn  n a Niln) => n
                      | (Consn   n a (Consn  m b l)) => (plus n m)
                      end.


Check <[_,_:nat]nat>Cases (LeO O) of 
                         (LeO x)  => x
                      | (LeS n m (LeO x)) => (plus x m)
                      | (LeS n m (LeS x y h)) => (plus n x)
                      end.


Check                 Cases (LeO O) of 
                         (LeO x)  => x
                      | (LeS n m (LeO x)) => (plus x m)
                      | (LeS n m (LeS x y h)) => (plus n x)
                      end.


Check <[_,_:nat]nat>Cases (LeO O) of 
                         (LeO x)  => x
                      | (LeS n m (LeO x)) => (plus x m)
                      | (LeS n m (LeS x y h)) => m
                      end.

Check                Cases (LeO O) of 
                         (LeO x)  => x
                      | (LeS n m (LeO x)) => (plus x m)
                      | (LeS n m (LeS x y h)) => m
                      end.


Check [n,m:nat][h:(Le n m)]
                    <[_,_:nat]nat>Cases h of 
                         (LeO x)  => x
                      | x => O
                      end.

Check [n,m:nat][h:(Le n m)]
                     Cases h of 
                         (LeO x)  => x
                      | x => O
                      end.


Check [n,m:nat][h:(Le n m)]
                    <[_,_:nat]nat>Cases h of 
                        (LeS n m h)  => n
                      | x => O
                      end.


Check [n,m:nat][h:(Le n m)]
                      Cases h of 
                        (LeS n m h)  => n
                      | x => O
                      end.


Check    [n,m:nat][h:(Le n m)]
  <[_,_:nat]nat*nat>Cases h of
                    (LeO n) => (O,n)
                   |(LeS n m _) => ((S n),(S m))
                   end.


Check    [n,m:nat][h:(Le n m)]
                  Cases h of
                    (LeO n) => (O,n)
                   |(LeS n m _) => ((S n),(S m))
                   end.


Fixpoint F [n,m:nat; h:(Le n m)] : (Le n (S m)) :=
 <[n,m:nat](Le n (S m))>Cases h  of 
                (LeO m') => (LeO (S m'))
              | (LeS n' m' h') => (LeS n' (S m') (F n' m' h'))
        end.

Reset F.

Fixpoint F [n,m:nat; h:(Le n m)] :(Le n (S m)) :=
  <[n,m:nat](Le n (S m))>Cases h of
                           (LeS n m h) => (LeS n (S m) (F n m h))
                         | (LeO m) => (LeO (S m)) 
                        end.

(* Rend la longueur de la liste *)
Definition length1:= [n:nat] [l:(listn n)]
        <[_:nat]nat>Cases l of 
                     (consn n _ (consn m _ _)) => (S (S m))
                    |(consn n _ _) => (S O)
                    | _ => O
             end.

Reset length1.
Definition length1:= [n:nat] [l:(listn n)]
                    Cases l of 
                     (consn n _ (consn m _ _)) => (S (S m))
                    |(consn n _ _) => (S O)
                    | _ => O
                    end.


Definition length2:= [n:nat] [l:(listn n)]
        <[_:nat]nat>Cases l of 
                     (consn n _ (consn m _ _)) => (S (S m))
                    |(consn n _ _) => (S n)
                    | _ => O
             end.

Reset length2.

Definition length2:= [n:nat] [l:(listn n)]
                   Cases l of 
                     (consn n _ (consn m _ _)) => (S (S m))
                    |(consn n _ _) => (S n)
                    | _ => O
                   end.

Definition length3 :=
[n:nat][l:(listn n)]
        <[_:nat]nat>Cases l of 
                     (consn n _ (consn m _ l)) => (S n)
                    |(consn n _ _) => (S O)
                    | _  => O
                   end.


Reset length3.

Definition length3 :=
[n:nat][l:(listn n)]
                   Cases l of 
                     (consn n _ (consn m _ l)) => (S n)
                    |(consn n _ _) => (S O)
                    | _  => O
                   end.

 
Check <[_,_:nat]nat>Cases (LeO O) of 
                        (LeS n m h)  =>(plus n m)
                      | x => O
                      end.
Check              Cases (LeO O) of 
                        (LeS n m h)  =>(plus n m)
                      | x => O
                      end.

Check [n,m:nat][h:(Le n m)]<[_,_:nat]nat>Cases h of 
                         (LeO x)  => x
                      | (LeS n m (LeO x)) => (plus x m)
                      | (LeS n m (LeS x y h)) =>(plus n (plus m (plus x y)))
                      end.


Check [n,m:nat][h:(Le n m)]Cases h of 
                         (LeO x)  => x
                      | (LeS n m (LeO x)) => (plus x m)
                      | (LeS n m (LeS x y h)) =>(plus n (plus m (plus x y)))
                      end.

Check <[_,_:nat]nat>Cases (LeO O) of 
                         (LeO x)  => x
                      | (LeS n m (LeO x)) => (plus x m)
                      | (LeS n m (LeS x y h)) =>(plus n (plus m (plus x y)))
                      end.

Check                 Cases (LeO O) of 
                         (LeO x)  => x
                      | (LeS n m (LeO x)) => (plus x m)
                      | (LeS n m (LeS x y h)) =>(plus n (plus m (plus x y)))
                      end.


Check <[_:nat]nat>Cases (LE_n O) of 
                         LE_n   => O
                      | (LE_S m LE_n) => (plus O m)
                      | (LE_S m (LE_S y h)) => (plus O m)
                      end.


Check                Cases (LE_n O) of 
                         LE_n   => O
                      | (LE_S m LE_n) => (plus O m)
                      | (LE_S m (LE_S y h)) => (plus O m)
                      end.

Check [n,m:nat][h:(Le n m)]<[_,_:nat]nat>Cases h of 
                                                x => x 
                                          end.

 Check [n,m:nat][h:(Le n m)]              Cases h of 
                                                x => x 
                                          end.

Check [n,m:nat][h:(Le n m)]<[_,_:nat]nat>Cases h of 
                                               (LeO n) => n
                                              |   x => O
                                          end.
Check [n,m:nat][h:(Le n m)] Cases h of 
                               (LeO n) => n
                             |   x => O
                            end.


Check [n:nat]<[_:nat]nat->nat>Cases niln of 
                         niln  => [_:nat]O
                      | (consn n a niln) => [_:nat]O
                      | (consn n a (consn m b l)) => [_:nat](plus n m)
                      end.


Check [n:nat]         Cases niln of 
                         niln  => [_:nat]O
                      | (consn n a niln) => [_:nat]O
                      | (consn n a (consn m b l)) => [_:nat](plus n m)
                      end.

Check [A:Set][n:nat][l:(Listn A n)]
                  <[_:nat]nat->nat>Cases l of 
                         Niln  => [_:nat]O
                      | (Consn  n a Niln) =>  [_:nat] n
                      | (Consn  n a (Consn  m b l)) => [_:nat](plus n m)
                      end.

Check [A:Set][n:nat][l:(Listn A n)]
                        Cases l of 
                         Niln  => [_:nat]O
                      | (Consn  n a Niln) =>  [_:nat] n
                      | (Consn  n a (Consn  m b l)) => [_:nat](plus n m)
                      end.

(* Alsos tests for multiple _ patterns *)
Check [A:Set][n:nat][l:(Listn A n)]
                  <[n:nat](Listn A n)>Cases l of 
                        (Niln as b) => b
                      | ((Consn _ _ _ ) as b)=>  b
                      end.

(** Horrible error message! 

Check [A:Set][n:nat][l:(Listn A n)]
                        Cases l of 
                        (Niln as b) => b
                      | ((Consn _ _ _ ) as b)=>  b
                      end.
******)

Check   <[n:nat](listn  n)>Cases niln of 
               (niln as b) => b
          | ((consn _ _ _ ) as b)=>  b
          end.


Check   <[n:nat](listn  n)>Cases niln of 
               (niln as b) => b
          |    x  =>  x
          end.

Check [n,m:nat][h:(LE n m)]<[_:nat]nat->nat>Cases h  of 
                         LE_n   => [_:nat]n
                      | (LE_S  m LE_n) => [_:nat](plus n m)
                      | (LE_S  m (LE_S y h)) => [_:nat](plus m y )
                      end.
Check [n,m:nat][h:(LE n m)]Cases h  of 
                         LE_n   => [_:nat]n
                      | (LE_S  m LE_n) => [_:nat](plus n m)
                      | (LE_S  m (LE_S y h)) => [_:nat](plus m y )
                      end.


Check [n,m:nat][h:(LE n m)]
    <[_:nat]nat>Cases h  of 
        LE_n   => n
      | (LE_S m  LE_n ) => (plus n m)
      | (LE_S  m (LE_S  y  LE_n )) => (plus (plus n m) y)
      | (LE_S  m (LE_S  y (LE_S  y' h))) => (plus (plus n m) (plus y y'))
                      end.



Check [n,m:nat][h:(LE n m)]
       Cases h  of 
        LE_n   => n
      | (LE_S m  LE_n ) => (plus n m)
      | (LE_S  m (LE_S  y  LE_n )) => (plus (plus n m) y)
      | (LE_S  m (LE_S  y (LE_S  y' h))) => (plus (plus n m) (plus y y'))
                      end.


Check [n,m:nat][h:(LE n m)]<[_:nat]nat>Cases h  of 
                        LE_n   => n
                      | (LE_S m LE_n) => (plus n m)
                      | (LE_S  m (LE_S y h)) => (plus (plus n m) y)
                      end.


Check [n,m:nat][h:(LE n m)]Cases h  of 
                        LE_n   => n
                      | (LE_S m LE_n) => (plus n m)
                      | (LE_S  m (LE_S y h)) => (plus (plus n m) y)
                      end.

Check [n,m:nat]
                    <[_,_:nat]nat>Cases (LeO O) of 
                        (LeS n m h)  =>(plus n m)
                      | x => O
                      end.

Check [n,m:nat]
                      Cases (LeO O) of 
                        (LeS n m h)  =>(plus n m)
                      | x => O
                      end.

Parameter test : (n:nat){(le O n)}+{False}.
Check  [n:nat]<nat>Cases (test n) of
                        (left _) => O 
                        | _ => O end.


Check  [n:nat]   <nat> Cases (test n) of
                          (left _) => O 
                        | _ => O end.

Check  [n:nat]Cases (test n) of
                          (left _) => O 
                        | _ => O end.

Parameter compare : (n,m:nat)({(lt n m)}+{n=m})+{(gt n m)}.
Check <nat>Cases (compare O O) of
               (* k<i *)  (inleft (left _)) => O
            |  (* k=i *)  (inleft  _)  => O
            |  (* k>i *)  (inright  _) => O end.

Check    Cases (compare O O) of
               (* k<i *)  (inleft (left _)) => O
            |  (* k=i *)  (inleft  _)  => O
            |  (* k>i *)  (inright  _) => O end.



CoInductive SStream [A:Set]  : (nat->A->Prop)->Set :=
scons  : 
  (P:nat->A->Prop)(a:A)(P O a)->(SStream A [n:nat](P (S n)))->(SStream A P).
Parameter B : Set.

Check 
  [P:nat->B->Prop][x:(SStream B P)]<[_:nat->B->Prop]B>Cases x of
     (scons _ a _ _) => a  end.


Check 
  [P:nat->B->Prop][x:(SStream B P)] Cases x of
     (scons _ a _ _) => a  end.

Check <nat*nat>Cases (O,O) of  (x,y) => ((S x),(S y)) end.
Check <nat*nat>Cases (O,O) of  ((x as b), y) => ((S x),(S y)) end.
Check <nat*nat>Cases (O,O) of  (pair x y) => ((S x),(S y)) end.

Check Cases (O,O) of  (x,y) => ((S x),(S y)) end.
Check Cases (O,O) of  ((x as b), y) => ((S x),(S y)) end.
Check Cases (O,O) of  (pair x y) => ((S x),(S y)) end.



Parameter concat : (A:Set)(List A) ->(List A) ->(List A).

Check <(List nat)>Cases (Nil nat) (Nil nat) of 
                 (Nil as b)  x  => (concat nat b x)
              | ((Cons _ _) as d) (Nil as c) => (concat nat d c)
              |  _ _ => (Nil nat)
              end.
Check Cases (Nil nat) (Nil nat) of 
           (Nil as b)  x  => (concat nat b x)
       | ((Cons _ _) as d) (Nil as c) => (concat nat d c)
       |  _ _ => (Nil nat)
       end.

Definition NIL := (Nil nat).
Definition CONS  := (Cons nat).
Check <(List nat)>Cases (Nil nat) of 
                NIL   => NIL
              |  _   => NIL
              end.

Check     Cases (Nil nat) of 
                NIL   => NIL
              |  _   => NIL
              end.


Inductive redexes : Set :=
    VAR : nat -> redexes
  | Fun : redexes -> redexes
  | Ap  : bool -> redexes -> redexes -> redexes.

Fixpoint regular [U:redexes] : Prop := <Prop>Cases U of
  (VAR n) => True
| (Fun V) => (regular V)
| (Ap true ((Fun _) as V)  W) => (regular V) /\ (regular W)
| (Ap true _ W) => False
| (Ap false V W) => (regular V) /\ (regular W) 
end.


Check [n:nat]Cases n of O => O | (S ((S n) as V)) => V | _ => O end.

Reset concat.
Parameter concat :(n:nat) (listn n) -> (m:nat) (listn m)-> (listn (plus n m)).
Check [n:nat][l:(listn n)][m:nat][l':(listn m)] 
 <[n,_:nat](listn (plus n m))>Cases l l' of 
                 niln  x => x
              | (consn n a l'') x =>(consn (plus n m) a (concat n l'' m x))
               end.

Check [x,y,z:nat]
        [H:x=y]
         [H0:y=z]<[_:nat]x=z>Cases H of refl_equal => 
                          <[n:nat]x=n>Cases H0 of refl_equal => H
                                             end
                                       end.

Check [h:False]<False>Cases h of end.

Check [h:False]<True>Cases h of end.

Definition is_zero := [n:nat]Cases n of O => True | _ => False end.

Check [n:nat][h:O=(S n)]<[n:nat](is_zero n)>Cases h of refl_equal => I end.

Definition disc : (n:nat)O=(S n)->False :=
  [n:nat][h:O=(S n)]
      <[n:nat](is_zero n)>Cases h of refl_equal => I end.

Definition nlength3 := [n:nat] [l: (listn n)]
                         Cases l of 
                            niln  => O
                         |  (consn O  _ _)  => (S O)
                         |  (consn (S n)  _ _) => (S (S n))
                         end.

(* == Testing strategy elimintation predicate  synthesis == *)
Section titi.
Variable h:False.
Check Cases O of 
          O  => O
       |  _  => (Except h)
       end.
End titi.

Check Cases niln of 
    (consn _ a niln) => a
 |  (consn n _ x)    => O
 |   niln  => O
 end.



Inductive wsort : Set := ws : wsort | wt : wsort.
Inductive TS : wsort->Set := 
   id :(TS ws) 
| lift:(TS ws)->(TS ws).

Check [b:wsort][M:(TS b)][N:(TS b)]
 Cases   M   N of   
  (lift M1)   id => False 
 | _ _ => True 
 end.



(* Testing eta-expansion of elimination predicate *)

Section NATIND2.
Variable P : nat -> Type.
Variable H0 : (P O).
Variable H1 : (P (S O)).
Variable H2 : (n:nat)(P n)->(P (S (S n))).
Fixpoint nat_ind2 [n:nat] : (P n) :=
         <P>Cases n of  
                        O     => H0
                  | (S O)     => H1
                  | (S (S n)) => (H2 n (nat_ind2 n))
        end.
End NATIND2.

(* ===================================================================== *)
(* To test pattern matching over a non-dependent inductive type, but     *)
(* having constructors with some arguments that depend on others         *)
(* I.e. to test manipulation of elimination predicate                    *)
(* ===================================================================== *)


Parameter LTERM : nat -> Set.
Mutual Inductive TERM : Type :=
	  var : TERM
	| oper : (op:nat) (LTERM op) -> TERM.

Parameter t1, t2:TERM.

Check Cases t1 t2 of 
   var   var  => True

 | (oper op1 l1)  (oper op2 l2) => False
 | _ _ => False 
 end. 
Reset LTERM.



Require Peano_dec.
Parameter n:nat.
Definition eq_prf := (EXT m | n=m).
Parameter p:eq_prf .

Check Cases p of
     (exT_intro c eqc) =>
          Cases (eq_nat_dec c n) of
            (right _) => (refl_equal ? n)
           |(left y) (* c=n*) => (refl_equal ? n) 
          end
     end.


Parameter ordre_total : nat->nat->Prop.

Parameter N_cla:(N:nat){N=O}+{N=(S O)}+{(ge N (S (S O)))}.

Parameter exist_U2:(N:nat)(ge N (S (S O)))->
                      {n:nat|(m:nat)(lt O m)/\(le m N)
                             /\(ordre_total n m)                   
                             /\(lt O n)/\(lt n N)}.

Check [N:nat](Cases (N_cla N) of
                         (inright H)=>(Cases (exist_U2 N H) of
                                               (exist a b)=>a
                                       end)
                        |   _       => O
                       end).



(* ============================================== *)
(*     To test compilation of dependent case      *)
(*  Nested patterns                               *)
(* ============================================== *)


Check <[n:nat]n=n>Cases O of 
                    O => (refl_equal nat O) 
                  | m => (refl_equal nat m) 
end.


(* == To test that terms named with AS are correctly absolutized before
      substitution in rhs   == *)

Check [n:nat]<[n:nat]nat>Cases (n) of 
          O  => O
       |  (S O)  => O
       |  ((S (S n1)) as N)  => N
      end.

(* ========= *)

Check <[n:nat][_:(listn n)]Prop>Cases niln of 
                         niln => True
                       | (consn (S O) _ _) => False
                       | _ => True end.

Check <[n:nat][_:(listn n)]Prop>Cases niln of 
                         niln => True
                       | (consn (S (S O)) _ _) => False
                       | _ => True end.


Check <[n,m:nat][h:(Le n m)]nat>Cases (LeO O) of 
                         (LeO _) => O
                       | (LeS (S x) _ _) => x
                       | _ => (S O) end.

Check <[n,m:nat][h:(Le n m)]nat>Cases (LeO O) of 
                         (LeO _) => O
                       | (LeS (S x)  (S y) _) => x
                       | _ => (S O) end.

Check <[n,m:nat][h:(Le n m)]nat>Cases (LeO O) of 
                         (LeO _) => O
                       | (LeS ((S x) as b)  (S y) _) => b
                       | _ => (S O) end.


Parameter iguales : (n,m:nat)(h:(Le n m))Prop .

Check <[n,m:nat][h:(Le n m)]Prop>Cases (LeO O) of 
                         (LeO O) => True
                       | (LeS (S x) (S y) H) => (iguales (S x) (S y) H)
                       | _ => False end.

Check <[n,m:nat][h:(Le n m)]Prop>Cases (LeO O) of 
                         (LeO O) => True
                       | (LeS (S x) O H) => (iguales (S x) O H)
                       | _ => False end.



Parameter ff: (n,m:nat)~n=m -> ~(S n)=(S m).
Parameter discr_r : (n:nat) ~(O=(S n)).
Parameter discr_l : (n:nat) ~((S n)=O).

Check 
[n:nat] 
  <[n:nat]n=O\/~n=O>Cases n of 
      O     => (or_introl ? ~O=O (refl_equal ? O))      
   |  (S x) => (or_intror (S x)=O ? (discr_l x))
  end.


Check 
[n:nat] 
  <[n:nat]n=O\/~n=O>Cases n of 
      O     => (or_introl ? ~O=O (refl_equal ? O))      
   |  (S O) => (or_intror (S O)=O ? (discr_l O))
   |  (S (S x)) => (or_intror (S (S x))=O ? (discr_l (S x)))
 
  end.


Fixpoint eqdec [n:nat] : (m:nat) n=m \/ ~n=m := 
[m:nat]
 <[n,m:nat] n=m \/ ~n=m>Cases n m of
      O   O   => (or_introl ? ~O=O (refl_equal ? O))

   |  O (S x) => (or_intror O=(S x) ? (discr_r x))

   | (S x) O  => (or_intror ? ~(S x)=O (discr_l x))

   | (S x) (S y) =>  
      <(S x)=(S y)\/~(S x)=(S y)>Cases (eqdec x y) of
        (or_introl h) => (or_introl  ? ~(S x)=(S y) (f_equal nat nat S x y h))
      | (or_intror h) => (or_intror (S x)=(S y) ? (ff x y h))   
      end
 end.

Reset eqdec.

Fixpoint eqdec [n:nat] : (m:nat) n=m \/ ~n=m := 
<[n:nat] (m:nat)n=m \/ ~n=m>Cases n  of
    O  => [m:nat] <[m:nat]O=m\/~O=m>Cases m of 
                     O    => (or_introl ? ~O=O (refl_equal nat O))
                   |(S x) => (or_intror O=(S x) ?  (discr_r x))
                  end
  | (S x) => [m:nat] 
    <[m:nat](S x)=m\/~(S x)=m>Cases m of  
        O    => (or_intror (S x)=O ? (discr_l x))
     | (S y) =>  
         <(S x)=(S y)\/~(S x)=(S y)>Cases (eqdec x y) of
            (or_introl h) => (or_introl ? ~(S x)=(S y) (f_equal ? ? S x y h))
          | (or_intror h) => (or_intror (S x)=(S y) ? (ff x y h))   
         end
    end
 end.


Inductive empty : (n:nat)(listn n)-> Prop := 
  intro_empty: (empty O niln).

Parameter inv_empty : (n,a:nat)(l:(listn n)) ~(empty (S n) (consn n a l)).

Check 
[n:nat] [l:(listn n)]
  <[n:nat] [l:(listn n)](empty n l) \/ ~(empty n l)>Cases l of 
        niln               =>  (or_introl ? ~(empty O niln) intro_empty)
   |  ((consn n a y) as b) =>  (or_intror (empty (S n) b) ? (inv_empty n a y))
  end.

Check 
[n:nat] [l:(listn n)]
  <[n:nat] [l:(listn n)](empty n l) \/ ~(empty n l)>Cases l of 
        niln               =>  (or_introl ? ~(empty O niln) intro_empty)
   |  ((consn n O y) as b) =>  (or_intror (empty (S n) b) ? (inv_empty n O y))
   |  ((consn n a y) as b) =>  (or_intror (empty (S n) b) ? (inv_empty n a y))

  end.

Check 
[n:nat] [l:(listn n)]
  <[n:nat] [l:(listn n)](empty n l) \/ ~(empty n l)>Cases l of 
        niln               =>  (or_introl ? ~(empty O niln) intro_empty)
   |  (consn n O y)  =>  (or_intror (empty (S n) (consn n O y)) ? 
                                              (inv_empty n O y))
   |  (consn n a y) =>  (or_intror (empty (S n) (consn n a y)) ? 
                                          (inv_empty n a y))

  end.

Check 
[n:nat] [l:(listn n)]
  <[n:nat] [l:(listn n)](empty n l) \/ ~(empty n l)>Cases l of 
        niln               =>  (or_introl ? ~(empty O niln) intro_empty)
   |  ((consn O a y) as b) =>  (or_intror (empty (S O) b) ? (inv_empty O a y))
   |  ((consn n a y) as b) =>  (or_intror (empty (S n) b) ? (inv_empty n a y))

  end.

Reset ff.
Parameter ff: (n,m:nat)~n=m -> ~(S n)=(S m).
Parameter discr_r : (n:nat) ~(O=(S n)).
Parameter discr_l : (n:nat) ~((S n)=O).

Check 
[n:nat] 
  <[n:nat]n=O\/~n=O>Cases n of 
      O     => (or_introl ? ~O=O (refl_equal ? O))      
   |  (S x) => (or_intror (S x)=O ? (discr_l x))
  end.


Check 
[n:nat] 
  <[n:nat]n=O\/~n=O>Cases n of 
      O     => (or_introl ? ~O=O (refl_equal ? O))      
   |  (S O) => (or_intror (S O)=O ? (discr_l O))
   |  (S (S x)) => (or_intror (S (S x))=O ? (discr_l (S x)))
 
  end.

Fixpoint eqdec [n:nat] : (m:nat) n=m \/ ~n=m := 
[m:nat]
 <[n,m:nat] n=m \/ ~n=m>Cases n m of
      O   O   => (or_introl ? ~O=O (refl_equal ? O))

   |  O (S x) => (or_intror O=(S x) ? (discr_r x))

   | (S x) O  => (or_intror ? ~(S x)=O (discr_l x))

   | (S x) (S y) =>  
      <(S x)=(S y)\/~(S x)=(S y)>Cases (eqdec x y) of
        (or_introl h) => (or_introl  ? ~(S x)=(S y) (f_equal nat nat S x y h))
      | (or_intror h) => (or_intror (S x)=(S y) ? (ff x y h))   
      end
 end.
Reset eqdec.

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

Reset eqdec.
Fixpoint eqdec [n:nat] : (m:nat) n=m \/ ~n=m := 
<[n:nat] (m:nat)n=m \/ ~n=m>Cases n  of
    O  => [m:nat] <[m:nat]O=m\/~O=m>Cases m of 
                     O    => (or_introl ? ~O=O (refl_equal nat O))
                   |(S x) => (or_intror O=(S x) ?  (discr_r x))
                  end
  | (S x) => [m:nat] 
    <[m:nat](S x)=m\/~(S x)=m>Cases m of  
        O    => (or_intror (S x)=O ? (discr_l x))
     | (S y) =>  
         <(S x)=(S y)\/~(S x)=(S y)>Cases (eqdec x y) of
            (or_introl h) => (or_introl ? ~(S x)=(S y) (f_equal ? ? S x y h))
          | (or_intror h) => (or_intror (S x)=(S y) ? (ff x y h))   
         end
    end
 end.


(* ================================================== *)
(* Pour tester parametres                             *)
(* ================================================== *)


Inductive Empty [A:Set] : (List A)-> Prop := 
  intro_Empty: (Empty A (Nil A)).

Parameter inv_Empty : (A:Set)(a:A)(x:(List A)) ~(Empty A (Cons A a x)).


Check
  <[l:(List nat)](Empty nat l) \/ ~(Empty nat l)>Cases (Nil nat) of 
        Nil   =>  (or_introl ? ~(Empty nat (Nil nat)) (intro_Empty nat))
   |   (Cons a y)  =>  (or_intror (Empty nat (Cons nat a y)) ? 
                                   (inv_Empty nat a y))
  end.


Check
[A:Set] 
[l:(List A)]
  <[l:(List A)](Empty A l) \/ ~(Empty A l)>Cases l of 
        Nil  =>  (or_introl ? ~(Empty A (Nil A)) (intro_Empty A))
   |  ((Cons a y) as b) =>  (or_intror (Empty A b) ? (inv_Empty A a y))
  end.



(* ================================================== *)
(* Sur les listes                                     *)
(* ================================================== *)


Inductive empty : (n:nat)(listn n)-> Prop := 
  intro_empty: (empty O niln).

Parameter inv_empty : (n,a:nat)(l:(listn n)) ~(empty (S n) (consn n a l)).

Check 
[n:nat] [l:(listn n)]
  <[n:nat] [l:(listn n)](empty n l) \/ ~(empty n l)>Cases l of 
        niln               =>  (or_introl ? ~(empty O niln) intro_empty)
   |  ((consn n a y) as b) =>  (or_intror (empty (S n) b) ? (inv_empty n a y))
  end.

Check 
[n:nat] [l:(listn n)]
  <[n:nat] [l:(listn n)](empty n l) \/ ~(empty n l)>Cases l of 
        niln               =>  (or_introl ? ~(empty O niln) intro_empty)
   |  ((consn n O y) as b) =>  (or_intror (empty (S n) b) ? (inv_empty n O y))
   |  ((consn n a y) as b) =>  (or_intror (empty (S n) b) ? (inv_empty n a y))

  end.

Check 
[n:nat] [l:(listn n)]
  <[n:nat] [l:(listn n)](empty n l) \/ ~(empty n l)>Cases l of 
        niln               =>  (or_introl ? ~(empty O niln) intro_empty)
   |  (consn n O y)  =>  (or_intror (empty (S n) (consn n O y)) ? 
                                              (inv_empty n O y))
   |  (consn n a y) =>  (or_intror (empty (S n) (consn n a y)) ? 
                                          (inv_empty n a y))

  end.

Check 
[n:nat] [l:(listn n)]
  <[n:nat] [l:(listn n)](empty n l) \/ ~(empty n l)>Cases l of 
        niln               =>  (or_introl ? ~(empty O niln) intro_empty)
   |  ((consn O a y) as b) =>  (or_intror (empty (S O) b) ? (inv_empty O a y))
   |  ((consn n a y) as b) =>  (or_intror (empty (S n) b) ? (inv_empty n a y))

  end.
(* ===================================== *)
(*   Test parametros:                    *)
(* ===================================== *)

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

Check
 <[x,y:(List nat)](eqlong x y)\/~(eqlong x y)>Cases (Nil nat) (Nil nat) of
      Nil Nil   => V1
   |  Nil (Cons a x)  => (V2 a x)
   |  (Cons a x)  Nil => (V3 a x)
   | (Cons a x)  (Cons b y)  => (V4 a x b y)
 end.


Check
[x,y:(List nat)]
 <[x,y:(List nat)](eqlong x y)\/~(eqlong x y)>Cases x y of
      Nil Nil   => V1
   |  Nil (Cons a x)  => (V2 a x)
   |  (Cons a x)  Nil => (V3 a x)
   | (Cons a x)  (Cons b y)  => (V4 a x b y)
 end.



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

Check
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

 
(* ===================================== *)

Inductive Eqlong : (n:nat) (listn n)-> (m:nat) (listn m)-> Prop :=
 Eql_cons : (n,m:nat )(x:(listn n))(y:(listn m)) (a,b:nat) 
            (Eqlong n x m y) 
             ->(Eqlong (S n) (consn n a x) (S m) (consn m b y))
| Eql_niln :  (Eqlong O niln O niln).


Parameter W1 : (Eqlong O niln O niln)\/ ~(Eqlong O niln O niln).
Parameter W2 : (n,a:nat)(x:(listn n)) 
  (Eqlong O niln (S n)(consn n a x)) \/ ~(Eqlong  O niln (S n) (consn n a x)).
Parameter W3 : (n,a:nat)(x:(listn n)) 
 (Eqlong (S n) (consn n a x)  O niln) \/ ~(Eqlong (S n) (consn n a x)  O niln).
Parameter W4 : (n,a:nat)(x:(listn n)) (m,b:nat)(y:(listn m)) 
      (Eqlong  (S n)(consn n a x) (S m) (consn m b y))
        \/ ~(Eqlong (S n)(consn n a x) (S m) (consn m b y)).

Check
 <[n:nat][x:(listn n)][m:nat][y:(listn m)]
     (Eqlong n x m y)\/~(Eqlong n x m y)>Cases niln  niln  of
      niln niln   => W1
   |  niln (consn n a x)  => (W2 n a x)
   |  (consn n a x)  niln => (W3 n a x)
   | (consn n a x)  (consn m b y)  => (W4 n a x m b y)
 end.


Check 
[n,m:nat][x:(listn n)][y:(listn m)]
 <[n:nat][x:(listn n)][m:nat][y:(listn m)]
     (Eqlong n x m y)\/~(Eqlong n x m y)>Cases x y of
      niln niln   => W1
   |  niln (consn n a x)  => (W2 n a x)
   |  (consn n a x)  niln => (W3 n a x)
   | (consn n a x)  (consn m b y)  => (W4 n a x m b y)
 end.


Parameter Inv_r : (n,a:nat)(x:(listn n)) ~(Eqlong O niln (S n) (consn n a x)).
Parameter Inv_l : (n,a:nat)(x:(listn n)) ~(Eqlong (S n) (consn n a x) O niln).
Parameter Nff : (n,a:nat)(x:(listn n)) (m,b:nat)(y:(listn m)) 
               ~(Eqlong n x m y)
                -> ~(Eqlong (S n) (consn n a x) (S m) (consn m b y)).



Fixpoint Eqlongdec [n:nat; x:(listn n)] : (m:nat)(y:(listn m))
                                           (Eqlong n x m y)\/~(Eqlong n x m y)
:= [m:nat][y:(listn m)]
 <[n:nat][x:(listn n)][m:nat][y:(listn m)]
     (Eqlong n x m y)\/~(Eqlong n x m y)>Cases x y of
      niln niln   => (or_introl ? ~(Eqlong O niln O niln)  Eql_niln)

   |  niln ((consn n a x) as L)  => 
        (or_intror (Eqlong O niln (S n) L)  ? (Inv_r n a x))

   | ((consn n a x) as L)  niln => 
       (or_intror (Eqlong (S n) L O niln) ? (Inv_l n a x))


   | ((consn n a x) as L1) ((consn m b y) as L2) =>
     <(Eqlong (S n) L1 (S m) L2) \/~(Eqlong (S n) L1 (S m) L2)>
      Cases (Eqlongdec n x m y) of
        (or_introl h) => 
           (or_introl  ? ~(Eqlong (S n) L1 (S m) L2)(Eql_cons n m x y a b h))
      | (or_intror h) => 
           (or_intror (Eqlong (S n) L1 (S m) L2) ? (Nff n a x  m b y h))   
      end
 end.

(* ============================================== *)
(*     To test compilation of dependent case      *)
(*      Multiple Patterns                         *)
(* ============================================== *)
Inductive skel: Type :=
     PROP: skel
   | PROD: skel->skel->skel.

Parameter Can : skel -> Type.
Parameter default_can : (s:skel) (Can s).


Check [s1,s2:skel]
      <[s1,_:skel](Can s1)>Cases s1 s2 of
          PROP PROP => (default_can PROP)
        | s1 _ => (default_can s1)
        end.

Check  [s1,s2:skel]
[s1,s2:skel]<[s1:skel][_:skel](Can s1)>Cases s1 s2 of
  PROP PROP => (default_can PROP)
| (PROD x y) PROP => (default_can (PROD x y))
| (PROD x y) _ => (default_can (PROD x y))
| PROP _ => (default_can PROP)
end.

Check [s1,s2:skel]
<[s1:skel][_:skel](Can s1)>Cases s1 s2 of
  PROP                 PROP => (default_can PROP)
| (PROP as s)             _ => (default_can s)
| ((PROD s1 s2) as s)  PROP => (default_can s)
| ((PROD s1 s2) as s)   _   => (default_can s)
end.



(* to test bindings in nested Cases *)
(* ================================ *)
Inductive Pair : Set :=
  pnil : Pair |
  pcons : Pair -> Pair -> Pair.

Check [p,q:Pair]Cases p of
  (pcons _ x) => 
     Cases q of 
      (pcons _ (pcons _ x)) => True
     |  _  => False
     end
|  _  => False
end.


Check [p,q:Pair]Cases p of
  (pcons _ x) => 
     Cases q of 
      (pcons _ (pcons _ x)) => 
          Cases q of 
              (pcons _ (pcons _ (pcons _ x))) => x
           | _ => pnil
           end
     |  _  => pnil
     end
|  _  => pnil
end.




(* =====================  To test ERRORS ===============================

Check  <[n:nat][_:(listn n)]nat>Cases niln of 
                         (consn m _ niln) => m
                       | _ => (S O) end.

Check [F:IFExpr]
    <Prop>Cases F of
       (IfE (Var _) H I) => True
     | (IfE _ _ _)   => False
     |  _          => True
     end.

Check [l:(List nat)]<nat>Cases l of 
                         (Nil nat) =>O
                      | (Cons  a l) => (S a)
                      end.


Definition Berry := [x,y,z:bool] 
  Cases x y z of 
     true false _ => O
   | false _ true => (S O)
   | _ true false => (S (S O))
end.

Definition Berry := [x,y,z:bool] 
  <nat>Cases x y z of 
     true false _ => O
   | false _ true => (S O)
   | _ true false => (S (S O))
end.


Inductive MS: Set := X:MS->MS | Y:MS->MS.
 
Check  [p:MS]<nat>Cases p of (X x) => O end.





Check <(List nat)>Cases (Nil nat) of 
                NIL   => NIL
              | (CONS _ _)  => NIL

              end.

Check [n:nat]
       [l:(listn n)]
        <nat>Cases n of 
            O  => O
        |  (S n)  =>
             <([_:nat]nat)>Cases l of 
                 niln  => (S O)
              |  l'  => (length1 (S n) l')
             end
       end.

Check <nat>Cases (Nil nat) of 
                             ((Nil_) as b) =>b
                            |((Cons _ _ _) as d) => d
                      end.


Check  
  [n:nat]
         [l:(listn (S n))]
           <[z:nat](listn (pred z))>Cases l of 
                       niln  => niln
                    |  (consn n _ l)  => 
                           <[m:nat](listn m)>Cases l of 
                                             niln => niln
                                           | b => b
                                           end
                   end.

Parameter compare : (n,m:nat)({(lt n m)}+{n=m})+{(gt n m)}.
Check <nat>Cases (compare O O) of
               (* k<i *)  (left _ _ (left _ _ _)) => O
            |  (* k=i *)  (left _ _ _)  => O
            |  (* k>i *)  (right _ _ _) => O end.





 ========================================== 
   To test binding !!

Check [x:nat]<nat> Cases x  of ((S x) as b) => (S b) end.
let va=dbize_cci sigma env aa;;

Check [x:nat]<nat> Cases x  of ((S x) as b) => (S b x) end.
let va=dbize_cci sigma env aa;;


Check [x:nat]<nat> Cases x  of 
                  ((S x) as b) => <nat>Cases x  of
                                        x => x 
                                   end
                          end.

Check [x:nat]<nat> Cases x  of 
                  ((S x) as b) => <nat>Cases x  of
                                        x => (S b x)
                                   end
                          end.

Check [x:nat]<nat> Cases x  of (S x) => x end .

Check [x:nat]<nat> Cases x  of ((S y x) as b) => (S b x) end.

Check <nat> Cases (plus O O)  of ((S n) as b) => b end


======================================= *)



(* -------------------------------------------------------------------- *)
(*   Example to test patterns matching on dependent families            *)     (* This exemple extracted from the developement done by Nacira Chabane  *)
(* (equipe Paris 6)                                                     *)
(* -------------------------------------------------------------------- *)


Require Prelude.
Require Logic_TypeSyntax.
Require Logic_Type.


Section Orderings.
   Variable U: Type.
   
   Definition Relation :=  U -> U -> Prop.

   Variable R: Relation.
   
   Definition Reflexive : Prop :=  (x: U) (R x x).
   
   Definition Transitive : Prop :=  (x,y,z: U) (R x y) -> (R y z) -> (R x z).
   
   Definition Symmetric : Prop :=  (x,y: U) (R x y) -> (R y x).
   
   Definition Antisymmetric : Prop :=
      (x,y: U) (R x y) -> (R y x) -> x==y.
   
   Definition contains : Relation -> Relation -> Prop :=
      [R,R': Relation] (x,y: U) (R' x y) -> (R x y).
  Definition same_relation : Relation -> Relation -> Prop :=
      [R,R': Relation] (contains R R') /\ (contains R' R).
Inductive Equivalence : Prop :=
         Build_Equivalence:
           Reflexive -> Transitive -> Symmetric -> Equivalence.
   
   Inductive PER : Prop :=
         Build_PER: Symmetric -> Transitive -> PER.
   
End Orderings.

(***** Setoid  *******)

Inductive Setoid : Type 
  := Build_Setoid : (S:Type)(R:(Relation S))(Equivalence ? R) -> Setoid.

Definition elem := [A:Setoid]
                   <Type>Match A with [S:?][R:?][e:?]S end.

Grammar command command1 :=
 elem  [ "|" command0($s) "|"] -> [ <<(elem $s)>>].

Definition equal := [A:Setoid]
   <[s:Setoid](Relation |s|)>Match A with [S:?][R:?][e:?]R end.


Grammar command command1 :=
 equal   [ command0($c) "=" "%" "S" command0($c2) ] -> 
         [ <<(equal ? $c $c2)>>].


Axiom prf_equiv : (A:Setoid)(Equivalence |A| (equal A)).
Axiom prf_refl : (A:Setoid)(Reflexive |A| (equal A)).
Axiom prf_sym : (A:Setoid)(Symmetric |A| (equal A)).
Axiom prf_trans : (A:Setoid)(Transitive |A| (equal A)).

Section Maps.
Variables A,B: Setoid.

Definition Map_law := [f:|A|->|B|]
    (x,y:|A|) x =%S y -> (f x) =%S (f y).

Inductive Map : Type :=
    Build_Map : (f:|A|->|B|)(p:(Map_law f))Map.

Definition explicit_ap := [m:Map] <|A|->|B|>Match m with 
         [f:?][p:?]f end.

Axiom pres : (m:Map)(Map_law (explicit_ap m)).

Definition ext := [f,g:Map]
         (x:|A|) (explicit_ap f x) =%S (explicit_ap g x).

Axiom Equiv_map_eq : (Equivalence Map ext).

Definition Map_setoid := (Build_Setoid Map ext Equiv_map_eq).

End Maps.

Syntactic Definition ap := (explicit_ap ? ?). 

Grammar command command8 :=
  map_setoid [ command7($c1) "=>" command8($c2) ] 
                 -> [ <<(Map_setoid $c1 $c2)>>].


Definition ap2 := [A,B,C:Setoid][f:|(A=>(B=>C))|][a:|A|] (ap (ap f a)).



(*****    posint     ******)

Inductive posint : Type
        := Z : posint | Suc : posint -> posint.

Require Logic_Type.

Axiom f_equal : (A,B:Type)(f:A->B)(x,y:A) x==y -> (f x)==(f y).
Axiom eq_Suc : (n,m:posint) n==m -> (Suc n)==(Suc m).

(* The predecessor function *)

Definition pred : posint->posint
     := [n:posint](<posint>Case n of (* Z *) Z 
                            (* Suc u *) [u:posint]u end).

Axiom pred_Sucn : (m:posint) m==(pred (Suc m)).
Axiom eq_add_Suc : (n,m:posint) (Suc n)==(Suc m) -> n==m.
Axiom not_eq_Suc : (n,m:posint) ~(n==m) -> ~((Suc n)==(Suc m)).


Definition IsSuc : posint->Prop
  := [n:posint](<Prop>Case n of (* Z *) False
                          (* Suc p *) [p:posint]True end).
Definition IsZero :posint->Prop :=
	[n:posint]<Prop>Match n with 
		True
		[p:posint][H:Prop]False end.

Axiom Z_Suc : (n:posint) ~(Z==(Suc n)).
Axiom  Suc_Z: (n:posint) ~(Suc n)==Z.
Axiom n_Sucn : (n:posint) ~(n==(Suc n)).
Axiom Sucn_n : (n:posint) ~(Suc n)==n.
Axiom eqT_symt : (a,b:posint) ~(a==b)->~(b==a).


(*******  Dsetoid *****)

Definition Decidable :=[A:Type][R:(Relation A)]
		(x,y:A)(R x y) \/ ~(R x y).


Record DSetoid : Type :=
{Set_of : Setoid;
 prf_decid : (Decidable |Set_of| (equal Set_of))}.

(* example de Dsetoide d'entiers *)


Axiom eqT_equiv : (Equivalence posint (eqT posint)).
Axiom Eq_posint_deci : (Decidable posint (eqT posint)).

(* Dsetoide des posint*)

Definition Set_of_posint := (Build_Setoid posint (eqT posint) eqT_equiv).

Definition Dposint := (Build_DSetoid Set_of_posint Eq_posint_deci).



(**************************************)


(* Definition des signatures *)
(* une signature est un ensemble d'operateurs muni
 de l'arite de chaque operateur *)


Section Sig.

Record Signature :Type :=
{Sigma : DSetoid; 
 Arity : (Map (Set_of Sigma) (Set_of Dposint))}.

Variable S:Signature.



Variable Var : DSetoid.

Mutual Inductive TERM : Type :=
	  var : |(Set_of Var)|->TERM
	| oper : (op: |(Set_of (Sigma S))|) (LTERM (ap (Arity S) op)) -> TERM
with
	LTERM : posint -> Type :=
	  nil : (LTERM Z)
	| cons : TERM -> (n:posint)(LTERM n) -> (LTERM (Suc n)).



(* -------------------------------------------------------------------- *)
(*                  Examples                                            *)
(* -------------------------------------------------------------------- *)


Parameter t1,t2: TERM.

Check 
 Cases t1 t2 of 
   (var  v1) (var v2) => True

 | (oper op1 l1)  (oper op2 l2) => False
 | _ _ => False 
 end.



Parameter n2:posint.
Parameter l1, l2:(LTERM n2).

Check 
 Cases l1 l2  of
    nil            nil => True 
 |  (cons v m y)   nil => False
 |  _               _  => False
end.


Check Cases l1 l2 of
    nil              nil      => True 
 | (cons u n x)  (cons v m y) =>False
 |   _               _        => False
end.



Fixpoint equalT [t1:TERM]:TERM->Prop :=
[t2:TERM] 
 Cases t1 t2 of 
   (var  v1)        (var v2)    => True
 | (oper op1 l1)  (oper op2 l2) => False
 |  _                   _       => False 
 end

with EqListT [n1:posint;l1:(LTERM n1)]: (n2:posint)(LTERM n2)->Prop :=
[n2:posint][l2:(LTERM n2)]
 Cases l1 l2 of
    nil                 nil             => True 
 | (cons t1 n1' l1')  (cons t2 n2' l2') => False
 | _                    _               => False
end.


Reset equalT.
Reset EqListT.
(* ------------------------------------------------------------------*)
(*          Initial exemple (without patterns)                       *)
(*-------------------------------------------------------------------*)

Fixpoint equalT [t1:TERM]:TERM->Prop :=
<TERM->Prop>Case t1 of 
	(*var*) [v1:|(Set_of Var)|][t2:TERM]
		<Prop>Case t2 of
		(*var*)[v2:|(Set_of Var)|] (v1 =%S v2)
		(*oper*)[op2:|(Set_of (Sigma S))|][_:(LTERM (ap (Arity S) op2))]False
		end
	(*oper*)[op1:|(Set_of (Sigma S))|]
                [l1:(LTERM (ap (Arity S) op1))][t2:TERM]
                <Prop>Case t2 of
		(*var*)[v2:|(Set_of Var)|]False
		(*oper*)[op2:|(Set_of (Sigma S))|]
                        [l2:(LTERM (ap (Arity S) op2))]
			((op1=%S op2)/\ (EqListT (ap (Arity S) op1) l1 (ap (Arity S) op2) l2))
		end
end
with EqListT [n1:posint;l1:(LTERM n1)]: (n2:posint)(LTERM n2)->Prop :=
<[_:posint](n2:posint)(LTERM n2)->Prop>Case l1 of
	(*nil*) [n2:posint][l2:(LTERM n2)]
		<[_:posint]Prop>Case l2 of
		(*nil*)True
	 	(*cons*)[t2:TERM][n2':posint][l2':(LTERM n2')]False
	end
	(*cons*)[t1:TERM][n1':posint][l1':(LTERM n1')]
		[n2:posint][l2:(LTERM n2)]
		<[_:posint]Prop>Case l2 of
		(*nil*) False
		(*cons*)[t2:TERM][n2':posint][l2':(LTERM n2')]
			((equalT t1 t2) /\ (EqListT n1' l1' n2' l2'))
		end
end.


(* ---------------------------------------------------------------- *)
(*                Version with simple patterns                      *)
(* ---------------------------------------------------------------- *)
Reset equalT.

Fixpoint equalT [t1:TERM]:TERM->Prop :=
Cases t1 of 
  (var  v1) => [t2:TERM]
	        Cases t2 of
		     (var v2) => (v1 =%S v2)
		 | (oper op2 _) =>False
		 end
| (oper op1 l1) => [t2:TERM]
		    Cases t2 of
	              (var _) => False
                    | (oper op2 l2) => (op1=%S op2)
                      /\ (EqListT (ap (Arity S) op1) l1 (ap (Arity S) op2) l2)
		    end
end
with EqListT [n1:posint;l1:(LTERM n1)]: (n2:posint)(LTERM n2)->Prop :=
<[_:posint](n2:posint)(LTERM n2)->Prop>Cases l1 of
  nil => [n2:posint][l2:(LTERM n2)]
          Cases l2 of
              nil => True
	  | _  => False
	  end
| (cons t1 n1' l1') => [n2:posint][l2:(LTERM n2)]
		        Cases l2 of
		           nil =>False
		        | (cons t2 n2' l2') => (equalT t1 t2) 
                                                /\ (EqListT n1' l1' n2' l2')
		end
end.


Reset equalT.

Fixpoint equalT [t1:TERM]:TERM->Prop :=
Cases t1 of 
  (var  v1) => [t2:TERM]
	        Cases t2 of
		     (var v2) => (v1 =%S v2)
		 | (oper op2 _) =>False
		 end
| (oper op1 l1) => [t2:TERM]
		    Cases t2 of
	              (var _) => False
                    | (oper op2 l2) => (op1=%S op2)
                      /\ (EqListT (ap (Arity S) op1) l1 (ap (Arity S) op2) l2)
		    end
end
with EqListT [n1:posint;l1:(LTERM n1)]: (n2:posint)(LTERM n2)->Prop :=
[n2:posint][l2:(LTERM n2)]
Cases l1 of
  nil => 
          Cases l2 of
              nil => True
	  | _  => False
	  end
| (cons t1 n1' l1') =>  Cases l2 of
		           nil =>False
		        | (cons t2 n2' l2') => (equalT t1 t2) 
                                                /\ (EqListT n1' l1' n2' l2')
		end
end.

(* ---------------------------------------------------------------- *)
(*                  Version with multiple patterns                  *)
(* ---------------------------------------------------------------- *)
Reset equalT.

Fixpoint equalT [t1:TERM]:TERM->Prop :=
[t2:TERM] 
 Cases t1 t2 of 
   (var  v1)       (var v2)     => (v1 =%S v2)

 | (oper op1 l1)  (oper op2 l2) => 
     (op1=%S op2) /\ (EqListT (ap (Arity S) op1) l1 (ap (Arity S) op2) l2)

 |  _               _ => False 
 end

with EqListT [n1:posint;l1:(LTERM n1)]: (n2:posint)(LTERM n2)->Prop :=
[n2:posint][l2:(LTERM n2)]
 Cases l1 l2 of
    nil                nil              => True 
 | (cons t1 n1' l1')  (cons t2 n2' l2') => (equalT t1 t2) 
                                          /\ (EqListT n1' l1' n2'  l2')
 | _ _ => False
end.


(* ------------------------------------------------------------------ *)

End Sig.

(* Test de la syntaxe avec nombres *)
Require Arith.
Check [n] Cases n of 2 => true | _ => false end.