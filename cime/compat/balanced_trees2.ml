(***************************************************************************

Balanced trees with two data info (one key, one data)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


type ('a,'b) node_info =
    {
      key : 'a;
      data : 'b;
      height : int;
      left : ('a,'b) t;
      right : ('a,'b) t
    }	
    
and ('a,'b) t =
    Empty
  | Node of ('a,'b) node_info
      
let empty = Empty
	      
let height = function
    Empty -> 0
  | Node(i) -> i.height
	
let create l x d r =
  let hl = height l 
  and hr = height r 
  in
  Node
    {
      key = x;
      data = d;
      height = if hl >= hr then hl + 1 else hr + 1;
      left = l;
      right = r
    } 
    
let bal l x d r =
  let hl = height l
  and hr = height r
  in 
  if hl > hr + 2 
  then 
    begin
      match l with
          Empty -> invalid_arg "Balanced_trees2.bal"
        | Node(il) -> 
            if height il.left >= height il.right 
	    then
              create il.left il.key il.data (create il.right x d r)
            else 
	      begin
              	match il.right with
                    Empty -> invalid_arg "Balanced_trees2.bal"
              	  | Node(ilr) -> 
                      create 
			(create il.left il.key il.data ilr.left) 
			ilr.key 
			ilr.data 
			(create ilr.right x d r)
              end
    end 
  else 
    if hr > hl + 2 
    then 
      begin
        match r with
            Empty -> invalid_arg "Balanced_trees2.bal"
          | Node(ir) -> 
              if height ir.right >= height ir.left 
	      then
		create (create l x d ir.left) ir.key ir.data ir.right
              else 
		begin
		  match ir.left with
                      Empty -> invalid_arg "Balanced_trees2.bal"
		    | Node(irl) ->
                      	create 
			  (create l x d irl.left) 
			  irl.key 
			  irl.data 
			  (create irl.right ir.key ir.data ir.right)
            	end
      end 
    else
      Node
	{
	  key = x;
	  data = d;
	  height = if hl >= hr then hl + 1 else hr + 1;
	  left = l;
          right = r
   	}  
	
let rec merge t1 t2 =
  match (t1, t2) with
      (Empty, t) -> t
    | (t, Empty) -> t
    | (Node(i1),Node(i2)) ->
        bal 
	  i1.left 
	  i1.key 
	  i1.data 
	  (bal (merge i1.right i2.left) i2.key i2.data i2.right)
	  

    let rec iter f = function
        Empty -> ()
      | Node(i) ->
          iter f i.left; f i.key i.data; iter f i.right

    let rec map f = function
        Empty -> Empty
      | Node(i) -> 
	  Node
	    {
	      key = i.key;
	      data = f i.data;
	      height = i.height;
	      left = map f i.left;
	      right = map f i.right
   	    } 

    let rec mapi f = function
        Empty -> Empty
      | Node(i) -> 
	  Node
	    {
	      key = i.key;
	      data = f i.key i.data;
	      height = i.height;
	      left = mapi f i.left;
	      right = mapi f i.right
   	    } 

    let rec fold f m accu =
      match m with
        Empty -> accu
      | Node(i) ->
          fold f i.left (f i.key i.data (fold f i.right accu))

