Inductive even : nat -> Prop :=
  | even_0 : even 0 
  | even_SS : forall n, even n -> even (S (S n)).

Declare ML Module "invert". 
Lemma l1 : forall n, even (2 + n) -> even n. 
  intros. Set Printing All.
  set (diag := fun x =>                                
                 match x return Prop with
                   | S (S x1) => even x1 
                   | _ => even x
                 end). 
  
  refine (match H in even args return diag args
           with 
             | even_0 => _
             | even_SS n x => _
           end). simpl.  constructor. 
  simpl. auto. 
  Restart. 
  intros. 
  set (diag := fun x =>                                
                 match x return Prop with
                   | S (S x1) => even x1 
                   | _ => even n
                 end). 
  
  refine (match H in even args return diag args
          with 
            | even_0 => _
            | even_SS n x => _
          end); simpl.  
  Restart.
  intros. 
  invert H. 

  Grab Existential Variables. 
  simpl. auto. 
  simpl. constructor. 
Abort. 
  
  Restart. 
  intros. 
  refine (let diag :=
       fun x : nat =>
                                match x return Prop with
                              | O => even x
                              | S x0 =>
                                  match x0 return Prop with
                                  | O => even x0
                                  | S x1 => even x1
                                  end
                              end in
                            match H in (even args) return (diag args) with
                            | even_0 => _:diag O
                            | even_SS n x => _:diag (S (S n))
                            end).
  apply even_0. simpl. auto. 
