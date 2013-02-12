Inductive even : nat -> Type :=
  | even_0 : even 0 
  | even_SS : forall n, even n -> even (S (S n)).

Declare ML Module "invert". 
Lemma l1 : forall n, even (2 + n) -> even n. 
  intros. Set Printing All.
  set (diag := fun x =>                                
                 match x return Type with
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
                 match x return Type with
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
  invert H. constructor.  intros; auto. Show Proof. 
Qed. 


Inductive mul3 : nat -> Prop :=
  | T0 : mul3 0
  | T3: forall n, mul3 n -> mul3 (3 + n).

Lemma inv_mul_3plusn : forall n, mul3 (3 + n) -> mul3 n.
Proof.
intros n m. 
invert m. constructor. 
simpl. auto. 
Qed. 

(* Not in the paper: version without 0 *)
Lemma inv_mul_3plusn_no0 : forall n, mul3 (3 + n) -> mul3 n.
Proof.
intros n m.
invert m. 
constructor.
simpl. auto. 
Qed.



Section sec_absu_2ismul3.

Variable C: Prop.

Lemma absurd2_inv : mul3 2 -> C.
Proof.
intros H. 
(* invert H. *)
Abort. 

End sec_absu_2ismul3.