
Declare ML Module "invert".

Section t. 
  Variable A : Type.
  
  Inductive vector: nat ->  Type :=
    |   nil : vector 0
    | cons : forall n : nat, forall x : A, forall v : vector n, vector (S n).

  Inductive P : forall n:nat, vector n -> Type :=
    | Pnil : P 0 nil
    | Pcons : forall n v, P n v -> forall h, P (S n) (cons n h v). 
    
  Lemma foo n h v: 
    P (S n) (cons n h v) -> P n v.
      intros H.
      
      refine (
          let diag n :=
              match n as n' return vector n' -> Type with 
                | 0 =>  fun v => False -> True
                | S n => fun (v: vector (S n)) => 
                          match v return Type with 
                            | nil => False -> True
                            | cons m h t =>  P m t
                          end
              end
          in _ ). 
      
      refine (match H in P n' v' return diag n' v' with | Pnil  => _  |Pcons n v h' h => _ end).
      simpl. auto. 
      simpl.  auto.
      
      Restart. 
      Set Printing All. 
      intros H. diag H D.  
      refine (match H in P n' v' return diag n' v' with | Pnil  => _  |Pcons n v h' h => _ end).
      simpl. 
      auto. simpl. auto. Show Proof. 
      Restart. 
      intros H. invert H. auto. auto. Show Proof. 
  Qed.
End t.  