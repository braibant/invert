
Declare ML Module "invert".

Section t. 
  Variable A : Type.
  
  Inductive vector: nat ->  Type :=
    |   nil : vector 0
    | cons : forall n : nat, forall x : A, forall v : vector n, vector (S n).

  Inductive P : forall n:nat, vector n -> Type :=
    | Pnil : P 0 nil
    | Pcons : forall n v, P n v -> forall h, P (S n) (cons n h v). 
    
  Lemma l0 n h v: 
    P (S n) (cons n h v) -> P n v.
      intros H.
      
      refine (
          let diag n :=
              match n as n' return vector n' -> Type with 
                | 0 =>  fun v => False -> True
                | S n => fun (v: vector (S n)) => 
                          match v in vector m return Type with 
                            | nil => False -> True
                            | cons m h t =>  P m t
                          end
              end
          in _ ). 
      Set Printing All. 
      refine (match H in P n' v' return diag n' v' with | Pnil  => _  |Pcons n v h' h => _ end).
      simpl. auto. 
      simpl.  auto.
      
  Qed. 

  Lemma l1 n h v: 
    P (S n) (cons n h v) -> P n v.
      intros H.
      
      refine (let diag := fun n : nat =>
          match n as n0 return (forall v : vector n0, P n0 v -> Type) with
          | 0 => fun (v : vector 0) (_ : P 0 v) => False -> True
          | S x =>
              fun v : vector (S x) =>
              match v as v0 in vector  m return (P m v0 -> Type) with
                | nil => fun _ => False -> True
                | cons n0 x0 v0 => fun _ => P n0 v0
              end
          end in _ ). 
      
      refine (match H in P n' v' return diag n' v' H with | Pnil  => _  |Pcons n v h' h => _ end).
      simpl. auto. 
      simpl.  auto.
      
  Qed. 

  Lemma l2 n h v : 
    P (S n) (cons n h v) -> P n v.
  Proof. intros H. 
         diag H D.  
      refine (match H in P n' v' return diag n' v' H with | Pnil  => _  |Pcons n v h' h => _ end).
      simpl. 
      auto. simpl. auto. 
      Show Proof. 
  Qed. 
  Lemma l3 n h v : 
    P (S n) (cons n h v) -> P n v.
  Proof. intros H. 
      intros H. invert H. auto. auto. Show Proof. 
  Qed.
End t.  