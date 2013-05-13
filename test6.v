
Declare ML Module "invert".

Section t. 
  Variable A : Type.
  
  Inductive vector: nat ->  Type :=
    |   nil : vector 0
    | cons : forall n : nat, forall x : A, forall v : vector n, vector (S n).
  
  Inductive P : forall n:nat, vector n -> vector n -> Type :=
    | Pnil : P 0 nil nil
    | Pcons : forall n v1 v2 , P n v1 v2 -> forall h, P (S n) (cons n h v1) (cons n h v2). 
    
  Lemma l0 n h v1 v2: 
    P (S n) (cons n h v1) (cons n h v2) -> P n v1 v2.
      
  Proof. 
    intros H.
    invert H. 
    auto. 
    Show Proof. 
  Qed. 
End t. 