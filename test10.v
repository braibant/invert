Declare ML Module "invert".

Section t. 
  Inductive vector: nat ->  Type :=
  | nil : vector 0
  | cons : forall n : nat, forall v : vector n, vector (S n).
  
  Inductive P : forall n:nat, vector n -> Type :=
  | Pnil : P 0 nil
  | Pcons : forall n v, P n v ->  P (S n) (cons n v).

  Lemma l2 n v (H: P (S n) (cons n v)) : P n v.
  Proof. 
    invert v ; [idtac  | idtac ]. 
  Abort. 
  (* TODO: n should disappear!! *)
End t. 
