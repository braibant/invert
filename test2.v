
Declare ML Module "invert".

Section t. 
  Variable A : Type.
  
  Inductive vector: nat ->  Type :=
  | nil : vector 0
  | cons : forall n : nat, forall x : A, forall v : vector n, vector (S n).
  
  Inductive P : forall n:nat, vector n -> Type :=
  | Pnil : P 0 nil
  | Pcons : forall n v, P n v -> forall h, P (S n) (cons n h v).

  Lemma l2 n h v : 
    P (S n) (cons n h v) -> P n v.
  Proof. intros H.
         diag H D.
         refine (match H in P n' v' return diag n' v' H with | Pnil  => _  |Pcons n v h' h => _ end).
         simpl. 
         auto. simpl. auto. 
         Show Proof. 
  Qed.

Definition rect2 (P:forall {n}, vector n -> vector n -> Type)
  (bas : P nil nil) (rect : forall {n v1 v2}, @P n v1 v2 ->
    forall a b, P (cons _ a v1) (cons _ b v2)) : forall n
    (v1 v2 : vector n), P v1 v2.
Proof.
fix 2.
intros n v1. invert v1.
 + intros v2. invert v2. assumption. 
 + intros m t1 q1 v2.
   invert v2. 
   intros m' t2 q2 q1'. apply rect. apply rect2.
Defined.
Print rect2.

Lemma l3 n h v : 
  P (S (S n)) (cons (S n) h v) -> P (S n) v.
Proof. 
  intros H.
  invert H.
  now intros.
Qed.

End t.