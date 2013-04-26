
Declare ML Module "invert".

Inductive P : nat -> Prop :=
| C1 : forall n, P n -> P (S (S n))
| C2 : forall n, P (S n) -> P (S (S n))
| C3 : P 0. 


Lemma test n (H : P (2 + n)) :  P n \/ P (S n).
Proof. 
  inversion H; auto. Show Proof. Restart. 
  invert H; auto.  Show Proof. 
Qed. 
