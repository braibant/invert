Inductive even : nat -> Prop :=
  | even_0 : even 0 
  | even_SS : forall n, even n -> even (S (S n)).

Declare ML Module "invert". 
Lemma l1 : forall n, even (2 + n) -> even n. 
  intros. invert H. inversion H. Show Proof. 
  