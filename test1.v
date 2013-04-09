Declare ML Module "invert".

Inductive even : nat -> Type :=
  | even_0 : even 0
  | even_SS : forall n, even n -> even (S (S n)).


Lemma l1 : forall n, even (2 + n) -> even n.
Proof.
  intros.
  invert H. simpl.  auto. simpl. auto.
 Show Proof. 
 Restart. 
 intros. 
 diag H D.
 refine (match H in even n' return diag n' with | even_0 => _ | even_SS n H' => _ end); simpl. 
 auto. 
 auto.
Qed. 
