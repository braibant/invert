Inductive even : nat -> Prop :=
| even0 : even 0
| evenSS : forall n, even n -> even (S (S n)).

Declare ML Module "invert".
Lemma test : forall n m, even n ->  even (n + m) -> even m.
Proof. 
  intros n m e. induction e as [| n e IHe];simpl. 
  tauto. 
  intros e2. 
  revert IHe. remember (n+m) as x.  invert e2. 
  intros. auto. 
Qed. 
