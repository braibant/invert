Declare ML Module "invert".

Inductive even : nat -> Type :=
  | even_0 : even 0
  | even_SS : forall n, even n -> even (S (S n)).


Lemma l0 n (H: even (2+n)) : even n.
Proof.
  refine (let diag := fun n : nat =>
          match n as n' return (even n' -> Type) with
            | 0 => fun _ : even 0 => False -> True
            | S x =>
              match x as x' return (even (S x') -> Type) with
                | 0 => fun _ : even 1 => False -> True
                | S x0 => fun _ : even (S (S x0)) => even x0
              end
          end in _ ).
  refine (match H in even n' return diag n' H with | even_0 => _ | even_SS n H' => _ end).
  simpl; auto.  Show Proof.
  simpl; auto.  Show Proof.
Qed.

Lemma l1 : forall n, even (2 + n) -> even n.
Proof.
  intros.
  Set Printing All.
  diag H D.
  refine (match H as H' in even n' return diag n' H' with | even_0 => _ | even_SS n H' => _ end).
  simpl; auto.  Show Proof.
  simpl; auto.  Show Proof.
Qed.

Lemma l2:  forall n, even (2 + n) -> even n.
  intros.
  invert H.  auto.  Show Proof. 
Qed.

Lemma l3:  forall n, even (2 + n) -> even n.
 intros. invert H;auto. Show Proof.
Qed.
