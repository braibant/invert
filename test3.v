Declare ML Module "invert".

Section t. 
  Variable A: Type. 
  Inductive t : nat -> Type :=
  |nil : t 0
  |cons : forall (h:A) (n:nat), t  n -> t (S n).

  Local Notation "[]" := (nil ).
  Local Notation "h :: t" := (cons h _ t) (at level 60, right associativity).
  
  (** An induction scheme for non-empty vectors *)
  
  Lemma rectS (P:forall {n}, t (S n) -> Type)
        (bas: forall a: A, P (a :: []))
        (rect: forall a {n} (v: t (S n)), P v -> P (a :: v)) :  
    forall n (v: t (S n)),  P v.
    Proof.
      fix 2. intros n v.
      invert v.
      destruct n0.
      { intros. invert X.
        apply bas. }
      { intros. apply rect. apply rectS. } Show Proof.
    Defined.
End t.
