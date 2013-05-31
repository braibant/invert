Declare ML Module "invert".

Inductive tm : Type :=
  | const : nat -> tm
  | plus : tm -> tm -> tm. 

Inductive val : Type :=
  | nval : nat -> val
  | bval : bool -> val. 

Inductive eval : tm -> val -> Prop :=
| econst : forall n, eval (const n) (nval n)
| eplus : forall t1 t2 n1 n2, eval t1 (nval n1) -> 
                         eval t2 (nval n2) -> 
                         eval (plus t1 t2) (nval (n1 + n2)).

Goal forall v, eval (plus (const 0) (const 1)) (nval v) -> 
          v = 1. 
Proof.
intros.
invert H.
intros.
invert H. invert H0. reflexivity.
Qed.
