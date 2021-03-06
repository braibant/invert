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
 intro t1; destruct t1. destruct n.
 intro t2; destruct t2. destruct n.
  exact (fun a b c d => False_rect _).
 destruct n.
  intros.
   invert H. destruct n.
   invert H0. destruct n. apply False_rect. destruct n.
   reflexivity. apply False_rect.
  apply False_rect.
  exact (fun a b c d => False_rect _).
  exact (fun a b c d => False_rect _).
  exact (fun a b c d e => False_rect _).
  exact (fun a b c d e => False_rect _).
Qed.
