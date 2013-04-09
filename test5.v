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

intros. 
invert H. auto.
simpl.  
set (diag := fun t (v1: val) => match t with 
                         | const _ => v = 1
                         | plus t1 t2 => forall (X: Prop), X
                         end). 
refine (match H in eval t v return diag t v with 
          | econst _ => I
          | eplus t1 t2 n1 n2 H1 H2 => _ end _ ) .
simpl.  admit. 
invert H. 
Abort. 
