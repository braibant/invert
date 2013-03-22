Inductive even : nat -> Type :=
  | even_0 : even 0
  | even_SS : forall n, even n -> even (S (S n)).

Declare ML Module "invert".

Lemma l1 : forall n, even (2 + n) -> even n.
Proof.
  intros.
  invert H. simpl.  auto. simpl. auto.
 Show Proof. 
Qed. 

Section ex1. 
  Variable A : Type.
  
  Inductive vector: nat ->  Type :=
    |   nil : vector 0
    | cons : forall n : nat, forall x : A, forall v : vector n, vector (S n).

  Inductive P : forall n:nat, vector n -> Prop :=
    | Pnil : P 0 nil
    | Pcons : forall n v, P n v -> forall h, P (S n) (cons n h v). 
    
  Lemma foo n h v: 
    P (S n) (cons n h v) -> P n v.
      intros H.
      Set Printing All. 
      invert H.  auto. auto. Show Proof. 
  Qed.
End ex1.  

Module vectors. 
 
Inductive t A : nat -> Type :=
  |nil : t A 0
  |cons : forall (h:A) (n:nat), t A n -> t A (S n).

Local Notation "[]" := (nil _).
Local Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

Section SCHEMES.

(** An induction scheme for non-empty vectors *)

Lemma rectS {A} (P:forall {n}, t A (S n) -> Type)
 (bas: forall a: A, P (a :: []))
 (rect: forall a {n} (v: t A (S n)), P v -> P (a :: v)) :  
forall n (v: t A (S n)),  P v.
fix 2. intros n v. invert v.  auto. intros. destruct n0. invert X. apply  bas. auto.
apply rect. apply rectS.
Qed.

Inductive mul3 : nat -> Prop :=
  | T0 : mul3 0
  | T3: forall n, mul3 n -> mul3 (3 + n).

Lemma inv_mul_3plusn : forall n, mul3 (3 + n) -> mul3 n.
Proof.
intros n m. 
invert m. constructor. 
simpl. auto. 
Qed. 

(* Not in the paper: version without 0 *)
Lemma inv_mul_3plusn_no0 : forall n, mul3 (3 + n) -> mul3 n.
Proof.
intros n m.
invert m. 
constructor.
simpl. auto. 
Qed.

Section sec_absu_2ismul3.
Variable C: Prop.
Lemma absurd2_inv : mul3 2 -> C.
Proof.
intros H.
invert H; simpl; intros; auto.
Show Proof.
Qed.  
End sec_absu_2ismul3.

Section vect. 
  Variable A : Type. 
  Inductive vector : nat -> Type :=
    | nil : vector 0
    | cons : forall n, A -> vector n -> vector (S n). 
  
  
  Goal forall v : vector 0, v = nil. 
  intros. 
  Fail invert v. 
  Abort. 
End vect. 
  

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
