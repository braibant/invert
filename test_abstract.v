Require Fin. 
Declare ML Module "invert".
Require Import JMeq. 
Require Import Program. 

Definition app {n m} : Fin.t n -> Fin.t m -> Fin.t (n + m). Admitted. 

Module B. 
  Notation fin := Fin.t.

  Inductive I : forall n, Fin.t n -> Type :=
  | C1 : forall n v, I (S n) (Fin.FS v).
  
  Lemma t : forall n m (fm: fin m) (fn : fin n) (fnm : fin (n + m)),
              I (n + m) fnm -> 
              @eq (fin (n+m)) (app fn fm) fnm. 
  Proof. 
    intros.
    dependent destruction H. Show Proof. 
    Abort. 
End B. 

Module A. 
Inductive J : forall n m, Fin.t (n + m) -> Type :=
| C1 : forall n m v, J n m v -> J n m v.

Lemma test0 n m fnm (P: nat -> nat -> Prop) : 
  J (S (n + n)) m (fnm) -> P n m. 
Proof. 
  intros H.
  set (k := n + n) in *. 
  Set Printing All. 
  clearbody k.
  invert H. simpl. 
Abort. 
End A. 

Inductive I : forall n, Fin.t n -> Type :=
| C1 : forall n v, I n v -> I (S n) (Fin.FS v).


Lemma test0 n m fnm (P: nat -> nat -> Prop) : 
  I (S (n + m)) (Fin.FS fnm) -> P n m. 
Proof. 
  intros H. 
  (* invert H.  *)
  Set Printing All. 
  Print JMeq_refl. 
  Check @JMeq_refl nat (n+m). 
Abort. 

Lemma test1 n m fn fm (P: nat -> nat -> Prop) : 
  I (S (n + m)) (Fin.FS (app fn fm)) -> P n m. 
  intros H. 
  invert H. 
  revert H. 
  
  assert (JMeq (app fn fm) (app fn fm)) by reflexivity. 
  revert H. generalize (app fn fm) at 1 3. 
  
  assert (n + m = n + m) by reflexivity. 
  revert H. 
  generalize (n+m) at 1 3 4 6 7. 
  intros. invert H1. 
  
  Show Proof. 
  admit.
  destruct v. auto. 
  Show Proof