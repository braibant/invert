
Declare ML Module "invert".

Section t. 
  Variable A : Type.
  
  Inductive vector: nat ->  Type :=
    |   nil : vector 0
    | cons : forall n : nat, forall x : A, forall v : vector n, vector (S n).
  
  Inductive P : forall n:nat, vector n -> vector n -> Type :=
    | Pnil : P 0 nil nil
    | Pcons : forall n v1 v2 , P n v1 v2 -> forall h, P (S n) (cons n h v1) (cons n h v2). 
    
  Lemma l0 n h v1 v2: 
    P (S n) (cons n h v1) (cons n h v2) -> P n v1 v2.
      
  Proof. 
    intros H.
    invert H. auto. 
    intros. subst. auto. 
    Show Proof. 
  Fail Qed. 
  (* Restart.  *)
  (* intros.  *)
  (* refine ( *)
  (*     let d := (fun n : nat => *)
  (*                 match n as n0 return (forall v v0 : vector n0, P n0 v v0 -> Type) with *)
  (*                   | 0 => fun (v v0 : vector 0) (_ : P 0 v v0) => False -> True *)
  (*                   | S a => *)
  (*                     fun v : vector (S a) => *)
  (*                       match *)
  (*                         v as v0 in (vector n0) *)
  (*                         return (forall v1 : vector n0, P n0 v0 v1 -> Type) *)
  (*                       with *)
  (*                         | nil => fun (v0 : vector 0) (_ : P 0 nil v0) => False -> True *)
  (*                         | cons m x q => *)
  (*                           fun v1 : vector (S m) => *)
  (*                             match *)
  (*                               v1 as v2 in (vector k) *)
  (*                               return match k as k' return vector k' -> Type with  *)
  (*                                        | 0 => fun _ => False -> True *)
  (*                                        | S k' => fun v2' =>  *)
  (*                                          forall q' : vector k' , P (S k') (cons k' x q') v2' -> Type *)
  (*                                      end v2 *)
  (*                             with *)
  (*                               | nil => False_rect _ *)
  (*                               | cons n1 x1 v2 =>  *)
  (*                                 fun q' => fun H =>  *)
  (*                                            P n1 q' v2 *)
  (*                             end q *)
  (*                       end *)
  (*                 end) in _ ).  *)
  
  (* refine (match X as X' in P a b c return d a b c X' with  *)
  (*           | Pnil => _  *)
  (*           | Pcons n v1 v2 H h => _ end); simpl.  *)
  (* auto.  *)
  (* auto.  *)

  (* Restart.  *)
  (* intros.  *)
  (* Qed.  *)
  Show Proof. 
Qed.