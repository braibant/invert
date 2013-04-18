
Declare ML Module "invert".

Section t. 
  Variable A : Type.
  
  Inductive vector: nat ->  Type :=
  | nil : vector 0
  | cons : forall n : nat, forall x : A, forall v : vector n, vector (S n).
  
  Inductive P : forall n:nat, vector n -> Type :=
  | Pnil : P 0 nil
  | Pcons : forall n v, P n v -> forall h, P (S n) (cons n h v). 
  
  Lemma i0 n h v:
    P (S n) (cons n h v) -> P n v.
  Proof. 
    refine (let diag n := match n as n0 return (forall (v : vector n0) (_ : P n0 v), Type) with
                            | O => fun (v : vector O) (_ : P O v) => forall _ : False, True
                            | S x =>
                              fun v : vector (S x) =>
                                match
                                  v as v0
                                  in (vector H)                                       
                                  return
                                  match H return Type with
                                    | O => forall _ : False, True
                                    | S n0 => P H v0 -> Type
                                  end
                                with
                                  | nil => fun _ => I
                                  | cons n0 x0 v0 => fun _ : P (S n0) (cons n0 x0 v0) => P n0 v0
                                end
                          end in _). 
    intros H. refine (match H in P n' v' return diag n' v' H with | Pnil  => _  |Pcons n v h' h => _ end); simpl. 
    auto. auto. 
  Qed. 

    
  Lemma l0 n h v: 
    P (S n) (cons n h v) -> P n v.
      intros H.
      
      refine (
          let diag n :=
              match n as n' return vector n' -> Type with 
                | 0 =>  fun v => False -> True
                | S n => fun (v: vector (S n)) => 
                          match v in vector m return Type with 
                            | nil => False -> True
                            | cons m h t =>  P m t
                          end
              end
          in _ ). 
      Set Printing All.
      refine (match H in P n' v' return diag n' v' with | Pnil  => _  |Pcons n v h' h => _ end).
      simpl. auto. 
      simpl.  auto.
      
  Qed. 

  Lemma l1 n h v: 
    P (S n) (cons n h v) -> P n v.
      intros H.
      
      refine (let diag := fun n : nat =>
          match n as n0 return (forall v : vector n0, P n0 v -> Type) with
          | 0 => fun (v : vector 0) (_ : P 0 v) => False -> True
          | S x =>
              fun v : vector (S x) =>
              match v as v0 in vector  m return (P m v0 -> Type) with
                | nil => fun _ => False -> True
                | cons n0 x0 v0 => fun _ => P n0 v0
              end
          end in _ ). 
      
      refine (match H in P n' v' return diag n' v' H with | Pnil  => _  |Pcons n v h' h => _ end).
      simpl. auto. 
      simpl.  auto.
      
  Qed. 

  Lemma l2 n h v : 
    P (S n) (cons n h v) -> P n v.
  Proof. intros H. 
         diag H D.  
      refine (match H in P n' v' return diag n' v' H with | Pnil  => _  |Pcons n v h' h => _ end).
      simpl. 
      auto. simpl. auto. 
      Show Proof. 
  Qed. 
  
  Lemma l3 n h v : 
    P (S n) (cons n h v) -> P n v.
  Proof. intros H.
         invert H. 
         auto. 
         auto. Show Proof. 
  Qed.

Definition rect2 (P:forall {n}, vector n -> vector n -> Type)
  (bas : P nil nil) (rect : forall {n v1 v2}, @P n v1 v2 ->
    forall a b, P (cons _ a v1) (cons _ b v2)) : forall n
    (v1 v2 : vector n), P v1 v2.
Proof.
fix 2.
intros n v1. invert v1.
 + intros v2; invert v2. assumption. exact (fun _ _ _ => False_rect _).
 + intros m t1 q1 v2.
   generalize q1. invert v2. exact (False_rect _).
   intros m' t2 q2 q1'. apply rect. apply rect2.
Defined.
Print rect2.

End t.  