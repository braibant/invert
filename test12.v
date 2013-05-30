Axiom A :Type. 
Inductive vect : nat -> Type :=
| nil : vect 0
| cons : forall n (x:A) (v:vect n), vect (S n). 

Inductive P : forall n m, vect n -> vect m -> Type :=
| P0 : P 0 0 nil nil
| PS : forall n m vn vm h, P n m vn vm -> 
                      P (S n) (S m) (cons n h vn) (cons m h vm). 

Axiom Q : forall n (v1 : vect (S n)) (v2: vect (S n)), P (S n) (S n) v1 v2 -> Type.
Goal forall n h1 h2 vn vm (H : P (S n) (S n)  (cons n h1 vn) (cons n h2 vm))
                          , Q  n  (cons n h1 vn) (cons n h2 vm) H. 
Proof. 
  intros. 
Require Import Equality.
Definition admit A : A . Admitted. 

refine (
let diag :=
    fun n  =>
      match
        n as n'
        return
        (forall (m : nat) (v1 : vect n') (v2 : vect m),
           P n' m v1 v2 -> Type)
      with
        | 0 =>
          fun (m0 : nat) (v1 : vect 0) (v2 : vect m0) (_ : P 0 m0 v1 v2) =>
            False -> True
        | S n => 
          fun m : nat =>
            match m return (forall (v1 : vect (S n)) (v2 : vect m), P (S n) m v1 v2 -> Type)
            with
              | 0 => fun (v1 : vect (S n)) (v2 : vect 0) (_ : P (S n) 0 v1 v2) => False -> True
              | S m => 
                fun v1 v2 H' => forall (H : n = m), 
                                 eq_rect n _ 
                                        (fun v1 : vect (S n) =>
                                           match
                                             v1 in vect a return
                                             (match a return (vect a -> Type) with
                                                | 0 => fun _ : vect 0 => False -> True
                                                | S n =>
                                                  fun v1 : vect (S n) =>
                                                    forall v2 : vect (S n),
                                                      P (S n) (S n) v1 v2 -> Type
                                              end v1)
                                           with
                                             | nil => fun H : False => False_rect True H
                                             | cons n h1 v1' => 
                                               (* n: nat; v1': vect n *)
                                               fun (v2: vect (S n)) H' => 
                                                 match v2 in (vect a) return 
                                                       (match a return vect a -> Type with 
                                                          | 0 => fun _ => False -> True
                                                          | S n => 
                                                            fun v2' => 
                                                            forall v1' : vect n, 
                                                            P (S n) (S n) (cons n h1 v1') v2' ->   
                                                            Type
                                                        end v2) 
                                                 with 
                                                   | nil => fun H => False_rect True H 
                                                   | cons n h2 v2' => fun (v1': vect n) H' => 
                                                                       Q n (cons n h1 v1') (cons n h2 v2') H'
                                                 end v1' H'
                                           end
                                        ) m H v1 v2 H'
                                        
            end
      end 
in 
    _ ).
pose (x := diag (S n) (S n) (cons n h1 vn) (cons n h2 vm) H). 
refine 
  (match H as H' in P n m v1 v2 return diag n m v1 v2 H'
    with 
      | P0 => _
      | PS a b c d e f => _
    end eq_refl); simpl. auto. 
intros. destruct H0. simpl.  