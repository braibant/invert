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
    refine (let diag n :=
                match n return t n -> Type with 
                    | 0 => fun v => False -> True
                    | S n => fun (v : t (S n)) => 
                              P n v
                  end in 
              _
             ).
      refine (match v in t n' return diag n' v with 
                | [] => _
                | cons h m q => _
              end
             ).
      simpl. auto. 
      simpl. clear diag v n. 
      
      refine (match m return forall (v : t m), P m (h::v) with
               | 0 => fun v => _ 
               | S n => fun v => _
             end q). 
      {
        refine (let diag n :=
                    match n return t n -> Type with 
                      | 0 => fun v => P 0 (h :: v)
                      | S n => fun v => False -> True
                    end 
                in _
                     
               ).
        refine (match v in t n' return diag n' v with 
                  | nil => _
                  | cons _ _ _ => _
                end). 
        simpl. apply bas. 
        simpl. auto. 
      }
      {
        apply rect.  apply rectS. 
      }
      Restart.
fix 2. intros n v.
invert v.
apply False_rect.
destruct n0.
{ intros. invert X.
apply bas. exact (fun a b c => False_rect _). }
{ intros. apply rect. apply rectS. }
Defined.
End t.