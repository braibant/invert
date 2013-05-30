

Definition admit A : A. Admitted.  
Goal forall a b c,  @existT Type  (fun x => x) a  b = existT (fun x => x) a c -> b = c. 
Proof. 
  intros. 
  refine (
    match H in _ = E
            return 
            (match E return Type with 
               | existT _ a'  c =>                  
                 forall (H' : a' = a), 
                   (eq_rect a' (fun x => x -> Prop  ) (fun b => @eq a' b c) a H') 
                   b  
             end)
      with
        | eq_refl => _
      end eq_refl).  
  intros H'.  
  Require Import Eqdep. 
  rewrite <- eq_rect_eq. reflexivity.  
Qed. 