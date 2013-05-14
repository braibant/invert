
Declare ML Module "invert".

Lemma test n m (H : Some n = Some m) :  S n = S m.
Proof. 
  invert H. reflexivity. 
Qed. 

Lemma test2 n (H : Some n = None) :  S n = n.
Proof. 
  invert H; auto. 
Qed. 

Lemma test3 (H : Some nat = Some bool) : True.  
  Fail invert H. 
Abort. 

