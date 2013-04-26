Declare ML Module "invert".

Inductive mul3 : nat -> Prop :=
  | T0 : mul3 0
  | T3: forall n, mul3 n -> mul3 (3 + n).

Lemma inv_mul_3plusn : forall n, mul3 (3 + n) -> mul3 n.
Proof.
intros n m. 
invert m.
simpl. auto. 
Qed. 

(* Not in the paper: version without 0 *)
Lemma inv_mul_3plusn_no0 : forall n, mul3 (3 + n) -> mul3 n.
Proof.
intros n m.
invert m.
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
