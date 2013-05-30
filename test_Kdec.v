Declare ML Module "invert".

Lemma Kbool (b : bool) (e : b = b) : e = eq_refl.
Proof.
destruct b;
invert e;
exact eq_refl.
Defined.
Eval compute in Kbool.

(*Lemma Ka (A : Type) (a : A) (H : forall (e : a = a), e = eq_refl) (eq : a = a) (eqeq : eq = eq)
  : eqeq = eq_refl.
Proof.
destruct ;
invert e;
exact eq_refl.
Defined.*)

(*Lemma Kor (A B : Prop) (x : A + B) (e : x = x) : e = eq_refl.
Proof.
destruct x.
invert e.
*)

Lemma Knat (n : nat) (e : n = n) : e = eq_refl.
Proof.
induction n. invert e. reflexivity.
pose (eq_refl n) as H.
change eq_refl with (eq_rect _ (fun x => S n = S x) eq_refl n H).
clearbody H; revert H.
invert e.

pose (fun m => match m as m' return S n = m' -> Type with
 | O => fun e : S n = O => True
 | S m => fun (e : S n = S m) => forall (H : n = m), e = eq_rect n (fun x : nat => S n = S x) eq_refl m H
  end) as diag.
refine (match e as e' in _ = m return diag m e' with eq_refl =>_ end).
intro eq.
apply (eq_rect eq_refl (fun y => eq_refl = eq_rect n (fun x : nat => S n = S x) eq_refl n y) eq_refl).
now symmetry.
Defined.
