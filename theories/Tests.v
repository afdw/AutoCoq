Declare ML Module "autocoq-plugin.plugin".

Goal forall A B, (A /\ B) <-> (B /\ A).
Proof.
  ac_isabelle.
Admitted.

Goal forall P, P \/ ~ P.
Proof.
  ac_isabelle.
Admitted.

Goal exists x : Prop, True.
Proof.
  ac_isabelle.
Admitted.

Goal forall A (x : A), exists y, y = x.
Proof.
  ac_isabelle.
Admitted.

Goal forall (A : Type) (z: A) A (x: A), exists y, y = x.
Proof.
  ac_isabelle.
Admitted.

Goal forall A, exists (y : A), True.
Proof.
  ac_isabelle.
Admitted.

Goal forall X Y (f : X -> Y), exists x1 x2, f x1 = f x2.
Proof.
  ac_isabelle.
Admitted.

Goal (fun (_ : Prop) => True) <> (fun (abc : Prop) => False).
Proof.
  ac_isabelle.
Admitted.
