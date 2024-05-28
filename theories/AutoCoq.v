Declare ML Module "autocoq-plugin.plugin".

(*
Axiom pos : forall A, (~ A -> A) -> A.
Axiom neg : forall A, (A -> ~ A) -> ~ A.

(*
~A \/ B
A \/ C
~ B
~ C
*)

Goal
  forall A B C
  (H1 : A -> B)
  (H2 : ~ B -> ~ A)
  (H3 : A -> ~ B -> False)
  (H4 : ~ A -> C)
  (H5 : C -> ~ A)
  (H6 : ~ A -> ~ C -> False)
  (H7 : ~ B)
  (H8 : B -> False)
  (H9 : ~ C)
  (H10 : C -> False),
  False.
Proof.
  intros.
  info_auto with nocore. Undo.
  specialize (pos A) as pos_A. specialize (pos B) as pos_B. specialize (pos C) as pos_C.
  specialize (neg A) as neg_A. specialize (neg B) as neg_B. specialize (neg C) as neg_C.
  info_auto with nocore. Undo.
  apply H10. apply H4. apply H2. apply H7.
Qed.

(*
P \/ Q
P \/ ~ Q
~ P \/ Q
~ P \/ ~ Q
*)

Goal
  forall P Q
  (H1 : ~ P -> Q)
  (H2 : P -> ~ Q)
  (H3 : ~ P -> ~ Q -> False)
  (H4 : ~ P -> ~ Q)
  (H5 : Q -> P)
  (H6 : ~ P -> Q -> False)
  (H7 : P -> Q)
  (H8 : ~ Q -> ~ P)
  (H9 : P -> ~ Q -> False)
  (H10 : P -> ~ Q)
  (H11 : Q -> ~ P)
  (H12 : P -> Q -> False),
  False.
Proof.
  intros.
  info_auto with nocore. Undo.
  specialize (pos P) as pos_P. specialize (pos Q) as pos_Q.
  info_eauto 8 with nocore. Undo. Undo. Undo.
  specialize (neg P) as neg_P. specialize (neg Q) as neg_Q.
  info_eauto 8 with nocore. Undo. Undo. Undo.
  specialize (pos P) as pos_P. specialize (pos Q) as pos_Q.
  specialize (neg P) as neg_P. specialize (neg Q) as neg_Q.
  info_auto with nocore. Undo.
  info_eauto 8 with nocore. Undo.
  info_eauto 100 with nocore. Undo.
  apply H12.
  - apply pos_P; intros G1. apply H5. apply H1. apply G1.
  - apply pos_Q; intros G2. apply H1. apply H8. apply G2.
Qed.

Goal forall A, (forall x y : A, x = y) -> (~ exists x y : A, x <> y).
Proof.
  intuition auto. repeat destruct H0. auto.
Qed.

Print eq.
Check @eq.
Check @eq_refl.
Check eq_ind.
Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : eq A x x.
*)
