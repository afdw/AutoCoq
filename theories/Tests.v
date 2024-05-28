Require Import AutoCoq.

Require Coq.Lists.List.
Import List.ListNotations.

Require Import Coq.ZArith.ZArith.
Undelimit Scope Z_scope.
Delimit Scope Z_scope with Int.
Open Scope Z_scope.
Notation "'int'" := Z.

(*
Goal forall A (x : A), Some x <> None.
Proof.
  ac_isabelle.
Admitted.

Inductive finite_powerset {T} (A : T -> Prop) : (T -> Prop) -> Prop :=
  | finite_powerset_empty : finite_powerset A (fun _ => False)
  | finite_powerset_insert : forall a B, A a -> finite_powerset A B -> finite_powerset A (fun x => x = a \/ B x).

Check @finite_powerset.

Goal forall T (A : T -> Prop) B, finite_powerset A B.
Proof.
  ac_isabelle.
*)

Goal forall A B, (A /\ B) <-> (B /\ A).
Proof.
  ac_isabelle.
Admitted.

Goal forall P, P \/ ~ P.
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

Goal forall (A : Type) (x: A), forall (A : Type) (y: A), (exists z, z = x) /\ (exists z, z = y).
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

Goal forall a b, (true && (negb a) && b = b && (negb a) || false)%bool.
Proof.
  ac_isabelle.
Admitted.

Goal -1 + 2 < 3 * 4.
Proof.
  ac_isabelle.
Admitted.

Goal (Z.le : int -> int -> Prop) <> Z.ge.
Proof.
  ac_isabelle.
Admitted.
