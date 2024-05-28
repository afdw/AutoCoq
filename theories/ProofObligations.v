Require Coq.Lists.List.
Import List.ListNotations.

Open Scope list_scope.

Require Import Coq.ZArith.ZArith.
Undelimit Scope Z_scope.
Delimit Scope Z_scope with Int.
Notation "'int'" := Z.

Axiom classicT : forall (P : Prop), {P} + {~ P}.

Notation "'If' P 'then' v1 'else' v2" :=
  (if (classicT P) then v1 else v2)
  (at level 200, right associativity) : type_scope.

(*
1 LIST FORALL PREDICATE
1.1 Definition of LibList.Forall
*)

Inductive Forall {A} (P : A -> Prop) : list A -> Prop :=
  | Forall_nil :
    Forall P nil
  | Forall_cons :
    forall l x,
    P x ->
    Forall P l ->
    Forall P (x :: l).

Lemma Forall_nil_eq :
  forall {A} (P : A -> Prop),
  Forall P nil = True.
Proof.
Admitted.

Lemma Forall_one_eq :
  forall {A} (P : A -> Prop) x,
  Forall P (x :: nil) = P x.
Proof.
Admitted.

Lemma Forall_app_eq :
  forall {A} (P : A -> Prop) l1 l2,
  Forall P (l1 ++ l2) = (Forall P l1 /\ Forall P l2).
Proof.
Admitted.

Lemma Forall_rev_eq :
  forall {A} (P : A -> Prop) l,
  Forall P (List.rev l) = Forall P l.
Proof.
Admitted.

(*
1.2 Example goals for Forall
*)

Lemma test_Forall_intro :
  forall {A} P l1 l2 l3 (x : A),
  Forall P l1 ->
  P x ->
  Forall P l2 ->
  Forall P l3 ->
  Forall P (l1 ++ x :: l2 ++ l3).
Proof.
Admitted.

Lemma test_Forall_inv_list :
  forall {A} P l1 l2 l3 (x : A),
  Forall P (l1 ++ x :: l2 ++ l3) ->
  Forall P l2.
Proof.
Admitted.

Lemma test_Forall_inv_one :
  forall {A} P l1 l2 l3 (x : A),
  Forall P (l1 ++ x :: l2 ++ l3) ->
  P x.
Proof.
Admitted.

Lemma test_Forall_inv_intro :
  forall {A} P l1 l2 l3 (x y : A),
  P x ->
  Forall P (l1 ++ y :: l2) ->
  Forall P l3 ->
  Forall P (l1 ++ x :: l2 ++ y :: l3).
Proof.
Admitted.

Lemma test_Forall_inst_intro :
  forall {A} (R : A -> A -> Prop) l1 l2 x a,
  Forall (R a) l1 ->
  R a x ->
  Forall (R a) l2 ->
  Forall (R a) (l1 ++ x :: l2).
Proof.
Admitted.

Lemma test_Forall_inst_inv :
  forall {A} (R : A -> A -> Prop) l1 l2 x a,
  Forall (R a) (l1 ++ x :: l2) ->
  R a x.
Proof.
Admitted.

Lemma test_Forall_inst_eta :
  forall {A} (R : A -> A -> Prop) (l1 l2 l3 : list A) x a,
  R a x ->
  Forall (fun b => R a b) l1 ->
  Forall (fun b => R a b) (x :: l1).
Proof.
Admitted.

(*
1.3 Membership predicate
*)

Inductive mem {A} (x : A) : list A -> Prop :=
  | mem_here :
    forall l,
    mem x (x :: l)
  | mem_next :
    forall y l,
    mem x l ->
    mem x (y :: l).

Lemma Forall_eq_forall_mem :
  forall {A} P (l : list A),
  Forall P l = (forall x, mem x l -> P x).
Proof.
Admitted.

Lemma Forall_mem_inv :
  forall {A} P l (x : A),
  Forall P l ->
  mem x l ->
  P x.
Proof.
Admitted.

Lemma test_Forall_intro_diverse :
  forall {A} P l1 l2 (x : A),
  Forall P l1 ->
  P x ->
  (forall y, mem y l2 -> P y) ->
  Forall P (l1 ++ x :: l2).
Proof.
Admitted.

Lemma test_Forall_inv_mem :
  forall {A} P l1 l2 l3 (x : A),
  mem x l2 ->
  Forall P (l1 ++ l2 ++ l3) ->
  P x.
Proof.
Admitted.

(*
1.4 Forall on lists of lists
*)

Lemma test_Forall_nested_inv_mem :
  forall {A} P (K : list (list A)) (L : list A) x,
  mem x L ->
  mem L K ->
  Forall (Forall P) K ->
  P x.
Proof.
Admitted.

Lemma test_Forall_nested_intro_mem :
  forall {A} P (K : list (list A)),
  (forall x L, mem L K -> mem x L -> P x) ->
  Forall (Forall P) K.
Proof.
Admitted.

(*
1.5 Predicate weakening
*)

Definition pred_incl {A : Type} (P Q : A -> Prop) :=
  forall x, P x -> Q x.

Lemma Forall_pred_incl :
  forall {A} (P Q : A -> Prop) l,
  Forall P l ->
  pred_incl P Q ->
  Forall Q l.
Proof.
Admitted.

Lemma pred_incl_refl :
  forall {A} (P : A -> Prop),
  pred_incl P P.
Proof.
Admitted.

Lemma pred_incl_trans :
  forall A (Q P R : A -> Prop),
  pred_incl P Q ->
  pred_incl Q R ->
  pred_incl P R.
Proof.
Admitted.

Parameter length_le : forall {A} (n : nat) (L : list A), Prop.

Parameter pred_incl_length_le :
  forall {A} (n m : nat),
  n <= m ->
  pred_incl (@length_le A n) (@length_le A m).

Parameter pred_incl_length_le' :
  forall {A} (n m : nat) (L : list A),
  n <= m ->
  length_le n L ->
  length_le m L.

Lemma test_Forall_pred_incl_app :
  forall {A} P Q (l1 l2 : list A),
  Forall P l1 ->
  Forall Q l2 ->
  pred_incl P Q ->
  Forall Q (l1 ++ l2).
Proof.
Admitted.

Lemma test_Forall_pred_incl_trans_app :
  forall {A} P Q R (l1 l2 : list A),
  Forall P l1 ->
  Forall Q l2 ->
  pred_incl P Q ->
  pred_incl Q R ->
  Forall R (l1 ++ l2).
Proof.
Admitted.

(*
1.6 Weakening on lists of lists
*)

Lemma test_Forall_length_le_intro :
  forall {A} n1 n2 n3 m (L : list A) (K1 K3 : list (list A)),
  n1 <= m ->
  n2 <= m ->
  n3 <= m ->
  Forall (length_le n1) K1 ->
  length_le n2 L ->
  Forall (length_le n3) K3 ->
  Forall (length_le m) (K1 ++ L :: K3).
Proof.
Admitted.

Lemma test_Forall_length_le_inv :
  forall {A} n m (L : list A) (K1 K3 : list (list A)),
  Forall (length_le n) (K1 ++ L :: K3) ->
  n <= m ->
  length_le m L.
Proof.
Admitted.

(*
2 TRANSITIVE CLOSURE OF BINARY RELATIONS
2.1 Transitive Closure
*)

Definition binary (A : Type) := A -> A -> Prop.

Parameter rtclosure : forall {A} (R : binary A), binary A.

Parameter rtclosure_once :
  forall {A} (R : binary A) x y,
  R x y ->
  rtclosure R x y.

Parameter rtclosure_refl :
  forall {A} (R : binary A) x,
  rtclosure R x x.

Parameter rtclosure_trans :
  forall {A} (R : binary A) y x z,
  rtclosure R x y ->
  rtclosure R y z ->
  rtclosure R x z.

Parameter rtclosure_cases :
  forall {A} (R : binary A) x z,
  R x z \/
  x = z \/
  (exists y, rtclosure R x y /\ rtclosure R y z).

Lemma test_rtclosure_r :
  forall {A} (R : binary A) y x z,
  rtclosure R x y ->
  R y z ->
  rtclosure R x z.
Proof.
Admitted.

Lemma test_rtclosure_r_provable_eq :
  forall {A} (R : binary A) P y1 y2 x z,
  (forall a b, P a -> P b -> a = b) ->
  rtclosure R x y1 ->
  P y1 ->
  P y2 ->
  R y2 z ->
  rtclosure R x z.
Proof.
Admitted.

Lemma test_rtclosure_r_arith_rel :
  forall (x y z n m : nat),
  let R := (fun a b => b - a <= n) in
  rtclosure R x y ->
  z - y <= m ->
  m <= n ->
  rtclosure R x z.
Proof.
Admitted.

Lemma test_rtclosure_trans_arith_eq :
  forall R (x z y1 y2 : nat),
  rtclosure R x (y1 + y2) ->
  rtclosure R (y2 + y1) z ->
  rtclosure R x z.
Proof.
Admitted.

(*
2.2 Relation inclusion
*)

Definition rel_incl {A B} (R1 R2 : A -> B -> Prop) : Prop :=
  forall x y, R1 x y -> R2 x y.

Lemma rel_incl_rtclosure :
  forall {A} (R1 R2 : binary A),
  rel_incl R1 R2 ->
  rel_incl (rtclosure R1) (rtclosure R2).
Proof.
Admitted.

Lemma test_rel_incl_rtclosure :
  forall {A} (R1 R2 : binary A) x y,
  (forall a b, R1 a b -> R2 a b) ->
  rtclosure R1 x y ->
  rtclosure R2 x y.
Proof.
Admitted.

Lemma test_rel_incl_rtclosure_bounded_diff :
  forall (x y n m : nat),
  n <= m ->
  rtclosure (fun a b => b - a <= n) x y ->
  rtclosure (fun a b => b - a <= m) x y.
Proof.
Admitted.

(*
3 LIST FILTERING
*)

Lemma mem_nil_eq :
  forall {A} (x : A),
  mem x nil = False.
Proof.
Admitted.

Lemma mem_cons_eq :
  forall {A} (x y : A) l,
  mem x (y :: l) = (x = y \/ mem x l).
Proof.
Admitted.

Parameter fold_right : forall {A B} (f : A -> B -> B) (i : B) (l : list A), B.

Parameter fold_right_nil :
  forall {A B} (f : A -> B -> B) i,
  fold_right f i nil = i.

Parameter fold_right_cons :
  forall {A B} (f : A -> B -> B) i x l,
  fold_right f i (x :: l) = f x (fold_right f i l).

Definition filter {A} (P : A -> Prop) (l : list A) : list A :=
  fold_right (fun x acc => If P x then x :: acc else acc) (@nil A) l.

Lemma filter_nil :
  forall {A} (P : A -> Prop),
  filter P nil = nil.
Proof.
Admitted.

Lemma filter_cons :
  forall {A} (x : A) l P,
  filter P (x :: l) = (If P x then x :: filter P l else filter P l).
Proof.
Admitted.

Lemma mem_filter_eq :
  forall {A} (x : A) P l,
  mem x (filter P l) = (mem x l /\ P x).
Proof.
Admitted.

Lemma Forall_filter_same :
  forall {A} P (l : list A),
  Forall P (filter P l).
Proof.
Admitted.

Lemma filter_eq_self_of_mem_implies_P :
  forall {A} (l : list A) P,
  (forall x, mem x l -> P x) ->
  filter P l = l.
Proof.
Admitted.

Lemma filter_eq_self_of_Forall :
  forall {A} (l : list A) P,
  Forall P l ->
  filter P l = l.
Proof.
Admitted.

Lemma Forall_filter_pred_incl :
  forall {A} P Q (l : list A),
  pred_incl P Q ->
  Forall Q (filter P l).
Proof.
Admitted.

Lemma length_filter :
  forall {A} (l : list A) P,
  length (filter P l) <= length l.
Proof.
Admitted.

Lemma test_mem_filter_eq_arith :
  forall (l : list int) d n m,
  mem n (filter (fun x => x <= m) l)%Int ->
  (d >= 0)%Int ->
  (n <= m + d)%Int.
Proof.
Admitted.

Lemma test_Forall_filter_pred_incl_arith :
  forall n m (l : list int),
  (n <= m)%Int ->
  Forall (fun x => x <= m)%Int (filter (fun x => x <= n)%Int l).
Proof.
Admitted.

(*
4 PREDICATES ABOUT SORTING
*)

Parameter sorted : forall {A} (R : binary A) (L : list A), Prop.

Parameter sorted_nil :
  forall {A} (R : binary A),
  sorted R nil.

Parameter sorted_one :
  forall {A} (R : binary A) x,
  sorted R (x :: nil).

Parameter sorted_two :
  forall {A} (R : binary A) L x y,
  sorted R (y :: L) ->
  R x y ->
  sorted R (x :: y :: L).

Parameter sorted_cases :
  forall {A} (R : binary A) L,
  sorted R L ->
  L = nil \/
  (exists x, L = x :: nil) \/
  (exists x y L', L = x :: y :: L' /\ sorted R (y :: L') /\ R x y).

Definition trans {A} (R : binary A) : Prop :=
  forall y x z, R x y -> R y z -> R x z.

Definition head_le {A} (R : binary A) (x : A) (L : list A) : Prop :=
  match L with
  | nil => True
  | y :: _ => R x y
  end.

Lemma test_head_le_trans :
  forall {A} (R : binary A) x y L,
  trans R ->
  head_le R x L ->
  R y x ->
  head_le R y L.
Proof.
Admitted.

Lemma test_sorted_cons2_inv_cons3 :
  forall {A} (R : binary A) x1 x2 x3 L,
  sorted R (x1 :: x3 :: L) ->
  R x1 x2 ->
  R x2 x3 ->
  sorted R (x1 :: x2 :: x3 :: L).
Proof.
Admitted.

Lemma test_sorted_cons_eq :
  forall {A} (R : binary A) x L,
  sorted R (x :: L) = (head_le R x L /\ sorted R L).
Proof.
Admitted.

Lemma test_Forall_le_of_sorted_head_le :
  forall {A} (R : binary A) x L,
  trans R ->
  sorted R L ->
  head_le R x L ->
  Forall (R x) L.
Proof.
Admitted.

Lemma test_sorted_cons2_inv_cons3_int_with_arith :
  forall x1 x2 x3 d L,
  sorted Z.le (x1 :: x3 :: L) ->
  (x1 + d <= x2)%Int ->
  (x2 + d <= x3)%Int ->
  (d >= 0)%Int ->
  sorted Z.le (x1 :: x2 :: x3 :: L).
Proof.
Admitted.

(*
5 LOGICAL EQUIVALENCES
*)

Lemma not_forall_eq :
  forall {A} (P : A -> Prop),
  (~ (forall x, P x)) = (exists x, ~ P x).
Proof.
Admitted.

Lemma test_not_forall_eq :
  forall (P Q : nat -> Prop),
  ~ (forall x, Q x) ->
  (forall x, ~ Q x -> P x) ->
  exists a, P a.
Proof.
Admitted.

Lemma test_not_forall_eq_arith :
  forall (P : nat -> Prop) (n : nat),
  ~ (forall x, x >= n) ->
  (forall x, x < n -> P x) ->
  exists a, P a.
Proof.
Admitted.

Lemma not_not_eq :
  forall P,
  (~ ~ P) = P.
Proof.
Admitted.

Lemma not_and_eq :
  forall P Q,
  (~ (P /\ Q)) = (~ P \/ ~ Q).
Proof.
Admitted.

Lemma not_or_eq :
  forall P Q,
  (~ (P \/ Q)) = (~ P /\ ~ Q).
Proof.
Admitted.

Lemma test_tauto_exploit :
  forall (P Q : nat -> Prop) (n : nat),
  ~ (P n \/ (forall x, ~ Q x)) ->
  (forall x, Q x -> P n) ->
  False.
Proof.
Admitted.

Lemma test_tauto_exploit_arith :
  forall (P : int -> Prop) (n d : int),
  ~ (P n \/ (forall x, x < n)%Int) ->
  (d >= 0)%Int ->
  (forall x, x >= n - d -> P n)%Int ->
  False.
Proof.
Admitted.
