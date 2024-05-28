Require Import AutoCoq.
From Hammer Require Import Tactics Hammer.

From TLC Require Import LibTactics LibLogic LibListZ LibMultiset.

Require Import Coq.ZArith.ZArith.
Undelimit Scope Z_scope.
Delimit Scope Z_scope with Int.
Open Scope Z_scope.
Notation "'int'" := Z.

(* ********************************************************************** *)
(** ** Types of elements *)

(** For simplicity, assume the priority queue to store integer values.
    It is not hard to generalize everything to any ordered type. *)

Notation "'elem'" := (int).
Notation "'elems'" := (multiset elem).

(* ******************************************************* *)
(** ** Data structure and definitions *)

(** Functional representation of a node in a (nonempty) pairing heap *)

Inductive node : Type :=
  | Node : elem -> list node -> node.

Instance Inhab_node : Inhab node.
Proof using. applys Inhab_of_val (Node arbitrary nil). Qed.

(** Functional representation of a possibly-empty pairing heap *)

Definition heap := option node.

Instance Inhab_heap : Inhab heap.
Proof using. applys Inhab_of_val (@None node). Qed.

(** Auxiliary definition for specifications *)

Definition min_of (E:elems) (x:elem) : Prop :=
  x \in E /\ forall_ y \in E, x <= y.

(** Auxiliary definition for stating invariants follow. *)

(** [is_ge x] is a predicate that characterizes items no less than [x] *)

Definition is_ge (x y:elem) : Prop :=
  x <= y.

(** [list_union Es] computes the iterated union of the multisets in the list [Es] *)

Definition list_union (Es:list elems) : elems :=
  LibList.fold_right union \{} Es.

(** [inv n E] relates a tree node [n] with the multiset [E] made of
    the items that the tree contains *)

Inductive inv : node -> elems -> Prop :=
  | inv_Node : forall x ns Es E,
      Forall2 inv ns Es ->
      Forall (foreach (is_ge x)) Es ->
      E = \{x} \u (list_union Es) ->
      inv (Node x ns) E.


(* ******************************************************* *)
(** ** Lemmas and tactics *)

(** Implicit Types *)

Implicit Types n : node.
Implicit Types x y : elem.
Implicit Types h : heap.
Implicit Types hs : list node.
Implicit Types E : elems.
Implicit Types Es : list elems.

(** Normalization lemmas for [list_union] *)

Lemma list_union_nil :
  list_union (@nil elems) = \{}.
Proof using. auto. Qed.

Lemma list_union_cons : forall E Es,
  list_union (E::Es) = E \u list_union Es.
Proof using. auto. Qed.

(** Hints *)

Hint Rewrite list_union_nil list_union_cons : rew_listx.
Hint Rewrite (@union_empty_r elems _ _ _) (@union_empty_l elems _ _ _) : rew_listx.
Hint Extern 1 (_ < _) => simpl; lia : core.
Hint Extern 1 (_ <= _) => simpl; lia : core.
Hint Extern 1 (_ = _ :> multiset _) => rew_listx; multiset_eq : core.
Hint Extern 1 (_ \in _) => multiset_in : core.
Hint Constructors Forall Forall2 list_sub : core.
Hint Unfold is_ge : core.

(** Lemmas to manipulate the invariant [Forall (foreach (is_ge x)) Es] *)

Lemma Forall_foreach_is_ge_inv : forall x y Es,
  Forall (foreach (is_ge x)) Es ->
  y \in list_union Es ->
  x <= y.
Proof using.
  introv M Hy. unfolds list_union. induction M; rew_listx in *.
  { multiset_in Hy. }
  { multiset_in Hy. { applys* H. } { applys* IHM. } }
Qed.

Lemma foreach_list_union : forall P Es,
  Forall (foreach P) Es ->
  foreach P (list_union Es).
Proof using.
  introv M. induction M.
  { applys foreach_empty. }
  { unfold list_union; rew_listx. applys* foreach_union. }
Qed.

(** Key auxiliary lemmas for the verification proofs
    (both for the functional version and the imperative version) *)

Lemma inv_not_empty : forall n E,
  inv n E ->
  E <> \{}.
Proof using. introv I. inverts I. multiset_inv. Qed.

Lemma merge_lemma : forall x1 x2 ns1 ns2 Es1 Es2,
  Forall2 inv ns1 Es1 ->
  Forall2 inv ns2 Es2 ->
  Forall (foreach (is_ge x2)) Es1 ->
  Forall (foreach (is_ge x1)) Es2 ->
  x1 <= x2 ->
  inv (Node x1 (Node x2 ns1 :: ns2)) ('{x1} \u '{x2} \u list_union Es1 \u list_union Es2).
Proof using.
  introv Is1 Is2 Ks1 Ks2 L. applys_eq inv_Node. constructor.
  { applys* inv_Node. }
  { eauto. }
  { constructors.
    { applys foreach_union.
      { applys* foreach_single. }
      { applys* foreach_list_union. applys Forall_pred_incl Ks1.
        { intros x Hx. applys* foreach_weaken. { intros y Hy. unfolds* is_ge. } } } }
    { eauto. } }
  { autos*. }
Qed.

Lemma pop_min_lemma : forall x Es,
  Forall (foreach (is_ge x)) Es ->
  min_of (\{x} \u list_union Es) x.
Proof.
  introv M. split.
  { auto. }
  { intros y Hy. multiset_in Hy.
    { auto. } { applys* Forall_foreach_is_ge_inv Es. } }
Qed.
