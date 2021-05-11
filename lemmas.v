Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Logic.
Require Import Psatz.
Require Import Bool.
Require Import definitions.


Lemma not_lt_0 : forall (n : nat), ~(n < 0).
  lia.
Qed.

Lemma not_lt_eq : forall (n : nat) (m : nat), n < m -> Nat.eqb n m = false.
Proof.
  intro. induction n.
  intros.
  simpl.
  inversion H.
  trivial. trivial.
  intros.
  destruct m.
  trivial.
  simpl.
  apply IHn.
  apply le_S_n. trivial.
Qed.


Lemma minus_0_le : forall (n : nat) (m : nat), n-m = 0 -> n <= m.
Proof.
  lia.
Qed.

Lemma lt_add : forall (i : nat) (n : nat) (m : nat), i+n < i+m -> n < m.
Proof.
  lia.
Qed.

Lemma sub_0 : forall n, n-0 = n.
Proof.
  lia.
Qed.


Lemma not_le : forall n m, ~ (n < m) -> m <= n.
Proof.
  lia.
Qed.
Lemma NotLt : forall n m, ~(n <= m) -> m < n.
  lia.
Qed.

Lemma sub_ineq : forall a b c,
  a < b + c -> a >= b -> a - b < c.
Proof.
  lia.
Qed.
