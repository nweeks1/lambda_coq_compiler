Print nat.
Print Nat.pred.


Inductive de_brujin : Set :=
  | Var : nat -> de_brujin
  | Abstraction : de_brujin -> de_brujin
  | App : de_brujin -> de_brujin -> de_brujin
.

(**
 On a ClosedN n u ssi toutes les variables libres de u sont < n.
 Ainsi, u est clos ssi closedN 0 u.
**)

Inductive ClosedN : nat -> de_brujin -> Prop :=
  | ClosedN_Var : forall n m : nat, m < n -> ClosedN n (Var m)
  | ClosedN_App : forall (n : nat) (u : de_brujin) (v : de_brujin),
              ClosedN n u -> ClosedN n v -> ClosedN n (App u v)
  | ClosedN_Abstraction : forall (n : nat) (u : de_brujin),
              ClosedN (S n) u -> ClosedN n (Abstraction u)
.


Theorem ClosedIncreasing : forall (n : nat) (u : de_brujin), ClosedN n u -> ClosedN (S n) u.
Proof.
  
  intro.
  intro.
  generalize n.
  clear n.
  
  induction u.
  
  + intros.
    inversion H.
    apply ClosedN_Var.
    apply le_S.
    trivial.
  
  + intros.
    inversion H.
    apply ClosedN_Abstraction.
    apply IHu. trivial.
    
  + intros.
    apply ClosedN_App.
    inversion H. apply IHu1. trivial. 
    inversion H. apply IHu2. trivial.
Qed.


Definition Closed : de_brujin -> Prop := ClosedN 0.

Lemma Closed_lt : forall (n : nat) (u : de_brujin), Closed u -> ClosedN n u.
Proof.
  intro.
  induction n.
  intros. trivial.
  intros. apply ClosedIncreasing. apply IHn. trivial.
Qed.

(** Incrémente variables libres de u avec indice >= n **)
Fixpoint increment_greater (n : nat) (u : de_brujin) : de_brujin :=
  match u with
    | Var i => if Nat.ltb i n then Var i else Var (S i)
    | App v w => App (increment_greater n v) (increment_greater n w)
    | Abstraction v => Abstraction (increment_greater (S n) v)
  end
.

Definition increment_free_vars := increment_greater 0.

Fixpoint subst (n : nat) (t : de_brujin) (u : de_brujin) :=
  match u with
    | Var i => 
        if Nat.eqb i n then t else u
    | App v w => 
        App (subst n t v) (subst n t w)
    | Abstraction v =>
        Abstraction (subst (S n) (increment_free_vars t) v)
  end
.

Lemma not_lt_0 : forall (n : nat), ~(n < 0).
  intro.
  intro.
  inversion H.
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


Lemma ClosedN_subst : forall (n : nat) (t : de_brujin) (u : de_brujin),
  ClosedN n u -> subst n t u = u.
Proof.
  intro. intro. intro.
  generalize n t.
  induction u.

  + intros.
    inversion H.
    simpl.
    case_eq (Nat.eqb n0 n1).
    clear H n2 m H1 H0.
    rewrite (not_lt_eq n0 n1).
    intro. inversion H.
    trivial.
    intro. trivial.

  + intros.
    simpl.
    inversion H.
    rewrite IHu.
    trivial. trivial.

  + intros.
    simpl.
    rewrite IHu1.
    rewrite IHu2.
    trivial. 
    inversion H.  trivial.  inversion H. trivial.
Qed.


Lemma Closed_subst : forall (n : nat) (t : de_brujin) (u : de_brujin),
  Closed u -> subst n t u = u.
Proof.
  intros.
  apply ClosedN_subst.
  apply Closed_lt.
  trivial.
Qed.
