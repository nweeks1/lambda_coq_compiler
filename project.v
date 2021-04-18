Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Bool.
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

Print List.nth.
Print list.
Print Nat.

Fixpoint parallel_subst (i : nat) (liU : list de_brujin) (u : de_brujin) : de_brujin :=
  match u with
    | Var j => 
      if (andb (Nat.leb i j) (Nat.ltb j (i + List.length liU))) then
       List.nth (j-i) liU (Var 0) 
       else Var j
    | App v w => App (parallel_subst i liU v) (parallel_subst i liU w)
    | Abstraction v => Abstraction (parallel_subst (S i) (List.map increment_free_vars liU) v)
  end
.

Theorem subst_empty_trivial : forall (i : nat) (u : de_brujin),
    parallel_subst i nil u = u.
Proof.
  intros.
  generalize i. clear i.
  induction u.
  
  + intro.
    simpl.
    rewrite plus_0_r.
    case_eq (i <=? n).
    intro.
    case_eq (n <? i).
    intro.
    apply (proj1 (Nat.leb_le i n)) in H.
    apply (proj1 (Nat.ltb_lt n i)) in H0.
    exfalso.
    apply (le_not_lt i n H).
    trivial.
    simpl. trivial.
    simpl. trivial.

  + simpl.
    intro.
    rewrite (IHu (S i)).
    trivial.
  + intro.
    simpl.
    rewrite IHu1. rewrite IHu2.
    trivial.
Qed.

Theorem ClosedN_subst_trivial : forall (i : nat) (liU : list de_brujin) (u : de_brujin),
  ClosedN i u -> parallel_subst i liU u = u.
Proof.
  intro. intro. intro.
  generalize i liU.
  clear i liU.
  induction u.

  + intros.
    inversion H.
    simpl.
    case_eq (i <=? n).
    intro.
    apply (proj1 (Nat.leb_le i n)) in H3.
    exfalso. apply (le_not_lt i n H3). trivial.
    trivial.

  + intros.
    inversion H.
    simpl.
    rewrite IHu. trivial. trivial.
  
  + intros.
    simpl. inversion H.
    rewrite IHu1. rewrite IHu2. trivial. trivial. trivial.
Qed.

Print List.Forall.


Lemma minus_0_le : forall (n : nat) (m : nat), n-m = 0 -> n <= m.
Proof.
  intro.
  induction n.
  simpl. intros. induction m. trivial. apply le_S. trivial.
  intro. induction m.
  intro.
  inversion H.
  intro.
  inversion H.
  apply le_n_S. apply IHn. trivial.
Qed.

Lemma lt_add : forall (i : nat) (n : nat) (m : nat), i+n < i+m -> n < m.
Proof.
  intro.
  induction i.
  intros.
  simpl in H. trivial.
  intros.
  rewrite Nat.add_succ_l in H.
  rewrite Nat.add_succ_l in H.
  apply lt_S_n in H.
  apply IHi. trivial.
Qed.


Theorem Subst_composite : forall (i : nat) (u0 : de_brujin) (q : list de_brujin) (u : de_brujin),
  List.Forall (ClosedN i) q -> parallel_subst i (u0 :: q) u = subst i u0 (parallel_subst (S i) q u).
Proof.
  intro. intro. intro. intro.
  generalize i u0 q. clear i u0 q.
  
  induction u.
  
  + intros.
    simpl.
    case_eq (i <=? n).
    intro. simpl. apply (proj1 (Nat.leb_le i n)) in H0.
    case_eq (n <? i + S (length q)).
    intro. simpl.
    apply (proj1 (Nat.ltb_lt n (i + S (length q)))) in H1.
    case_eq (n-i).
    intro. destruct n.
    simpl. destruct i. trivial.
    inversion H0.
    
    case_eq (i <=? n).
    intro. apply (proj1 (Nat.leb_le i n)) in H3.
    simpl.
    apply minus_0_le in H2.
    apply (le_trans (S n) i n H2) in H3.
    exfalso.
    apply (le_not_lt n n).
    trivial. trivial. simpl. intro.
    clear H3.
    apply le_plus_minus in H0.
    rewrite H2 in H0. rewrite Nat.add_0_r in H0.
    rewrite <- H0.
    rewrite (proj2 (Nat.eqb_eq n n)).
    trivial. trivial.
    
    intros.
    apply le_plus_minus in H0. rewrite H2 in H0.
    rewrite H0.
    case_eq (i + S n0).
    simpl. intro.

    rewrite (Nat.add_succ_r i n0) in H3.
    inversion H3.

    intros.
    rewrite (Nat.add_succ_r) in H3.
    inversion H3. clear H3.
    rewrite (proj2 (Nat.leb_le i (i + n0))).
    simpl.
    rewrite (Nat.add_succ_r) in H0.
    rewrite <- H0.
    rewrite (Nat.add_succ_r) in H1.
    rewrite (proj2 (Nat.ltb_lt n (S (i + length q)))).

    rewrite minus_plus.
    trivial.
    rewrite (ClosedN_subst i). trivial.
    apply (proj1 (List.Forall_nth (ClosedN i) q)).
    trivial.
    rewrite H0 in H1.
    apply lt_S_n in H1.
    apply (lt_add i).
    trivial.
    trivial.
    apply le_plus_l.

    intro.
    rewrite Nat.add_succ_r in H1.
    rewrite H1.
    rewrite andb_false_r.
    simpl.
    case_eq (n =? i).
    intro.
    apply (proj1 (Nat.eqb_eq n i)) in H2.
    rewrite H2 in H1.
    exfalso.
    apply (lt_not_le i (S (i + length q))).

    apply le_n_S.
    apply le_plus_l.
    
    apply (proj2 (not_true_iff_false (i <? S (i + length q)))) in H1.
    apply (proj1 (not_iff_compat (Nat.ltb_lt i (S (i + length q))))) in H1.
    case_eq (Nat.le_gt_cases (S (i + length q)) i).
    intros.
    trivial.
    intros.
    exfalso. apply H1. trivial.
    trivial.
    
    intro.
    simpl.
    apply (proj2 (not_true_iff_false (i <=? n))) in H0.
    apply (proj1 (not_iff_compat (Nat.leb_le i n))) in H0.
    case_eq n.
    simpl. intros.
    rewrite H1 in H0.
    case_eq i.
    intro.
    rewrite H2 in H0. exfalso. apply H0. trivial.
    intros.
    trivial.
    intros.
    simpl.
    case_eq (i <=? n0).
    simpl. intro.
    apply (proj1 (Nat.leb_le i n0)) in H2.
    apply le_S in H2.
    rewrite <- H1 in H2.
    exfalso. apply H0. apply H2.
    simpl.
    intros.
    case_eq i.
    trivial.
    intros.
    case_eq (n0 =? n1).
    intro.
    apply (proj1 (Nat.eqb_eq n0 n1)) in H4.
    apply eq_S in H4.
    rewrite <- H1 in H4.
    rewrite <- H3 in H4.
    exfalso. apply H0.
    rewrite H4. trivial.
    trivial.

  + intros.
    simpl.
    rewrite IHu.
    trivial.
    induction q.
    simpl. trivial.
    
    simpl.
    apply Forall_cons.
    