Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Logic.
Require Import Psatz.
Require Import Bool.

Inductive de_brujin : Type :=
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

Definition Closed : de_brujin -> Prop := ClosedN 0.

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

Fixpoint decrement_vars_greater (n : nat) (u : de_brujin):=
  match u with
    | Var i => if Nat.ltb n i then Var (i-1) else Var i
    | App u v => App (decrement_vars_greater n u) (decrement_vars_greater n v)
    | Abstraction u => Abstraction (decrement_vars_greater (S n) u)
  end.


Inductive Beta : de_brujin -> de_brujin -> Prop :=
  | BetaStep : forall (u : de_brujin) (v : de_brujin), 
    Beta (App (Abstraction u) v ) (decrement_vars_greater 0 (subst 0 (increment_free_vars v) u))
  | BetaAppL : forall (u : de_brujin) (v : de_brujin) (t : de_brujin),
      Beta t u -> Beta (App t v) (App u v)
  | BetaAppR : forall (u : de_brujin) (v : de_brujin) (t : de_brujin),
      Beta t v -> Beta (App u t) (App u v)
  | BetaAbst : forall (u : de_brujin) (v : de_brujin),
      Beta u v -> Beta (Abstraction (increment_free_vars u)) (Abstraction (increment_free_vars v))
.

Inductive BetaS : de_brujin -> de_brujin -> Prop :=
  | BetaSRefl : forall (u : de_brujin),
    BetaS u u
  | BetaSStep : forall (t : de_brujin) (u : de_brujin) (v : de_brujin),
    Beta t u -> BetaS u v -> BetaS t v
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


Lemma Closed_lt : forall (n : nat) (u : de_brujin), Closed u -> ClosedN n u.
Proof.
  intro.
  induction n.
  intros. trivial.
  intros. apply ClosedIncreasing. apply IHn. trivial.
Qed.

Lemma closedN_incrementM : forall (n : nat) (m : nat) (u : de_brujin), 
  ClosedN n u -> ClosedN (S n) (increment_greater m u).
Proof.
  intro. intro. intro.
  generalize n m.
  clear n m.
  induction u.
  intros.
  simpl.
  inversion H.
  clear m0 n1 H1 H0.
  case_eq (n <? m).
  intro.
  apply ClosedN_Var.
  apply lt_S. trivial.
  intro.
  apply ClosedN_Var. apply lt_n_S. trivial.
  
  intros.
  simpl.
  apply ClosedN_Abstraction.
  apply IHu.
  inversion H.
  trivial.
  
  intros.
  simpl.
  apply ClosedN_App.
  inversion H.
  apply IHu1. trivial.
  apply IHu2. inversion H. trivial.
Qed.
  

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

    case_eq (i + S n0)%nat.
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
    apply closedN_incrementM. 
    inversion H.
    trivial.
    apply IHq. 
    inversion H. trivial.

  +  intros.
     simpl.
     rewrite (IHu1).
     rewrite (IHu2).
     trivial.
     trivial. trivial.
Qed.


Theorem BetaSContextL : forall (u : de_brujin) (v : de_brujin) (t : de_brujin),
  BetaS t u -> BetaS (App t v) (App u v).
Proof.
  intros.
  induction H.
  apply BetaSRefl.
  apply (BetaSStep (App t v) (App u v)).
  apply BetaAppL.
  trivial.
  trivial.
Qed.


Theorem BetaSContextR : forall (u : de_brujin) (v : de_brujin) (t : de_brujin),
  BetaS t v -> BetaS (App u t) (App u v).
Proof.
  intros.
  induction H.
  apply BetaSRefl.
  apply (BetaSStep (App u t) (App u u0)).
  apply BetaAppR.
  trivial.
  trivial.
Qed.

Theorem BetaSContextAbst : forall (t : de_brujin) (u : de_brujin),
  BetaS t u -> BetaS (Abstraction (increment_free_vars t)) (Abstraction (increment_free_vars u)).
Proof.
  intros.
  induction H.
  apply BetaSRefl.
  apply (BetaSStep (Abstraction (increment_free_vars t)) (Abstraction (increment_free_vars u))).
  apply BetaAbst.
  trivial.
  trivial.
Qed.

Inductive instruction : Type := 
  | Access : nat -> instruction
  | Grab : instruction
  | Push : code -> instruction
  
with code : Type :=
  | EmptyCode : code
  | ConsCode : instruction -> code -> code.
  
Inductive environment : Type :=
  | EmptyEnv : environment
  | ConsEnv : code -> environment -> environment -> environment
.

Inductive stack : Type :=
  | EmptyStack : stack
  | ConsStack : code -> environment -> stack -> stack
.

Definition state := (code * environment * stack) % type.

Definition stepKrivine (st : state) : option state :=
  match st with
    | (c, env, stk) => 
      match c with
        | EmptyCode => None
        | ConsCode inst nxtCode =>
          match inst with
            | Access 0 =>
              match env with
                | EmptyEnv => None
                | ConsEnv c0 e0 _ => Some (c0, e0, stk)
              end
            | Access (S n) =>
              match env with
                | EmptyEnv => None
                | ConsEnv c0 e0 e' => Some (ConsCode (Access n) EmptyCode, e', stk)
              end
            | Push c' => 
              Some (nxtCode, env, ConsStack c' env stk)
            | Grab => 
              match stk with
                | EmptyStack => None
                | ConsStack c0 e0 nxtStk => Some (nxtCode, ConsEnv c0 e0 env, nxtStk)
              end
          end
      end
  end. 

Fixpoint Comp (u : de_brujin) : code :=
  match u with
    | Abstraction t => ConsCode Grab (Comp t)
    | App t u => ConsCode (Push (Comp u)) (Comp t)
    | Var n => ConsCode (Access n) EmptyCode
  end.

Fixpoint revCompCode (c : code) : option de_brujin :=
  match c with
    | EmptyCode => None
    | ConsCode instr nxtCode =>
      match instr with
        | Access n => Some (Var n)
        | Push c' =>
          match revCompCode c', revCompCode nxtCode with
            | None, _ => None
            | _, None => None
            | Some v, Some u => Some (App u v)
          end
        | Grab  =>
          match revCompCode nxtCode with
            | None => None
            | Some u => Some (Abstraction u)
          end
      end
  end.

Fixpoint revCompEnv (env : environment) : option (list de_brujin) :=
  match env with
    | EmptyEnv => Some []
    | ConsEnv c0 e0 e => 
      match revCompCode c0 with
        | None => None
        | Some u => 
          match revCompEnv e0, revCompEnv e with
            | None, _ => None
            | _, None => None
            | Some substc0, Some substRest =>
              Some ( (parallel_subst 0 substc0 u) :: substRest)
          end
      end
  end.

Fixpoint revCompStack (stk : stack) : option (list de_brujin) :=
  match stk with
    | EmptyStack => Some []
    | ConsStack c0 e0 nxtStk => 
      match revCompCode c0, revCompEnv e0, revCompStack nxtStk with
        | None, _, _ | _, None, _ | _, _, None => None
        | Some u, Some liU, Some liStk => Some ((parallel_subst 0 liU u) :: liStk)
      end
  end.


Definition revCompState (st : state) : option de_brujin :=
  match st with
    | (c, e, stk) => 
      match revCompCode c, revCompEnv e, revCompStack stk with
        | None, _, _ | _, None, _ | _, _, None => None
        | Some u, Some liU, Some liStk =>
         Some (List.fold_left (fun cur nxt => App cur nxt) liStk (parallel_subst 0 liU u))
      end
  end.

Fixpoint length_stack (stk : stack) : nat :=
  match stk with
    | EmptyStack => 0
    | ConsStack c0 e0 nxtStk => 1 + length_stack nxtStk
  end.

Fixpoint length_env (env : environment) : nat :=
  match env with
    | EmptyEnv => 0
    | ConsEnv c0 e0 nxtEnv => 1 + length_env nxtEnv
  end.

Inductive CorrectEnv : environment -> Prop :=
  | CorrectEmptyEnv : CorrectEnv EmptyEnv
  | CorrectConsEnv : forall (c0 : code) (e0 : environment) (nxtEnv : environment),
    CorrectEnv nxtEnv -> (exists u, ClosedN (length_env e0) u /\ Some u = revCompCode c0)
    -> CorrectEnv e0 -> CorrectEnv (ConsEnv c0 e0 nxtEnv).

Inductive CorrectStack : stack -> Prop :=
  | CorrectEmptyStk : CorrectStack EmptyStack
  | CorrectConsStk : forall (c0 : code) (e0 : environment) (nxtStk : stack),
    CorrectStack nxtStk -> CorrectEnv e0
   -> (exists u, ClosedN (length_env e0) u /\ Some u = revCompCode c0)
    -> CorrectStack (ConsStack c0 e0 nxtStk).

Inductive CorrectState : state -> Prop :=
  | CorrectSt : forall (c : code) (env : environment) (stk : stack),
    (exists u, ClosedN (length_env env) u /\ Some u = revCompCode c)
    -> CorrectEnv env -> CorrectStack stk -> CorrectState (c, env, stk).


Lemma CorrectEnvDecomp : forall (env : environment),
  CorrectEnv env -> (exists l, revCompEnv env = Some l).
Proof.
  intro.
  induction env.
  intro.
  simpl.
  exists [].
  trivial.
  intros.
  inversion H.
  clear H0 H1 H2 c0 e0 nxtEnv.
  
  simpl.
  destruct H4.
  destruct H0.
  rewrite <- H1.
  apply IHenv1 in H5.
  destruct H5.
  rewrite H2.
  apply IHenv2 in H3.
  destruct H3.
  rewrite H3.
  exists (parallel_subst 0 x0 x :: x1).
  trivial.
Qed.

Lemma CorrectStackDecomp : forall (stk : stack),
  CorrectStack stk -> (exists l, revCompStack stk = Some l).
Proof.
  intro.
  induction stk.
  intro.
  simpl.
  exists [].
  trivial.
  intro.
  inversion H.
  simpl.
  destruct H5.
  destruct H5.
  rewrite <- H6.
  apply CorrectEnvDecomp in H4.
  destruct H4.
  rewrite H4.
  apply IHstk in H3.
  destruct H3.
  rewrite H3.
  exists (parallel_subst 0 x0 x :: x1).
  trivial.
Qed.
  
Lemma CorrectStateDecomp : forall (st : state), 
CorrectState st ->(exists u, revCompState st = Some u).
Proof.
  intros.
  destruct st.
  destruct p.
  simpl.
  inversion H.
  destruct H3.
  destruct H3.
  rewrite <- H6.
  apply CorrectEnvDecomp in H4.
  apply CorrectStackDecomp in H5.
  destruct H4.
  destruct H5.
  rewrite H4.
  rewrite H5.
  exists (fold_left (fun cur nxt : de_brujin => App cur nxt) x1 (parallel_subst 0 x0 x)).
  trivial.
Qed.
  

Lemma revStackEmpty : forall (stk : stack), revCompStack stk = Some [] -> stk = EmptyStack.
Proof.
  intros.
  induction stk.
  trivial.
  simpl in H.
  case_eq (revCompCode c).
  intros. rewrite H0 in H.
  case_eq (revCompEnv e). intros. rewrite H1 in H.
  case_eq (revCompStack stk).
  intros.
  rewrite H2 in H.
  inversion H.
  intro. rewrite H2 in H. inversion H.
  intro. rewrite H1 in H. inversion H.
  intro.  rewrite H0 in H. inversion H.
Qed.

Lemma revEnvEmpty : forall (env : environment), revCompEnv env = Some [] -> env = EmptyEnv.
Proof.
  intros.
  induction env.
  trivial.
  simpl in H.
  clear IHenv1 IHenv2.
  case_eq (revCompCode c).
  intros.
  rewrite H0 in H.
  case_eq (revCompEnv env1).
  intros. rewrite H1 in H.
  case_eq (revCompEnv env2).
  intros. rewrite H2 in H.
  inversion H.
  intros. rewrite H2 in H. inversion H.
  intros. rewrite H1 in H. inversion H.
  intros. rewrite H0 in H. inversion H.
Qed.


Lemma LengthRevEnv : forall (env : environment) (li : list de_brujin),
  revCompEnv env = Some li -> List.length li = length_env env.
Proof.
  intro.
  induction env.
  intros.
  simpl in H.
  inversion H.
  simpl. trivial.
  
  intros.
  simpl in H.
  case_eq (revCompCode c).
  intros.
  rewrite H0 in H.
  simpl.
  case_eq (revCompEnv env1).
  intros.
  rewrite H1 in H.
  case_eq (revCompEnv env2).
  intros.
  rewrite H2 in H.
  inversion H.
  simpl.
  apply eq_S.
  apply IHenv2.
  trivial.
  intros. rewrite H2 in H. inversion H.
  intros. rewrite H1 in H. inversion H.
  intros. rewrite H0 in H. inversion H.
Qed.

Theorem CompInverse : forall (u : de_brujin), revCompState (Comp u, EmptyEnv, EmptyStack) = Some u.
Proof.
  intro.
  induction u.
  
  + trivial.
  
  + simpl.  
    simpl in IHu.
    destruct (revCompCode (Comp u)).
    rewrite subst_empty_trivial.
    rewrite subst_empty_trivial in IHu.
    inversion IHu.
    trivial.
    inversion IHu.

  + simpl.
    simpl in IHu1.
    simpl in IHu2.
    destruct (revCompCode (Comp u1)).
    rewrite (subst_empty_trivial) in IHu1.
    inversion IHu1.
    destruct (revCompCode (Comp u2)).
    rewrite subst_empty_trivial.
    rewrite subst_empty_trivial in IHu2.
    inversion IHu2.
    trivial.
    inversion IHu2.
    inversion IHu1.
Qed.

Theorem correct_step : forall (cur : state), 
    CorrectState cur -> (exists nxt, stepKrivine cur = Some nxt) 
    -> (exists nxt, stepKrivine cur = Some nxt /\  CorrectState nxt).
Proof.
  intros.
  induction cur.
  induction a.
  rename a into c.
  rename b0 into env.
  rename b into stk.
  
  simpl.
  induction c.
  
  + inversion H.
    inversion H4.
    inversion H7.
    simpl in H9.
    inversion H9.
    
  + induction i.
    
    ++ induction n.
        
       * induction env.
         
         ** inversion H0.
            simpl in H1.
            inversion H1.
         ** exists (c0, env1, stk).
            split.
            trivial.
            apply CorrectSt.
            
            *** inversion H.
                inversion H5.
                trivial.
            *** inversion H.
                inversion H5.
                trivial.
            *** inversion H.
                trivial.
       * induction env.
          
         ** inversion H.
            inversion H4.
            inversion H7.
            simpl in H9.
            inversion H9.
            rewrite H11 in H8.
            simpl in H8.
            inversion H8.
            inversion H13.
         
         ** exists (ConsCode (Access n) EmptyCode, env2, stk).
            split.
            trivial.
            apply CorrectSt.
            
            *** simpl.
                exists (Var n).
                split.
                inversion H.
                inversion H4.
                inversion H7.
                simpl in H9.
                inversion H9.
                rewrite H11 in H8.
                inversion H8.
                simpl in H13.
                apply lt_S_n in H13.
                apply ClosedN_Var.
                trivial.
                trivial.
            *** inversion H.
                inversion H5.
                trivial.
            *** inversion H.
                trivial.
     ++ induction stk.
         
         * clear IHc.
           inversion H0.
           simpl in H1.
           inversion H1.
         
         * exists (c, ConsEnv c0 e env, stk).
           split.
           trivial.
           apply CorrectSt.
           
           ** inversion H.
              inversion H4.
              inversion H7.
              simpl in H9.
              case_eq (revCompCode c).
              
              *** intros.
                  exists d.
                  split.
                  rewrite H10 in H9.
                  inversion H9.
                  rewrite H12 in H8.
                  inversion H8.
                  simpl.
                  trivial.
                  trivial.
              *** intro.
                  rewrite H10 in H9.
                  inversion H9.
          ** clear IHc IHstk.
             inversion H.
             inversion H6.
             apply CorrectConsEnv.
             trivial.
             trivial.
             trivial.
          ** clear IHc IHstk.
              inversion H.
              inversion H6.
              trivial.
     ++ clear IHc.
        exists (c, env, ConsStack c0 env stk).
        split.
        trivial.
        apply CorrectSt.
        
        * inversion H.
          clear H1 H2 H3 c1 env0 stk0.
          destruct H4.
          destruct H1.
          simpl in H2.
          case_eq (revCompCode c0).
          ** intros.
             rewrite H3 in H2.
             case_eq (revCompCode c).
             *** intros.
                 rewrite H4 in H2.
                 exists d0.
                 split.
                 inversion H2.
                 rewrite H8 in H1.
                 inversion H1.
                 trivial.
                 trivial.
             *** intro.
                 rewrite H4 in H2.
                 inversion H2.
          ** intros.
             rewrite H3 in H2.
             inversion H2.
       * inversion H.
         trivial.
       * inversion H.
         clear H1 H2 H3 c1 env0 stk0.
         inversion H4.
         destruct H1.
         simpl in H2.
         case_eq (revCompCode c0).
         ** intros.
            rewrite H3 in H2.
            case_eq (revCompCode c).
            *** intros.
                rewrite H7 in H2.
                inversion H2.
                rewrite H9 in H1.
                inversion H1.
                apply CorrectConsStk.
                trivial.
                trivial.
                exists d.
                split.
                trivial.
                rewrite H3.
                trivial.
            *** intro.
                rewrite H7 in H2.
                inversion H2.
        ** intro.
           rewrite H3 in H2.
          inversion H2.
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
Lemma inc_dec_single_n : forall (n : nat) u, decrement_vars_greater n (increment_greater n u)= u.
Proof.
  intro. intro.
  generalize n.
  clear n.
  induction u.
  
  + intros.
    simpl.
    case_eq (n <? n0).
    intro.
    apply Nat.ltb_lt in H.
    simpl.
    case_eq (n0 <? n).
    intro.
    apply Nat.ltb_lt in H0.
    apply lt_asym in H0.
    exfalso. apply H0. trivial.
    trivial.
    intro.
    simpl.
    case_eq (n0 <? S n).
    intro.
    rewrite <- minus_n_O.
    trivial.
    intro.
    exfalso.
    apply (le_not_lt n n0).
    apply le_Sn_le.
    apply not_le .
    intro.
    apply Nat.ltb_lt in H1.
    rewrite H1 in H0. inversion H0.
    
    apply NotLt.
    intro.
    apply le_lt_or_eq in H1.
    destruct H1.
    apply Nat.ltb_lt in H1.
    rewrite H1 in H. inversion H.
    rewrite H1 in H0.

    pose proof (le_n n0) as H2.
    
    apply (le_lt_n_Sm n0 n0) in H2.
    apply Nat.ltb_lt in H2.
    rewrite H2 in H0. inversion H0.
    
  + intros.
    simpl.
    rewrite IHu.
    trivial.
  
  + intros.
    simpl.
    rewrite IHu1. rewrite IHu2.
    trivial.
Qed.
Lemma inc_dec_single : forall u, decrement_vars_greater 0 (increment_free_vars u) = u.
Proof.
  intros.
  
  rewrite inc_dec_single_n.
  trivial.
Qed.


Lemma inc_comm_n : forall u n m,
  m <= n -> increment_greater m (increment_greater n u) = increment_greater (S n) (increment_greater m u).
Proof.
  intro.
  
  induction u.
  
  + intros.
    simpl.
    case_eq (n <? m).
    intro.
    apply Nat.ltb_lt in H0.

    apply (Nat.lt_le_trans n m n0) in H0 as H1.
    apply Nat.ltb_lt in H1.
    rewrite H1.

    simpl.
    apply Nat.ltb_lt in H0.
    rewrite H0.
    apply Nat.ltb_lt in H1.

    apply Nat.lt_lt_succ_r in H1.
    apply Nat.ltb_lt in H1. rewrite H1. trivial. trivial.
    intro.
    simpl.
    case_eq (n <? n0).
    intro.
    apply Nat.ltb_lt in H1.

    apply lt_n_S in H1.
    apply Nat.ltb_lt in H1.
    rewrite H1.
    simpl.
    rewrite H0.
    trivial.
    intro.
    simpl.
    case_eq (S n <? m).
    intro.
    apply Nat.ltb_lt in H2.

    apply (Nat.lt_le_trans (S n) m n0) in H2.
    apply Nat.lt_lt_succ_r in H2.
    apply Nat.ltb_lt in H2.
    rewrite H2.
    trivial.
    trivial.
    intro.
    case_eq (S n <? (S n0)).
    intro.
    apply Nat.ltb_lt in H3.

    apply lt_S_n in H3.
    apply Nat.ltb_lt in H3. rewrite H3 in H1. inversion H1.
    trivial.
    
    
  + intros.
    simpl.
    rewrite IHu.
    trivial.
    lia.
  
  + intros.
    simpl.
    rewrite IHu1. rewrite IHu2. trivial.
    trivial. trivial.
Qed.

Lemma inc_comm : forall u n,
  increment_free_vars (increment_greater n u) = increment_greater (S n) (increment_free_vars u).
Proof.
  intros.
  apply inc_comm_n.
  lia.
Qed.

Lemma inc_comm_li : forall l n,
 map increment_free_vars (map (increment_greater n) l) = map (increment_greater (S n)) (map increment_free_vars l).
Proof.

  intro.
  induction l.
  intros.
  simpl.
  trivial.
  intros.
  simpl.
  rewrite IHl.
  rewrite inc_comm.
  trivial.
Qed.

Lemma inc_dec_n : forall u n l, 
  ClosedN (n + length l) u -> decrement_vars_greater n (parallel_subst n (List.map (increment_greater n) l) u) = parallel_subst n l u.

Proof.
  intro.
  
  induction u.
  
  + intros.
    inversion H.
    simpl.
    case_eq (n0 <=? n).
    intros.
    simpl.
    apply Nat.leb_le in H3.
    rewrite map_length.
    case_eq (n <? n0 + length l).
    intro.
    apply Nat.ltb_lt in H4.

    rewrite (nth_indep (map (increment_greater n0) l)  (Var 0) (increment_greater n0 (Var 0))).
    rewrite map_nth.
    rewrite inc_dec_single_n.
    trivial.
    rewrite map_length.
    lia.
    intro.
    apply Nat.ltb_lt in H2.
    rewrite H2 in H4. inversion H4.
    intro.
    
    simpl.
    case_eq (n0 <? n).
    intro.
    exfalso.
    apply Nat.ltb_lt in H4.

    apply le_Sn_le in H4.
    apply Nat.leb_le in H4.
    rewrite H4 in H3. inversion H3.
    trivial.
   
  + intros.
    simpl.
    rewrite <- (IHu (S n) (map increment_free_vars l)).

    rewrite inc_comm_li.
    trivial.
    inversion H.

    rewrite plus_comm.
    rewrite <- plus_n_Sm.
    rewrite plus_comm.
    rewrite map_length.
    trivial.
  
  + intros.
    inversion H. 
    simpl.
    rewrite (IHu1).
    rewrite IHu2.
    trivial.
    trivial.
    trivial.
Qed.
     
    
(* Change to more general dec/inc ! *)
Lemma inc_dec : forall (u : de_brujin) (l : list de_brujin),
  ClosedN (length l) u -> decrement_vars_greater 0 (parallel_subst 0 (List.map increment_free_vars l) u) 
  = parallel_subst 0 l u.
Proof. 
  intros.
  apply inc_dec_n.

  rewrite Nat.add_0_l. trivial.
Qed.
Lemma sub_ineq : forall a b c,
  a < b + c -> a >= b -> a - b < c.
Proof.
  lia.
Qed.



Lemma ClosedIncrement : forall n m u, ClosedN n u -> ClosedN (S n) (increment_greater m u).
Proof.
  intro. intro. intro.
  generalize n m.
  clear n m.
  induction u.
  
  + intros.
    simpl.
    case_eq (n <? m).
    intro.
    inversion H. apply ClosedN_Var. 
    apply le_S in H3.
    trivial.
    intro.
    apply ClosedN_Var.
    apply lt_n_S.
    inversion H. trivial.
  
  + intros.
    simpl.
    apply ClosedN_Abstraction.
    apply IHu.
    inversion H.
    trivial.
  
  + intros.
    simpl. inversion H.
    apply ClosedN_App.
    apply IHu1. trivial.
    apply IHu2. trivial.
Qed.
  
Lemma ClosedIncForall : forall n l, Forall (ClosedN n) l -> Forall (ClosedN (S n)) (map increment_free_vars l).
Proof.
  intro.
  intro.
  generalize n.
  clear n.
  
  induction l.
  intros.
  simpl.
  trivial.
  
  intros.
  simpl.
  inversion H.
  apply Forall_cons.
  apply ClosedIncrement.
  trivial.
  apply IHl.
  trivial.
Qed.
  
Lemma SubstClosed : forall (u : de_brujin) (n : nat) (l : list de_brujin),
  Forall (ClosedN n) l -> ClosedN (n + length l) u -> ClosedN n (parallel_subst n l u).
Proof.
  intro.
  induction u.
  
  +
    intros.
    simpl.
    inversion H0.
    case_eq (n0 <=? n).
    intro.
    simpl.
    apply Nat.leb_le in H4.
    case_eq (n <? n0 + length l).
    intro.
    apply Nat.ltb_lt in H5.

    apply Forall_nth.
    trivial.
    lia.
    intro.
    apply Nat.ltb_lt in H3.
    rewrite H3 in H5. inversion H5.
    intro.
    simpl.
    apply ClosedN_Var.

    apply NotLt.
    intro.
    apply Nat.leb_le in H5. rewrite H5 in H4. inversion H4.
  
  + intros.
    simpl.
    apply ClosedN_Abstraction.
    apply IHu.
    apply ClosedIncForall.
    trivial.
    inversion H0.
    rewrite map_length.

    rewrite plus_comm in H3.
    rewrite plus_n_Sm in H3.
    rewrite plus_comm in H3.
    trivial.
  
  + intros.
    apply ClosedN_App.
    apply IHu1.
    trivial.
    inversion H0. trivial.
    apply IHu2. trivial. inversion H0. trivial.
Qed.
    

Lemma ClosedEnv : forall (e : environment),
  CorrectEnv e -> (revCompEnv e = None) \/ (exists liU, revCompEnv e = Some liU /\ (Forall Closed liU)).
Proof.
 intro.
  induction e.
  intro. right. exists []. simpl. split. trivial. apply Forall_nil.
  intro.
  simpl.
  case_eq (revCompCode c).
  intros.
  case_eq (revCompEnv e1).
  intros.
  case_eq (revCompEnv e2).
  intros.
  right.
  inversion H.
  apply IHe1 in H8.
  apply IHe2 in H6.
  destruct H6.
  rewrite H6 in H2. inversion H2.
  destruct H6.
  destruct H6.
  destruct H8. rewrite H8 in H1. inversion H1.
  destruct H8.
  exists (parallel_subst 0 l d :: l0).
  split.
  trivial.
  apply Forall_cons.
  destruct H8.
  rewrite H1 in H8.
  inversion H8. clear H8.
  rewrite <- H12 in H10.
  rewrite <- H12.
  apply SubstClosed.
  trivial.
  rewrite H2 in H6.
  inversion H6. destruct H7. destruct H7.
  rewrite H0 in H8.
  inversion H8.
  rewrite H14 in H7.
  rewrite (LengthRevEnv e1). trivial. trivial. 
  rewrite H2 in H6. inversion H6. trivial.
  left. trivial.
  intro. left. trivial.
  intro. left. trivial.
Qed.



Lemma BetaFold : forall (l : list de_brujin) (u : de_brujin) (v : de_brujin),
  Beta u v -> Beta (List.fold_left (fun cur toAdd => App cur toAdd) l u)
  (List.fold_left (fun cur toAdd => App cur toAdd) l v).
Proof.
  intro.
  induction l.
  simpl. trivial.
  
  simpl.
  intros.
  apply IHl.
  apply BetaAppL.
  trivial.
Qed.


Lemma ClosedIncClosed_n : forall u n, ClosedN n u -> ClosedN n (increment_greater n u).
Proof.
  intro.
  induction u.
  
  + intros.
   simpl.
   inversion H.
   apply Nat.ltb_lt in H2.
   rewrite H2.
   trivial.
   
 + intros.
   simpl.
   apply ClosedN_Abstraction.
   apply IHu.
   inversion H.
   trivial.
  
  + intros.
  simpl.
  apply ClosedN_App.
  apply IHu1.
  inversion H. trivial.
  apply IHu2. inversion H. trivial.
Qed.

Lemma ClosedIncClosed : forall u, Closed u -> Closed (increment_free_vars u).
Proof.
  intros.
  apply ClosedIncClosed_n.
  trivial.
Qed.
Lemma ClosedIncClosedList : forall li, Forall Closed li -> Forall Closed (List.map increment_free_vars li).
Proof.
  intro.
  induction li.
  trivial.
  intro.
  inversion H.
  simpl.
  apply Forall_cons.
  apply ClosedIncClosed.
  trivial.
  apply IHli.
  trivial.
Qed.

Lemma transition_beta_lemma : forall (u : de_brujin) (cur : state) (nxt : state),
  stepKrivine cur = Some nxt -> revCompState cur = Some u -> CorrectState cur ->
    revCompState cur = revCompState nxt \/ (exists (v : de_brujin), revCompState nxt = Some v /\ Beta u v). 
Proof.
  intros.
  destruct cur.
  destruct p.
  destruct c.
  
  + simpl in H0. inversion H0.
  
  + destruct i.
  
    ++ left.
       destruct n.
       
       * simpl in H.
         destruct e. inversion H.
         inversion H. destruct H.
         simpl.
         case_eq (revCompCode c0).
         intros.
         case_eq (revCompEnv e1).
         intros.
         case_eq (revCompEnv e2).
         intros.
         case_eq (revCompStack s).
         intros.
         simpl.
         trivial.
         trivial.
         intros.
         case_eq (revCompStack s).
         intros.
         simpl in H0.
         rewrite H in H0.
         rewrite H2 in H0.
         rewrite H4 in H0.
         inversion H0.
         trivial.
         trivial.
         trivial.
         
      * simpl in H.
        destruct e. inversion H.
        inversion H. destruct H.
        simpl.
        case_eq (revCompCode c0).
        case_eq (revCompEnv e1).
        case_eq (revCompEnv e2).
        case_eq (revCompStack s).
        intros.
        simpl.
        inversion H1.
        destruct H9.
        destruct H9.
        simpl in H12.
        inversion H12. clear H12.
        rewrite H14 in H9.
        inversion H9.
        simpl in H15.
        rewrite (LengthRevEnv e2 l0).
        apply (Nat.ltb_lt) in H15 as H17.
        apply lt_S_n in H15.
        apply Nat.ltb_lt in H15 as H16.
        rewrite H16. rewrite H17.
        rewrite sub_0. trivial.
        trivial. intros. trivial. intros. trivial.
        intros.
        case_eq (revCompEnv e2).
        intros.
        simpl in H0.
        rewrite H4 in H0.
        rewrite H in H0.
        case_eq (revCompCode c0).
        intros.
        rewrite H5 in H0. inversion H0.
        intro. rewrite H5 in H0. inversion H0. trivial.
        intros.
        case_eq (revCompEnv e2).
        intros.
        simpl in H0. rewrite H in H0. inversion H0.
        trivial.
        
      ++ apply correct_step in H1 as correct_next.
      destruct correct_next.
      destruct H2.
      rewrite H in H2.
      inversion H2. clear H2. rewrite <- H5.
      rewrite <- H5 in H3.
      clear H5.
      rename H3 into correct_nxt.
      simpl in H.
         destruct s.
         inversion H.
         inversion H. clear H.
         
         right.
         simpl.
         case_eq (revCompCode c).
         intros.
         case_eq (revCompCode c0).
         intros.
         case_eq (revCompEnv e0).
         intros.
         case_eq (revCompEnv e).
         intros.
         case_eq (revCompStack s).
         intros.
         exists (fold_left (fun cur nxt0 : de_brujin => App cur nxt0) l1
       (parallel_subst 0 (parallel_subst 0 l d0 :: l0) d)).
       split.
       trivial.
       simpl in H0.
       rewrite H in H0.
       rewrite H2 in H0. rewrite H4 in H0. rewrite H5 in H0. rewrite H6 in H0.
       inversion H0. clear H0.
       apply BetaFold.


       rewrite <- (inc_dec d).
       simpl.
       rewrite (Subst_composite 0 (increment_free_vars (parallel_subst 0 l d0)) (map increment_free_vars l0) d).
       
       apply BetaStep.
       inversion H1.
       apply (ClosedEnv) in H11.
       destruct H11.
       rewrite H5 in H11. inversion H11.
       destruct H11. destruct H11.
       rewrite H5 in H11.
       inversion H11. clear H11.
       
       destruct H10. destruct H10. destruct H11.
       apply ClosedIncClosedList.
       trivial.
       rewrite <- H3 in correct_nxt.
       inversion correct_nxt.
       destruct H10.
       destruct H10.
       rewrite H in H13.
       inversion H13. clear H13.
       rewrite H15 in H10.
       simpl.
       simpl in H10.

       rewrite (LengthRevEnv e l0).
       trivial.
       trivial.
       
       intro.
       simpl in H0.
       rewrite H6 in H0.
       case_eq (revCompCode c).
       intros.
       rewrite H7 in H0.
       rewrite H5 in H0.
       rewrite H2 in H0.
       case_eq (revCompEnv e0).
       intros.
       rewrite H8 in H0.
       inversion H0.
       intro.
       rewrite H8 in H0.
       inversion H0.
       intro.
       rewrite H7 in H0.
       inversion H0.
       intro.
       simpl in H0.
       rewrite H5 in H0.
       case_eq (revCompCode c).
       intros. rewrite H6 in H0. inversion H0.
       intro.
       rewrite H6 in H0.
       inversion H0.
       intro.
       simpl in H0.
       rewrite H4 in H0.
       rewrite H in H0.
       case_eq (revCompEnv e).
       intros.
       rewrite H5 in H0.
       rewrite H2 in H0.
       inversion H0.
       intro.
       rewrite H5 in H0.
       inversion H0.
       intro.
       simpl in H0.
       rewrite H in H0.
       case_eq (revCompEnv e).
       intros.
       rewrite H4 in H0.
       rewrite H2 in H0.
       inversion H0.
       intro.
       rewrite H4 in H0.
       inversion H0.
       intro.
       simpl in H0. rewrite H in H0.
       inversion H0.
       exists nxt.
       trivial.
     
     ++ left.
        simpl in H.
        inversion H. clear H.
        simpl.
        case_eq (revCompEnv e).
        intros.
        case_eq (revCompCode c).
        intros.
        case_eq (revCompCode c0).
        intros.
        case_eq (revCompStack s).
        intros.
        simpl.
        trivial.
        trivial.
        trivial.
        intro.
        simpl in H0.
        rewrite H in H0.
        rewrite H2 in H0.
        case_eq (revCompCode c0).
        intros. rewrite H4 in H0. inversion H0.
        trivial.
        intro.
        simpl in H0. rewrite H in H0.
        case_eq (revCompCode c0).
        intros. rewrite H2 in H0.
        case_eq (revCompCode c). trivial. trivial.
        intros. case_eq (revCompCode c). trivial. trivial.
Qed.

Theorem transition_beta : forall cur nxt,
  stepKrivine cur = Some nxt -> CorrectState cur -> 
    revCompState cur = revCompState nxt 
    \/ (exists u, revCompState cur = Some u /\ (exists v, revCompState nxt = Some v /\ Beta u v)).
Proof.
  intros.
  apply CorrectStateDecomp in H0 as H1.
  destruct H1.
  Check transition_beta_lemma.
  rename x into u.
  apply (transition_beta_lemma u) in H.
  destruct H.
  left. trivial.
  right.
  destruct H.
  exists u.
  split.
  trivial.
  exists x.
  split.
  destruct H.
  trivial.
  destruct H.
  trivial.
  trivial.
  trivial.
Qed.
