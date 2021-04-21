Require Import List.
Import ListNotations.
Require Import Arith.
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


Inductive Beta : de_brujin -> de_brujin -> Prop :=
  | BetaStep : forall (u : de_brujin) (v : de_brujin), 
    Beta (App (Abstraction u) v ) (subst 0 v u)
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
    CorrectStack nxtStk -> (exists u, ClosedN (length_env e0) u /\ Some u = revCompCode c0)
    -> CorrectStack (ConsStack c0 e0 nxtStk).

Inductive CorrectState : state -> Prop :=
  | CorrectSt : forall (c : code) (env : environment) (stk : stack),
    (exists u, ClosedN (length_env env) u /\ Some u = revCompCode c)
    -> CorrectEnv env -> CorrectStack stk -> CorrectState (c, env, stk).

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
    CorrectState cur -> (exists nxt, stepKrivine cur = Some nxt /\ CorrectState nxt).
Proof.
  intros.
  induction cur.
  induction a.
  rename a into c.
  rename b0 into env.
  rename b into stk.
  
  induction c.
  
  + simpl.
    inversion H.
    simpl in H3.
    inversion H3.
    inversion H6.
    inversion H8.
  
  + simpl.
    induction i.
    
    ++ induction n.
       
       +++ induction env.
           * inversion H.
            inversion H3.
            simpl in H6.
            inversion H6.
            inversion H8.
            clear H8 H6.
            inversion H7.
            inversion H6.
            rewrite H10 in H11.
            inversion H11.
            rewrite H10 in H9.
            inversion H9.
          
          * inversion H.
            clear H2 H1 H0 c1 env stk0.
            exists (c0, env1, stk).
            split.
            trivial.
            apply CorrectSt.
            
            ** inversion H4.
               trivial.
            ** inversion H4.
               trivial.
            ** trivial.
          
      +++ induction env.
          
          * inversion H.
            inversion H3.
            simpl in H6.
            inversion H6.
            inversion H8.
            inversion H7.
            inversion H9.
            rewrite H10 in H13.
            inversion H13.
            rewrite H10 in H12.
            inversion H12.
            
          * exists (ConsCode (Access n) EmptyCode, env2, stk).
            split.
            trivial.
            apply CorrectSt.
            
            ** simpl.
               exists (Var n).
               split.
               inversion H.
               inversion H3.
               simpl in H6.
               inversion H6.
               inversion H8.
               rewrite H10 in H7.
               inversion H7.
               apply ClosedN_Var.
               apply lt_S_n in H12.
               trivial.
               trivial.
           
            ** inversion H.
               inversion H4.
               trivial.
               
            ** inversion H.
               trivial.
     ++ induction stk.
        
        +++ exfalso.
            inversion H.
            clear H0 H1 H2 H5 c0 env0 stk.
            simpl in H3.