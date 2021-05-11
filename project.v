Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Logic.
Require Import Psatz.
Require Import Bool.
Require Import definitions.
Require Import lemmas.

(** Le prédicat C[[.]] est croissant **)
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
    lia.
  
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

(** Si C[[n]](u), alors en notant v le lambda-terme obtenu en incrémentant toutes les variables >= m de u, 
C[[n+1]](v)**)
Lemma closedN_incrementM : forall (n : nat) (m : nat) (u : de_brujin), 
  ClosedN n u -> ClosedN (S n) (increment_greater m u).
Proof.
  intro. intro. intro.
  generalize n m.
  clear n m.
  induction u.
  
  + intros.
    simpl.
    inversion H.
    clear m0 n1 H1 H0.
    case_eq (n <? m); intro; apply ClosedN_Var; lia.
    
  + intros.
    simpl.
    apply ClosedN_Abstraction.
    apply IHu.
    inversion H.
    trivial.
  
  + intros.
    simpl.
    apply ClosedN_App.
    inversion H.
    apply IHu1. trivial.
    apply IHu2. inversion H. trivial.
Qed.

(** Pareil mais pour tous les termes d'une liste de lambda-termes **)
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
  apply closedN_incrementM .
  trivial.
  apply IHl.
  trivial.
Qed.


(** Si C[[n]](u), alors u[[n <- t]] = u **)
Theorem ClosedN_subst : forall (n : nat) (t : de_brujin) (u : de_brujin),
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

(** Lemme pour n = 0, et donc décrit que substituer une variable par une autre dans un combinateur ne fait rien**)
Lemma Closed_subst : forall (n : nat) (t : de_brujin) (u : de_brujin),
  Closed u -> subst n t u = u.
Proof.
  intros.
  apply ClosedN_subst.
  apply Closed_lt.
  trivial.
Qed.

(** u[[n <- [[]]]] = u **)
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
    apply Nat.leb_le in H.
    apply Nat.ltb_lt in H0.
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

(** Si C[[i]](u), alors on a le même résultat que plus haut en substituant par une liste **)
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
    apply Nat.leb_le in H3.
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

(** Décrit le lemme de composition de la question I.4 **)
Theorem Subst_composite : forall (i : nat) (u0 : de_brujin) (q : list de_brujin) (u : de_brujin),
  List.Forall (ClosedN i) q -> parallel_subst i (u0 :: q) u = subst i u0 (parallel_subst (S i) q u).
Proof.
  intro. intro. intro. intro.
  generalize i u0 q. clear i u0 q.
  
  induction u.
  
  + intros.
    simpl.
    case_eq (i <=? n).
    intro. simpl. apply Nat.leb_le in H0.
    case_eq (n <? i + S (length q)).
    intro. simpl.
    apply Nat.ltb_lt in H1.
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

(** Passage au contexte de ->* à gauche **)
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

(** Passage au contexte de ->* à droite **)
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

(** Passage au contexte de ->* pour les abstractions**)
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

(** Pour les environnements corrects, la fonction tau ne peut pas renvoyer None **)
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

(** De même pour les stacks **)
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

(** Montre que tau est valide pour les états (i.e ne renvoie jamais None ) **)
Theorem CorrectStateDecomp : forall (st : state), 
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
  

(** Si tau(stk) = [[]] alors stk est vide **) 
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

(** Si tau(env) = [[]] alors env est vide **)
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

(** Si tau(env) renvoie une liste l, alors l a la même longueur que env **)
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

(** Appliquer tau à la machine de Krivine obtenue en compilant u renvoie u (même si u n'est pas clôt !)**)
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

(** Si un état est correct et qu'il a une transition, alors on reste correct après une transition **)
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

(** Décrit simplement que si on incrémente puis décrémente, on ne change rien 
    Plus généralement, les lemmes qui suivent décrivent simplement des relations entre ces deux opérateurs 
**)
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

(** Un lemme clé pour le grand théorème qui suit : si u est un lambda terme, l une liste de lambda terne
  alors si C[[n + |l|]](u), décrementer toutes les variables > n du lambda-terme obtenue en subsituant n, n + 1 , ..., n + |l|-1 par les termes de l obtenu en incrémentant les variables >= n, revient à juste faire u[[n <- l]] **)
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

(** Le lemme précédent pour n = 0 **)
Lemma inc_dec : forall (u : de_brujin) (l : list de_brujin),
  ClosedN (length l) u -> decrement_vars_greater 0 (parallel_subst 0 (List.map increment_free_vars l) u) 
  = parallel_subst 0 l u.
Proof. 
  intros.
  apply inc_dec_n.

  rewrite Nat.add_0_l. trivial.
Qed.

(** Si l = [[u_1, ..., u_k]] et que C[[n]](u_i) pour tout i, et que C[[n + |l|]](u),
alors C[[n]](u[[n <- l]]) **)
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

(** Si e est un environnement correct, alors ou bien tau(env) = None,
  ou bien tau(e) = l et tous les termes de l sont clos. Lemme fondamental pour la suite **)
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

(** Lemme trivial : Dit que si u -> v, alors u u_1 ... u_k -> v u_1 ... u_k **)
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

(** Si u n'a pas de variables libres, alors les incrémenter ne fait rien ...**)
Lemma ClosedIncClosed : forall u, Closed u -> Closed (increment_free_vars u).
Proof.
  intros.
  apply ClosedIncClosed_n.
  trivial.
Qed.

(** Pareil pour les listes **)
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

(** Si cur ->_kriv nxt, et tau(cur) = u, et cur est correct, alors ou bien tau(nxt) = u, ou bien u -> tau(nxt)
l'énoncé demande de montrer que seulement le deuxième cas est possible, mais dans ma preuve je montre 
que dans certains cas (les 2/3 en fait), tau modifie l'état sans changer le lambda-terme associé (en modifiant l'environnement ou la stack)**)
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

(** Même théorème que ci-dessus en ne supposant plus l'existence de u, qui découle d'un autre théorème**)
Theorem transition_beta : forall cur nxt,
  stepKrivine cur = Some nxt -> CorrectState cur -> 
    revCompState cur = revCompState nxt 
    \/ (exists u, revCompState cur = Some u /\ (exists v, revCompState nxt = Some v /\ Beta u v)).
Proof.
  intros.
  apply CorrectStateDecomp in H0 as H1.
  destruct H1.

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

(** Si u est clos, alors (Comp u, [[]], [[]]) est un état valide**)
Theorem compilation_valide : forall u,
  Closed u -> CorrectState (Comp u, EmptyEnv, EmptyStack).
Proof.
  intros.
  split.
  + exists u.
    split.
    simpl.
    trivial.
    rewrite <- CompInverse.
    simpl.
    case_eq (revCompCode (Comp u)).
    intros.
    rewrite subst_empty_trivial.
    trivial.
    trivial.
    
  + apply CorrectEmptyEnv.
  + apply CorrectEmptyStk.
Qed.

(** Si un état s se réduit en n étapes en t, et s est valide, alors tau(s) ->* tau(t) **)
Theorem transitions_beta_star : forall n s st,
  CorrectState s -> KrivineReduceN n s st -> (exists u, revCompState s = Some u /\ (exists v, revCompState st = Some v /\ BetaS u v)).
Proof.
  intro.
  induction n.
  
  + intros.
    inversion H0.
    rewrite <- H3.
    apply CorrectStateDecomp in H.
    destruct H.
    rewrite H.
    exists x.
    split.
    trivial.
    exists x.
    split. trivial. apply BetaSRefl.

  + intros.
    inversion H0.
    apply IHn in H3.
    destruct H3.
    destruct H3.
    destruct H6.
    destruct H6.
    apply (transition_beta s t) in H.
    destruct H.
    exists x.
    split.
    rewrite H.
    trivial.
    exists x0.
    split.
    trivial.
    trivial.
    destruct H.
    destruct H.
    destruct H8.
    destruct H8.
    exists x1.
    split.
    trivial.
    exists x0.
    split.
    trivial.
    apply (BetaSStep x1 x2 x0).
    trivial.
    rewrite H8 in H3.
    inversion H3.
    trivial.
    trivial.
    apply correct_step in H.
    destruct H.
    destruct H.
    rewrite H in H2.
    inversion H2.
    rewrite <- H8.
    trivial.
    exists t.
    trivial.
Qed.

(** Pareil mais en partant de l'etat initial associé à un lambda-terme**)
Theorem compilation_reductions : forall u st n,
  KrivineReduceN n (Comp u, EmptyEnv, EmptyStack) st -> Closed u -> (exists v, revCompState st = Some v /\ BetaS u v).
Proof.
  intros.
  apply compilation_valide in H0.
  apply (transitions_beta_star n (Comp u, EmptyEnv, EmptyStack) st) in H.
  destruct H.
  destruct H.
  destruct H1.
  destruct H1.
  exists x0.
  split.
  trivial.
  rewrite  CompInverse in H.
  inversion H.
  trivial.
  trivial.
Qed.

(** Le théorème de la compilation, qui dit que si on prend un combinateur u,
alors en notant s l'état initial associé à u, si s se réduit en un nombre fini d'étapes en t, alors u ->* tau(t) **)
Theorem theoreme_compilation : forall u st,
  KrivineReduce (Comp u, EmptyEnv, EmptyStack) st -> Closed u -> (exists v, revCompState st = Some v /\ BetaS u v).
Proof.
  intros.
  destruct H.
  apply compilation_reductions in H.
  destruct H.
  exists x0.
  trivial.
  trivial.
Qed.