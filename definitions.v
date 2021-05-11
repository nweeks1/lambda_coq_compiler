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

(** Substitue la variable libre n par t dans u **)

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


(** Si liU = [[t_1, ..., t_k]], alors cette fonction renvoie u[[i <- t_1, ..., t_k]] **)

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

(** Décrémente toutes les variables > n**)

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

(** Restriction de tau aux codes **)
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

(** Restriction de tau aux environnements, renvoie la liste des substitutions **)
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

(** De même pour les stack, renvoie la liste des applications à effectuer **)
Fixpoint revCompStack (stk : stack) : option (list de_brujin) :=
  match stk with
    | EmptyStack => Some []
    | ConsStack c0 e0 nxtStk => 
      match revCompCode c0, revCompEnv e0, revCompStack nxtStk with
        | None, _, _ | _, None, _ | _, _, None => None
        | Some u, Some liU, Some liStk => Some ((parallel_subst 0 liU u) :: liStk)
      end
  end.

(** revCompState = tau pour les états **)
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

(** Traduit le fait qu'une machine de krivine s se réduit en t en n étapes
J'ai eu besoin de quantifier n pour pouvoir faire des récurrences sur la longueur de la 
réduction, je ne sais pas pourquoi je ne pouvais pas faire une récurrence sinon. **)
Inductive KrivineReduceN : nat -> state -> state -> Prop :=
  | KrivineReduce0 : forall (st : state), KrivineReduceN 0 st st
  | KrivineReduceS : forall n s t v,
    stepKrivine s = Some t -> KrivineReduceN n t v -> KrivineReduceN (S n) s v.

(** Clôture réflexive et transitive de la relation -> pour les machines de Krivine **)
Definition KrivineReduce (s : state) (t : state) := exists n, KrivineReduceN n s t.