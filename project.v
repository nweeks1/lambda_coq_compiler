Print nat.
Print Nat.pred.

(* On adopte une convention un peu différente, pour ne pas avoir à faire à des entiers négatifs 
  (je veux rester avec nat), le terme lambda x. x sera représenté par le terme lambda. 1 et non
  lambda.0.
*)

Inductive de_brujin : Set :=
  | Var : nat -> de_brujin
  | Abstraction : de_brujin -> de_brujin
  | App : de_brujin -> de_brujin -> de_brujin
.

Print nat.

Print de_brujin.
Print de_brujin_ind.
Print nat_ind.
(*
  Cette fonction décrémente toutes les variables d'une expression.
*)

Fixpoint decrement_vars (u: de_brujin) : de_brujin := 
  match u with
    | Var i => Var (pred i)
    | App v w => App (decrement_vars v) (decrement_vars w)
    | Abstraction v => Abstraction (decrement_vars v)
    end
.

(* 
 On a ClosedN n u ssi toutes les variables libres de u sont <= n.
 Ainsi, u est clos ssi closedN 0 u.
 Pour définir closedN n u, c'est assez immédiat dans le cas d'une variable ou d'une application
 Pour le cas d'une abstraction lambda . u, il faut faire attention aux 1 qui peuvent être présents
 dans le terme, qui sont des variables liées. Pour cela, on décrémente de 1 toutes les variables
 qui apparaissent dans u. de sorte à ce que les 1 n'influent plus, mais on décrémente aussi
 n de 1
*)

Inductive ClosedN : nat -> de_brujin -> Prop :=
  | ClosedN_Var : forall n m : nat, m <= n -> ClosedN n (Var m)
  | ClosedN_App : forall (n : nat) (u : de_brujin) (v : de_brujin),
              ClosedN n u -> ClosedN n v -> ClosedN n (App u v)
  | ClosedN_Abstraction : forall (n : nat) (u : de_brujin),
              ClosedN n (decrement_vars u) -> ClosedN (S n) (Abstraction u)
.


Theorem ClosedIncreasing : forall (n : nat) (u : de_brujin), ClosedN n u -> ClosedN (S n) u.
Proof.
  intro.
  induction n.
  
  + intro.
    induction u.
    intro. inversion H. apply ClosedN_Var. apply le_S. trivial.
    intro. inversion H.
    intro.
    inversion H.
    apply ClosedN_App.
    apply IHu1. trivial. apply IHu2. trivial.
    
  + intro.
    induction u.
    
    intro. inversion H. apply ClosedN_Var. apply le_S. trivial.
    
    intro.
    inversion H.
    apply ClosedN_Abstraction.
    apply IHn. trivial.
    
    intro.
    inversion H.
    apply ClosedN_App. apply IHu1. trivial. apply IHu2. trivial.
Qed.

Definition Closed : de_brujin -> Type := ClosedN 0.

Fixpoint subst (n : nat) (t : de_brujin) (u : de_brujin) =
  match u with
    | Var i => 
        if i = n then t else u
    | App v w => 
        App (subst n t v) (subst n t w)
    | Abstraction v => 
        if n = 0 then 
          Abstraction v
        else
        
