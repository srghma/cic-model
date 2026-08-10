-- CicModel/Lambda.lean
import Mathlib.Data.Nat.Basic

namespace CicModel

inductive term : Type
  | Ref (n : Nat)
  | Abs (body : term)
  | App (f arg : term)

namespace term

-- Shifting (lifting) de Bruijn indices
def lift_rec (n : Nat) (t : term) (k : Nat) : term :=
  match t with
  | Ref i =>
    if i ≥ k then Ref (n + i)
    else Ref i
  | Abs M => Abs (lift_rec n M (k + 1))
  | App u v => App (lift_rec n u k) (lift_rec n v k)

def lift (n : Nat) (t : term) : term :=
  lift_rec n t 0

-- Substitution of N into M at index k
def subst_rec (N : term) (M : term) (k : Nat) : term :=
  match M with
  | Ref i =>
    if i > k then Ref (i - 1)
    else if i = k then lift k N
    else Ref i
  | Abs B => Abs (subst_rec N B (k + 1))
  | App u v => App (subst_rec N u k) (subst_rec N v k)

def subst (N M : term) : term :=
  subst_rec N M 0

-- Inductive predicate for subterm
inductive subterm : term → term → Prop where
  | sbtrm_abs : ∀ B : term, subterm B (Abs B)
  | sbtrm_app_l : ∀ A B : term, subterm A (App A B)
  | sbtrm_app_r : ∀ A B : term, subterm B (App A B)

-- Inductive predicate for occur
inductive occur : Nat → term → Prop
  | occ_var : ∀ n : Nat, occur n (Ref n)
  | occ_app_l : ∀ (n : Nat) (A B : term), occur n A → occur n (App A B)
  | occ_app_r : ∀ (n : Nat) (A B : term), occur n B → occur n (App A B)
  | occ_abs : ∀ (n : Nat) (M : term), occur (n + 1) M → occur n (Abs M)

-- Boolean checker for occurrences
def boccur (n : Nat) (t : term) : Bool :=
  match t with
  | Ref i => i == n
  | App u v => (boccur n u) || (boccur n v)
  | Abs m => boccur (n + 1) m

def closed (t : term) : Prop :=
  ∀ k : Nat, ¬ occur k t

end term

end CicModel
