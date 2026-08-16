-- CicModel/MyList.lean
import Mathlib.Data.List.Basic

namespace CicModel

section MyList

variable {A : Type}

-- Inductive predicate for item
inductive item (x : A) : List A → Nat → Prop where
  | item_hd : ∀ l : List A, item x (x :: l) 0
  | item_tl : ∀ (l : List A) (n : Nat) (y : A), item x l n → item x (y :: l) (n + 1)

-- uniqueness of item
theorem fun_item {u v : A} {e : List A} {n : Nat} (h1 : item u e n) (h2 : item v e n) : u = v := by
  induction h1 generalizing v with
  | item_hd l =>
    cases h2 with
    | item_hd => rfl
  | item_tl l' n' y' _ ih =>
    cases h2 with
    | item_tl _ _ _ h2' => exact ih h2'

-- nth_def: returns nth element with default value d
def nth_def (d : A) : List A → Nat → A
  | [], _ => d
  | x :: _, 0 => x
  | _ :: tl, k + 1 => nth_def d tl k

theorem nth_sound {x : A} {l : List A} {n : Nat} {d : A} (h : item x l n) : nth_def d l n = x := by
  induction h with
  | item_hd l' => rfl
  | item_tl l' n' y' _ ih => exact ih

theorem inv_nth_nl {x : A} {n : Nat} (h : item x [] n) : False := by
  cases h

theorem inv_nth_cs {x y : A} {l : List A} {n : Nat} (h : item x (y :: l) (n + 1)) : item x l n := by
  cases h with
  | item_tl _ _ _ h_tl => exact h_tl

-- Inductive predicate for insert
inductive insert (x : A) : Nat → List A → List A → Prop where
  | insert_hd : ∀ l : List A, insert x 0 l (x :: l)
  | insert_tl : ∀ (n : Nat) (l il : List A) (y : A), insert x n l il → insert x (n + 1) (y :: l) (y :: il)

-- Inductive predicate for trunc
inductive trunc : Nat → List A → List A → Prop where
  | trunc_O : ∀ e : List A, trunc 0 e e
  | trunc_S : ∀ (k : Nat) (e f : List A) (x : A), trunc k e f → trunc (k + 1) (x :: e) f

theorem item_trunc {n : Nat} {e : List A} {t : A} (h : item t e n) : ∃ f : List A, trunc (n + 1) e f := by
  induction n generalizing e with
  | zero =>
    cases h with
    | item_hd l => exact ⟨l, trunc.trunc_S 0 _ _ _ (trunc.trunc_O _)⟩
  | succ n' ih =>
    cases h with
    | item_tl l' _ y h_tl =>
      have ⟨f', h_trunc⟩ := ih h_tl
      exact ⟨f', trunc.trunc_S _ _ _ y h_trunc⟩

theorem ins_le {k : Nat} {f g : List A} {d x : A} (h_ins : insert x k f g) (n : Nat) (h_le : k ≤ n) :
    nth_def d f n = nth_def d g (n + 1) := by
  induction h_ins generalizing n with
  | insert_hd l =>
    cases n with
    | zero => rfl
    | succ n' => rfl
  | insert_tl k' l il y' _ ih =>
    cases n with
    | zero => exfalso; omega
    | succ n' =>
      dsimp [nth_def]
      apply ih
      omega

theorem ins_gt {k : Nat} {f g : List A} {d x : A} (h_ins : insert x k f g) (n : Nat) (h_gt : k > n) :
    nth_def d f n = nth_def d g n := by
  induction h_ins generalizing n with
  | insert_hd l => exfalso; omega
  | insert_tl k' l il y' _ ih =>
    cases n with
    | zero => rfl
    | succ n' =>
      dsimp [nth_def]
      apply ih
      omega

theorem ins_eq {k : Nat} {f g : List A} {d x : A} (h_ins : insert x k f g) :
    nth_def d g k = x := by
  induction h_ins with
  | insert_hd l => rfl
  | insert_tl k' l il y' _ ih => exact ih

-- list_item decidability
theorem list_item (e : List A) (n : Nat) :
    (∃ t : A, item t e n) ∨ (∀ t : A, ¬ item t e n) := by
  induction e generalizing n with
  | nil =>
    right
    intro t ht
    cases ht
  | cons h tl ih =>
    cases n with
    | zero =>
      left
      exact ⟨h, item.item_hd tl⟩
    | succ n' =>
      cases ih n' with
      | inl h_ex =>
        have ⟨t, itm⟩ := h_ex
        left
        exact ⟨t, item.item_tl tl n' h itm⟩
      | inr h_not =>
        right
        intro t ht
        cases ht with
        | item_tl _ _ _ itm_tl => exact h_not t itm_tl

end MyList

-- list map function (standard list map)
def my_map {A B : Type} (f : A → B) : List A → List B
  | [] => []
  | x :: xs => f x :: my_map f xs

end CicModel
