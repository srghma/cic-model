inductive SortT : Type where
  | kind : SortT
  | prop : SortT

inductive Term : Type where
  | srt : SortT → Term
  | ref : Nat → Term
  | abs : Term → Term → Term
  | app : Term → Term → Term
  | prod : Term → Term → Term

def liftRec (n : Nat) (t : Term) (k : Nat) : Term :=
  match t with
  | Term.srt s => Term.srt s
  | Term.ref i => if i >= k then Term.ref (i + n) else Term.ref i
  | Term.abs T M => Term.abs (liftRec n T k) (liftRec n M (k + 1))
  | Term.app u v => Term.app (liftRec n u k) (liftRec n v k)
  | Term.prod A B => Term.prod (liftRec n A k) (liftRec n B (k + 1))

def lift (n : Nat) (t : Term) : Term := liftRec n t 0

def substRec (N M : Term) (k : Nat) : Term :=
  match M with
  | Term.srt s => Term.srt s
  | Term.ref i =>
      if i > k then
        Term.ref (i - 1)
      else if i = k then
        liftRec k N 0
      else
        Term.ref i
  | Term.abs A B => Term.abs (substRec N A k) (substRec N B (k + 1))
  | Term.app u v => Term.app (substRec N u k) (substRec N v k)
  | Term.prod T U => Term.prod (substRec N T k) (substRec N U (k + 1))

def subst (N M : Term) : Term := substRec N M 0

inductive Subterm : Term → Term → Prop where
  | abs_l : ∀ A B, Subterm A (Term.abs A B)
  | abs_r : ∀ A B, Subterm B (Term.abs A B)
  | app_l : ∀ A B, Subterm A (Term.app A B)
  | app_r : ∀ A B, Subterm B (Term.app A B)
  | prod_l : ∀ A B, Subterm A (Term.prod A B)
  | prod_r : ∀ A B, Subterm B (Term.prod A B)

inductive MemSort (s : SortT) : Term → Prop where
  | eq : MemSort s (Term.srt s)
  | prod_l : ∀ u v, MemSort s u → MemSort s (Term.prod u v)
  | prod_r : ∀ u v, MemSort s v → MemSort s (Term.prod u v)
  | abs_l : ∀ u v, MemSort s u → MemSort s (Term.abs u v)
  | abs_r : ∀ u v, MemSort s v → MemSort s (Term.abs u v)
  | app_l : ∀ u v, MemSort s u → MemSort s (Term.app u v)
  | app_r : ∀ u v, MemSort s v → MemSort s (Term.app u v)

inductive Red1 : Term → Term → Prop where
  | beta : ∀ M N T, Red1 (Term.app (Term.abs T M) N) (subst N M)
  | abs_red_l : ∀ M M' N, Red1 M M' → Red1 (Term.abs M N) (Term.abs M' N)
  | abs_red_r : ∀ M M' N, Red1 M M' → Red1 (Term.abs N M) (Term.abs N M')
  | app_red_l : ∀ M1 N1 M2, Red1 M1 N1 → Red1 (Term.app M1 M2) (Term.app N1 M2)
  | app_red_r : ∀ M2 N2 M1, Red1 M2 N2 → Red1 (Term.app M1 M2) (Term.app M1 N2)
  | prod_red_l : ∀ M1 N1 M2, Red1 M1 N1 → Red1 (Term.prod M1 M2) (Term.prod N1 M2)
  | prod_red_r : ∀ M2 N2 M1, Red1 M2 N2 → Red1 (Term.prod M1 M2) (Term.prod M1 N2)

inductive Red (M : Term) : Term → Prop where
  | refl : Red M M
  | trans : ∀ P N, Red M P → Red1 P N → Red M N

inductive Conv (M : Term) : Term → Prop where
  | refl : Conv M M
  | trans_red : ∀ P N, Conv M P → Red1 P N → Conv M N
  | trans_exp : ∀ P N, Conv M P → Red1 N P → Conv M N

inductive ParRed1 : Term → Term → Prop where
  | beta : ∀ M M' N N' T, ParRed1 M M' → ParRed1 N N' → ParRed1 (Term.app (Term.abs T M) N) (subst N' M')
  | sort : ∀ s, ParRed1 (Term.srt s) (Term.srt s)
  | ref : ∀ n, ParRed1 (Term.ref n) (Term.ref n)
  | abs : ∀ M M' T T', ParRed1 M M' → ParRed1 T T' → ParRed1 (Term.abs T M) (Term.abs T' M')
  | app : ∀ M M' N N', ParRed1 M M' → ParRed1 N N' → ParRed1 (Term.app M N) (Term.app M' N')
  | prod : ∀ M M' N N', ParRed1 M M' → ParRed1 N N' → ParRed1 (Term.prod M N) (Term.prod M' N')
