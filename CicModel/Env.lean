import CicModel.Term

def Env : Type := List Term

def Item (x : Term) (l : List Term) (n : Nat) : Prop :=
  l[n]? = some x

def ItemLift (t : Term) (e : Env) (n : Nat) : Prop :=
  ∃ u, t = lift (n + 1) u ∧ Item u e n

inductive InsInEnv (A : Term) : Nat → Env → Env → Prop where
  | ins_O : ∀ e, InsInEnv A 0 e (A :: e)
  | ins_S : ∀ n e f t, InsInEnv A n e f → InsInEnv A (n + 1) (t :: e) (liftRec 1 t n :: f)

inductive SubInEnv (t T : Term) : Nat → Env → Env → Prop where
  | sub_O : ∀ e, SubInEnv t T 0 (T :: e) e
  | sub_S : ∀ e f n u, SubInEnv t T n e f → SubInEnv t T (n + 1) (u :: e) (substRec t u n :: f)
