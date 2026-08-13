import CicModel.Term
import CicModel.Env
import CicModel.Conv

mutual
  inductive Wf : Env → Prop where
    | wf_nil : Wf []
    | wf_var : ∀ e T s, Typ e T (Term.srt s) → Wf (T :: e)

  inductive Typ : Env → Term → Term → Prop where
    | type_prop : ∀ e, Wf e → Typ e (Term.srt SortT.prop) (Term.srt SortT.kind)
    | type_var : ∀ e v t, Wf e → ItemLift t e v → Typ e (Term.ref v) t
    | type_abs : ∀ e T M U s1 s2,
        Typ e T (Term.srt s1) →
        Typ (T :: e) U (Term.srt s2) →
        Typ (T :: e) M U →
        Typ e (Term.abs T M) (Term.prod T U)
    | type_app : ∀ e u v V Ur,
        Typ e v V →
        Typ e u (Term.prod V Ur) →
        Typ e (Term.app u v) (subst v Ur)
    | type_prod : ∀ e T U s1 s2,
        Typ e T (Term.srt s1) →
        Typ (T :: e) U (Term.srt s2) →
        Typ e (Term.prod T U) (Term.srt s2)
    | type_conv : ∀ e t U V s,
        Typ e t U →
        Conv U V →
        Typ e V (Term.srt s) →
        Typ e t V
end

theorem typ_wf : ∀ {e t T}, Typ e t T → Wf e
  | _, _, _, Typ.type_prop e hwf => hwf
  | _, _, _, Typ.type_var e _ _ hwf _ => hwf
  | _, _, _, Typ.type_abs e _ _ _ _ _ hT _ _ => typ_wf hT
  | _, _, _, Typ.type_app e _ _ _ _ _ hu => typ_wf hu
  | _, _, _, Typ.type_prod e _ _ _ _ hT _ => typ_wf hT
  | _, _, _, Typ.type_conv e _ _ _ _ ht _ _ => typ_wf ht

theorem thinning :
  ∀ e t T A, Typ e t T → Wf (A :: e) → Typ (A :: e) (lift 1 t) (lift 1 T) := by
  sorry

theorem substitution :
  ∀ e t u U d, Typ (t :: e) u U → Typ e d t → Typ e (subst d u) (subst d U) := by
  sorry

theorem typ_unique :
  ∀ e t T, Typ e t T → ∀ U, Typ e t U → Conv T U := by
  sorry

theorem type_case :
  ∀ e t T, Typ e t T → (∃ s, Typ e T (Term.srt s)) ∨ T = Term.srt SortT.kind := by
  sorry

theorem subj_red :
  ∀ e t T, Typ e t T → ∀ u, Red1 t u → Typ e u T := by
  sorry

theorem subject_reduction :
  ∀ e t u, Red t u → ∀ T, Typ e t T → Typ e u T := by
  sorry
