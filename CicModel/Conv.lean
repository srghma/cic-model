import CicModel.Term

def StrConfluent (R : Term → Term → Prop) : Prop :=
  ∀ x y z, R x y → R x z → ∃ u, R y u ∧ R z u

inductive ParRed (M : Term) : Term → Prop where
  | refl : ParRed M M
  | trans : ∀ P N, ParRed M P → ParRed1 P N → ParRed M N

def Commut (R S : Term → Term → Prop) : Prop :=
  ∀ x y, R x y → ∀ z, S x z → ∃ u, S y u ∧ R z u

def Normal (t : Term) : Prop :=
  ∀ t', ¬ Red1 t t'

theorem str_confluence_par_red1 : StrConfluent ParRed1 := by
  sorry

theorem strip_lemma : Commut ParRed (fun a b => ParRed1 b a) := by
  sorry

theorem confluence_par_red : StrConfluent ParRed := by
  sorry

theorem confluence_red : StrConfluent Red := by
  sorry


theorem church_rosser :
  ∀ u v, Conv u v → ∃ t, Red u t ∧ Red v t := by
  sorry

theorem inv_conv_prod_l :
  ∀ a b c d, Conv (Term.prod a c) (Term.prod b d) → Conv a b := by
  sorry

theorem inv_conv_prod_r :
  ∀ a b c d, Conv (Term.prod a c) (Term.prod b d) → Conv c d := by
  sorry

theorem nf_uniqueness :
  ∀ u v, Conv u v → Normal u → Normal v → u = v := by
  sorry

theorem conv_sort :
  ∀ s1 s2, Conv (Term.srt s1) (Term.srt s2) → s1 = s2 := by
  sorry

theorem conv_kind_prop :
  ¬ Conv (Term.srt SortT.kind) (Term.srt SortT.prop) := by
  sorry

theorem conv_sort_prod :
  ∀ s t u, ¬ Conv (Term.srt s) (Term.prod t u) := by
  sorry
