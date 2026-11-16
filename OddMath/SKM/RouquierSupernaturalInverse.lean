import OddMath.SKM.RouquierHomPostNaturalInverse

/-!
# Augmented inverses in the superfunctor category

Homogeneous component extensionality lifts the five augmented inverse
identities to the full SCat Hom category, without replacing it by its even
subcategory or requiring biproduct objects in the probe category.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v r
variable {k : Type r} [CommRing k] {C C' : Type u} [Category.{v} C] [Category.{v} C']
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive C'] [Linear k C'] [Supercategory k C']
  {F G H : Superfunctor k C C'}

private theorem homogeneous_comp_app {p q : ZMod 2}
    {x : ∀ Z, F.obj Z ⟶ G.obj Z} {y : ∀ Z, G.obj Z ⟶ H.obj Z}
    (hx : IsSupernatural k p x) (hy : IsSupernatural k q y) (s : ZMod 2) (Z : C) :
    ((Superfunctor.homMk (F := F) (G := G) hx.toSuperNatTrans) ≫ (Superfunctor.homMk (F := G) (G := H) hy.toSuperNatTrans)).app s Z =
      if s = p + q then x Z ≫ y Z else 0 := by
  fin_cases p <;> fin_cases q <;> fin_cases s <;>
    simp [Superfunctor.comp_app, IsSupernatural.toSuperNatTrans, SuperNatTrans.zmod2_one_add_one]

private theorem transformation_sum_app {F G : Superfunctor k C C'}
    (s : Finset ℕ) (x : ℕ → (F ⟶ G)) (p : ZMod 2) (Z : C) :
    (∑ n ∈ s, x n).app p Z = ∑ n ∈ s, (x n).app p Z := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih => simp [Finset.sum_insert, hn, ih]

/-- Lift the prescribed pointwise row inverse using signed naturality of all entries. -/
def SuperSumInvTo.supernatural
    {f : ∀ Z, F.obj Z ⟶ G.obj Z} {g : ℕ → ∀ Z, F.obj Z ⟶ H.obj Z}
    {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
    (J : ∀ Z, SuperSumInvTo (k := k) (f Z) (fun m => g m Z) p q n)
    (hf : IsSupernatural k p f) (hg : ∀ m, IsSupernatural k (q m) (g m))
    (hj : IsSupernatural k p (fun Z => (J Z).f'))
    (hk : ∀ m, IsSupernatural k (q m) (fun Z => (J Z).g' m)) :
    SuperSumInvTo (k := k) (Superfunctor.homMk (F := F) (G := G) hf.toSuperNatTrans)
      (fun m => (Superfunctor.homMk (F := F) (G := H) (hg m).toSuperNatTrans)) p q n where
  f' := hj.toSuperNatTrans
  g' m := (hk m).toSuperNatTrans
  f_mem := Superfunctor.IsSupernatural.toSuperNatTrans_mem hf
  g_mem m := Superfunctor.IsSupernatural.toSuperNatTrans_mem (hg m)
  f'_mem := Superfunctor.IsSupernatural.toSuperNatTrans_mem hj
  g'_mem m := Superfunctor.IsSupernatural.toSuperNatTrans_mem (hk m)
  total := by
    apply Superfunctor.hom_ext
    intro s Z
    simp only [Superfunctor.add_app, transformation_sum_app, homogeneous_comp_app,
      zmod2_add_self]
    fin_cases s
    · simpa using (J Z).total
    · simp
  ff := by
    apply Superfunctor.hom_ext
    intro s Z
    simp only [homogeneous_comp_app, zmod2_add_self]
    fin_cases s
    · simpa using (J Z).ff
    · simp
  fg m hm := by
    apply Superfunctor.hom_ext
    intro s Z
    simp only [homogeneous_comp_app, (J Z).fg m hm, ite_self, Superfunctor.zero_app]
  gf m hm := by
    apply Superfunctor.hom_ext
    intro s Z
    simp only [homogeneous_comp_app, (J Z).gf m hm, ite_self, Superfunctor.zero_app]
  gg m l hm hl := by
    apply Superfunctor.hom_ext
    intro s Z
    rw [homogeneous_comp_app, (J Z).gg m l hm hl]
    by_cases e : m = l
    · subst l
      fin_cases s <;> simp [zmod2_add_self]
    · simp [e]

/-- Lift the prescribed pointwise column inverse using signed naturality of all entries. -/
def SuperSumInvFrom.supernatural
    {f : ∀ Z, G.obj Z ⟶ F.obj Z} {g : ℕ → ∀ Z, H.obj Z ⟶ F.obj Z}
    {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
    (J : ∀ Z, SuperSumInvFrom (k := k) (f Z) (fun m => g m Z) p q n)
    (hf : IsSupernatural k p f) (hg : ∀ m, IsSupernatural k (q m) (g m))
    (hj : IsSupernatural k p (fun Z => (J Z).f'))
    (hk : ∀ m, IsSupernatural k (q m) (fun Z => (J Z).g' m)) :
    SuperSumInvFrom (k := k) (Superfunctor.homMk (F := G) (G := F) hf.toSuperNatTrans)
      (fun m => (Superfunctor.homMk (F := H) (G := F) (hg m).toSuperNatTrans)) p q n where
  f' := hj.toSuperNatTrans
  g' m := (hk m).toSuperNatTrans
  f_mem := Superfunctor.IsSupernatural.toSuperNatTrans_mem hf
  g_mem m := Superfunctor.IsSupernatural.toSuperNatTrans_mem (hg m)
  f'_mem := Superfunctor.IsSupernatural.toSuperNatTrans_mem hj
  g'_mem m := Superfunctor.IsSupernatural.toSuperNatTrans_mem (hk m)
  total := by
    apply Superfunctor.hom_ext
    intro s Z
    simp only [Superfunctor.add_app, transformation_sum_app, homogeneous_comp_app,
      zmod2_add_self]
    fin_cases s
    · simpa using (J Z).total
    · simp
  ff := by
    apply Superfunctor.hom_ext
    intro s Z
    simp only [homogeneous_comp_app, zmod2_add_self]
    fin_cases s
    · simpa using (J Z).ff
    · simp
  fg m hm := by
    apply Superfunctor.hom_ext
    intro s Z
    simp only [homogeneous_comp_app, (J Z).fg m hm, ite_self, Superfunctor.zero_app]
  gf m hm := by
    apply Superfunctor.hom_ext
    intro s Z
    simp only [homogeneous_comp_app, (J Z).gf m hm, ite_self, Superfunctor.zero_app]
  gg m l hm hl := by
    apply Superfunctor.hom_ext
    intro s Z
    rw [homogeneous_comp_app, (J Z).gg m l hm hl]
    by_cases e : m = l
    · subst l
      fin_cases s <;> simp [zmod2_add_self]
    · simp [e]

/-- The ordered mate has the parity of its crossing, since the adjunction is even. -/
theorem rouquierMate_homogeneous {B : Type*} [BicategoryStruct B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
    [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
    {a b c : B} {E : a ⟶ b} {F : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A : SuperAdjunction (k := k) E F) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    {p : ZMod 2} {t : E ≫ E₂ ⟶ E ≫ E₂} (ht : t ∈ parity (R := k) _ _ p) :
    rouquierMate A A₂ t ∈ parity (R := k) _ _ p := by
  have h₁ := inv_mem (rightUnitor (F ≫ E)) (TwoSupercategory.rightUnitor_hom_mem (R := k) (F ≫ E))
  have h₂ := TwoSupercategory.whiskerLeft_mem (F ≫ E) A₂.unit_mem
  have h₃ := TwoSupercategory.associator_hom_mem (R := k) F E (E₂ ≫ F₂)
  have h₄ := TwoSupercategory.whiskerLeft_mem F
    (inv_mem (associator E E₂ F₂) (TwoSupercategory.associator_hom_mem (R := k) E E₂ F₂))
  have h₅ := TwoSupercategory.whiskerLeft_mem F (TwoSupercategory.whiskerRight_mem F₂ ht)
  have h₆ := inv_mem (associator F (E ≫ E₂) F₂) (TwoSupercategory.associator_hom_mem (R := k) F (E ≫ E₂) F₂)
  have h₇ := TwoSupercategory.whiskerRight_mem F₂
    (inv_mem (associator F E E₂) (TwoSupercategory.associator_hom_mem (R := k) F E E₂))
  have h₈ := TwoSupercategory.whiskerRight_mem F₂ (TwoSupercategory.whiskerRight_mem E₂ A.counit_mem)
  have h₉ := TwoSupercategory.whiskerRight_mem F₂ (TwoSupercategory.leftUnitor_hom_mem (R := k) E₂)
  have hm := comp_mem h₁ (comp_mem h₂ (comp_mem h₃ (comp_mem h₄
    (comp_mem h₅ (comp_mem h₆ (comp_mem h₇ (comp_mem h₈ h₉)))))))
  simp only [zero_add, add_zero] at hm
  exact hm

end OddMath.SKM
