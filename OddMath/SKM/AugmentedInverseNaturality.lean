/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.RouquierSupernaturalInverse

/-! # Signed naturality forced by augmented inverse identities

BE (1.13)–(1.14): the finite forward fields jointly detect maps, so their
signed naturality forces that of the finite inverse entries. Outside the
finite window an inverse row is unconstrained and must be zero-extended
before bundling a supernatural family.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.SKM
universe u v w
variable {k : Type w} [CommRing k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  {A B Z V : C} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}

/-- The specified forward columns jointly detect every outgoing map. -/
theorem SuperSumInvFrom.hom_ext {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
    (J : SuperSumInvFrom (k := k) f g p q n) {s t : A ⟶ V}
    (hf : f ≫ s = f ≫ t) (hg : ∀ m, m < n → g m ≫ s = g m ≫ t) : s = t := by
  have hs := congrArg (fun a : A ⟶ A => a ≫ s) J.total
  have ht := congrArg (fun a : A ⟶ A => a ≫ t) J.total
  simp only [Preadditive.add_comp, Preadditive.sum_comp, Category.assoc, Category.id_comp] at hs ht
  calc
    s = J.f' ≫ (f ≫ s) + ∑ m ∈ Finset.range n, J.g' m ≫ (g m ≫ s) := hs.symm
    _ = J.f' ≫ (f ≫ t) + ∑ m ∈ Finset.range n, J.g' m ≫ (g m ≫ t) := by
      rw [hf]
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      rw [hg m (Finset.mem_range.mp hm)]
    _ = t := ht

/-- The specified forward rows jointly detect every incoming map. -/
theorem SuperSumInvTo.hom_ext {f : A ⟶ B} {g : ℕ → (A ⟶ Z)}
    (J : SuperSumInvTo (k := k) f g p q n) {s t : V ⟶ A}
    (hf : s ≫ f = t ≫ f) (hg : ∀ m, m < n → s ≫ g m = t ≫ g m) : s = t := by
  have hs := congrArg (fun a : A ⟶ A => s ≫ a) J.total
  have ht := congrArg (fun a : A ⟶ A => t ≫ a) J.total
  simp only [Preadditive.comp_add, Preadditive.comp_sum, ← Category.assoc, Category.comp_id] at hs ht
  calc
    s = (s ≫ f) ≫ J.f' + ∑ m ∈ Finset.range n, (s ≫ g m) ≫ J.g' m := hs.symm
    _ = (t ≫ f) ≫ J.f' + ∑ m ∈ Finset.range n, (t ≫ g m) ≫ J.g' m := by
      rw [hf]
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      rw [hg m (Finset.mem_range.mp hm)]
    _ = t := ht

/-- Extend inverse rows by zero outside their prescribed finite window. -/
def SuperSumInvFrom.zeroExtend {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
    (J : SuperSumInvFrom (k := k) f g p q n) : SuperSumInvFrom (k := k) f g p q n where
  f' := J.f'
  g' m := if m < n then J.g' m else 0
  f_mem := J.f_mem
  g_mem := J.g_mem
  f'_mem := J.f'_mem
  g'_mem m := by
    split_ifs
    · exact J.g'_mem m
    · exact Submodule.zero_mem _
  total := by
    have hs : (∑ m ∈ Finset.range n, (if m < n then J.g' m else 0) ≫ g m) =
        ∑ m ∈ Finset.range n, J.g' m ≫ g m := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [ite_eq_left (Finset.mem_range.mp hm)]
    simpa only [hs] using J.total
  ff := J.ff
  fg m hm := by simpa only [ite_eq_left hm] using J.fg m hm
  gf := J.gf
  gg m l hm hl := by simpa only [ite_eq_left hl] using J.gg m l hm hl

/-- Extend inverse columns by zero outside their prescribed finite window. -/
def SuperSumInvTo.zeroExtend {f : A ⟶ B} {g : ℕ → (A ⟶ Z)}
    (J : SuperSumInvTo (k := k) f g p q n) : SuperSumInvTo (k := k) f g p q n where
  f' := J.f'
  g' m := if m < n then J.g' m else 0
  f_mem := J.f_mem
  g_mem := J.g_mem
  f'_mem := J.f'_mem
  g'_mem m := by
    split_ifs
    · exact J.g'_mem m
    · exact Submodule.zero_mem _
  total := by
    have hs : (∑ m ∈ Finset.range n, g m ≫ (if m < n then J.g' m else 0)) =
        ∑ m ∈ Finset.range n, g m ≫ J.g' m := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [ite_eq_left (Finset.mem_range.mp hm)]
    simpa only [hs] using J.total
  ff := J.ff
  fg := J.fg
  gf m hm := by simpa only [ite_eq_left hm] using J.gf m hm
  gg m l hm hl := by simpa only [ite_eq_left hm] using J.gg m l hm hl

section Columns
variable {A₀ B₀ Z₀ A₁ B₁ Z₁ : C}
  {f₀ : B₀ ⟶ A₀} {f₁ : B₁ ⟶ A₁} {g₀ : ℕ → (Z₀ ⟶ A₀)} {g₁ : ℕ → (Z₁ ⟶ A₁)}
  (J₀ : SuperSumInvFrom (k := k) f₀ g₀ p q n)
  (J₁ : SuperSumInvFrom (k := k) f₁ g₁ p q n)
  (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (z : Z₀ ⟶ Z₁) (r : ZMod 2)
  (hf : f₀ ≫ a = koszulSign p r • (b ≫ f₁))
  (hg : ∀ m, m < n → g₀ m ≫ a = koszulSign (q m) r • (z ≫ g₁ m))

include hf hg in
/-- Signed intertwining of forward columns determines that of their principal inverse. -/
theorem SuperSumInvFrom.principal_intertwine :
    a ≫ J₁.f' = koszulSign p r • (J₀.f' ≫ b) := by
  apply J₀.hom_ext
  · calc
      f₀ ≫ (a ≫ J₁.f') = koszulSign p r • (b ≫ (f₁ ≫ J₁.f')) := by
        rw [← Category.assoc, hf, Linear.smul_comp, Category.assoc]
      _ = koszulSign p r • b := by rw [J₁.ff, Category.comp_id]
      _ = f₀ ≫ (koszulSign p r • (J₀.f' ≫ b)) := by
        rw [Linear.comp_smul, ← Category.assoc, J₀.ff, Category.id_comp]
  · intro m hm
    rw [← Category.assoc, hg m hm, Linear.smul_comp, Category.assoc,
      J₁.gf m hm, Limits.comp_zero, smul_zero, Linear.comp_smul,
      ← Category.assoc, J₀.gf m hm, Limits.zero_comp, smul_zero]

include hf hg in
/-- Every inverse row in the prescribed finite window has forced signed intertwining. -/
theorem SuperSumInvFrom.row_intertwine (m : ℕ) (hm : m < n) :
    a ≫ J₁.g' m = koszulSign (q m) r • (J₀.g' m ≫ z) := by
  apply J₀.hom_ext
  · rw [← Category.assoc, hf, Linear.smul_comp, Category.assoc,
      J₁.fg m hm, Limits.comp_zero, smul_zero, Linear.comp_smul,
      ← Category.assoc, J₀.fg m hm, Limits.zero_comp, smul_zero]
  · intro l hl
    rw [← Category.assoc, hg l hl, Linear.smul_comp, Category.assoc, J₁.gg l m hl hm,
      Linear.comp_smul, ← Category.assoc, J₀.gg l m hl hm]
    by_cases hlm : l = m
    · subst l
      simp only [ite_true, Category.comp_id, Category.id_comp]
    · simp only [ite_eq_right hlm, Limits.comp_zero, Limits.zero_comp, smul_zero]

end Columns
section Rows
variable {A₀ B₀ Z₀ A₁ B₁ Z₁ : C}
  {f₀ : A₀ ⟶ B₀} {f₁ : A₁ ⟶ B₁} {g₀ : ℕ → (A₀ ⟶ Z₀)} {g₁ : ℕ → (A₁ ⟶ Z₁)}
  (J₀ : SuperSumInvTo (k := k) f₀ g₀ p q n)
  (J₁ : SuperSumInvTo (k := k) f₁ g₁ p q n)
  (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (z : Z₀ ⟶ Z₁) (r : ZMod 2)
  (hf : a ≫ f₁ = koszulSign p r • (f₀ ≫ b))
  (hg : ∀ m, m < n → a ≫ g₁ m = koszulSign (q m) r • (g₀ m ≫ z))

include hf hg in
/-- Signed intertwining of forward rows determines that of their principal inverse. -/
theorem SuperSumInvTo.principal_intertwine :
    b ≫ J₁.f' = koszulSign p r • (J₀.f' ≫ a) := by
  apply J₁.hom_ext
  · simp only [Category.assoc, J₁.ff, Category.comp_id, Linear.smul_comp, hf,
      Linear.comp_smul, koszulSign_smul_smul]
    rw [← Category.assoc, J₀.ff, Category.id_comp]
  · intro m hm
    simp only [Category.assoc, J₁.fg m hm, Limits.comp_zero, Linear.smul_comp, hg m hm,
      Linear.comp_smul]
    rw [← Category.assoc, J₀.fg m hm, Limits.zero_comp, smul_zero, smul_zero]

include hf hg in
/-- Every inverse column in the finite window has forced signed intertwining. -/
theorem SuperSumInvTo.column_intertwine (m : ℕ) (hm : m < n) :
    z ≫ J₁.g' m = koszulSign (q m) r • (J₀.g' m ≫ a) := by
  apply J₁.hom_ext
  · simp only [Category.assoc, J₁.gf m hm, Limits.comp_zero, Linear.smul_comp, hf,
      Linear.comp_smul]
    rw [← Category.assoc, J₀.gf m hm, Limits.zero_comp, smul_zero, smul_zero]
  · intro l hl
    simp only [Category.assoc, J₁.gg m l hm hl, Linear.smul_comp, hg l hl, Linear.comp_smul]
    rw [← Category.assoc, J₀.gg m l hm hl]
    by_cases hml : m = l
    · subst l
      simp only [ite_true, Category.comp_id, Category.id_comp, koszulSign_smul_smul]
    · simp only [ite_eq_right hml, Limits.comp_zero, Limits.zero_comp, smul_zero]

end Rows

section Families
variable {D : Type u} [Category.{v} D]
  [Preadditive D] [Linear k D] [Supercategory k D]
  {F G H : Superfunctor k D C}

private theorem natural_koszul
    {L V : Superfunctor k D C} {s : ZMod 2} {t : ∀ X, L.obj X ⟶ V.obj X}
    (ht : IsSupernatural k s t) {X Y : D} {r : ZMod 2} {h : X ⟶ Y}
    (hh : h ∈ parity (R := k) _ _ r) :
    L.map h ≫ t Y = koszulSign s r • (t X ≫ V.map h) := by
  simpa only [koszulSign_smul (R := k)] using ht.naturality hh

private theorem signed_reverse {W : Type*} [AddCommGroup W]
    (p r : ZMod 2) {x y : W} (h : x = koszulSign p r • y) :
    y = koszulSign p r • x := by
  have ht := congrArg (fun z => koszulSign p r • z) h
  simpa only [koszulSign_smul_smul] using ht.symm

/-- The given forward families force signed naturality of every principal inverse row. -/
theorem SuperSumInvFrom.principal_supernatural
    {f : ∀ X, G.obj X ⟶ F.obj X} {g : ℕ → ∀ X, H.obj X ⟶ F.obj X}
    (J : ∀ X, SuperSumInvFrom (k := k) (f X) (fun m => g m X) p q n)
    (hf : IsSupernatural k p f) (hg : ∀ m, IsSupernatural k (q m) (g m)) :
    IsSupernatural k p (F := F.toFunctor) (G := G.toFunctor) (fun X => (J X).f') where
  mem X := (J X).f'_mem
  naturality := by
    intro X Y r h hh
    have ht := SuperSumInvFrom.principal_intertwine (J X) (J Y) (F.map h) (G.map h) (H.map h) r
      (signed_reverse p r (natural_koszul hf hh))
      (fun m _ => signed_reverse (q m) r (natural_koszul (hg m) hh))
    simpa only [koszulSign_smul (R := k)] using ht

/-- Every finite inverse row is supernatural, with zero extension outside the window. -/
theorem SuperSumInvFrom.row_supernatural
    {f : ∀ X, G.obj X ⟶ F.obj X} {g : ℕ → ∀ X, H.obj X ⟶ F.obj X}
    (J : ∀ X, SuperSumInvFrom (k := k) (f X) (fun m => g m X) p q n)
    (hf : IsSupernatural k p f) (hg : ∀ m, IsSupernatural k (q m) (g m)) (m : ℕ) :
    IsSupernatural k (q m) (F := F.toFunctor) (G := H.toFunctor)
      (fun X => ((J X).zeroExtend).g' m) where
  mem X := ((J X).zeroExtend).g'_mem m
  naturality := by
    intro X Y r h hh
    by_cases hm : m < n
    · have ht := SuperSumInvFrom.row_intertwine (J X) (J Y) (F.map h) (G.map h) (H.map h) r
        (signed_reverse p r (natural_koszul hf hh))
        (fun l _ => signed_reverse (q l) r (natural_koszul (hg l) hh)) m hm
      simpa only [SuperSumInvFrom.zeroExtend, ite_eq_left hm, koszulSign_smul (R := k)] using ht
    · simp only [SuperSumInvFrom.zeroExtend, ite_eq_right hm,
        Limits.comp_zero, Limits.zero_comp, smul_zero]

/-- The forward families force signed naturality of every principal inverse column. -/
theorem SuperSumInvTo.principal_supernatural
    {f : ∀ X, F.obj X ⟶ G.obj X} {g : ℕ → ∀ X, F.obj X ⟶ H.obj X}
    (J : ∀ X, SuperSumInvTo (k := k) (f X) (fun m => g m X) p q n)
    (hf : IsSupernatural k p f) (hg : ∀ m, IsSupernatural k (q m) (g m)) :
    IsSupernatural k p (F := G.toFunctor) (G := F.toFunctor) (fun X => (J X).f') where
  mem X := (J X).f'_mem
  naturality := by
    intro X Y r h hh
    have ht := SuperSumInvTo.principal_intertwine (J X) (J Y) (F.map h) (G.map h) (H.map h) r
      (natural_koszul hf hh) (fun m _ => natural_koszul (hg m) hh)
    simpa only [koszulSign_smul (R := k)] using ht

/-- Every finite inverse column is supernatural, zero-extended outside the window. -/
theorem SuperSumInvTo.column_supernatural
    {f : ∀ X, F.obj X ⟶ G.obj X} {g : ℕ → ∀ X, F.obj X ⟶ H.obj X}
    (J : ∀ X, SuperSumInvTo (k := k) (f X) (fun m => g m X) p q n)
    (hf : IsSupernatural k p f) (hg : ∀ m, IsSupernatural k (q m) (g m)) (m : ℕ) :
    IsSupernatural k (q m) (F := H.toFunctor) (G := F.toFunctor)
      (fun X => ((J X).zeroExtend).g' m) where
  mem X := ((J X).zeroExtend).g'_mem m
  naturality := by
    intro X Y r h hh
    by_cases hm : m < n
    · have ht := SuperSumInvTo.column_intertwine (J X) (J Y) (F.map h) (G.map h) (H.map h) r
        (natural_koszul hf hh) (fun l _ => natural_koszul (hg l) hh) m hm
      simpa only [SuperSumInvTo.zeroExtend, ite_eq_left hm, koszulSign_smul (R := k)] using ht
    · simp only [SuperSumInvTo.zeroExtend, ite_eq_right hm,
        Limits.comp_zero, Limits.zero_comp, smul_zero]

/-- Pointwise augmented column inverses bundle without an inverse-naturality premise. -/
def SuperSumInvFrom.ofSupernaturalComponents
    {f : ∀ X, G.obj X ⟶ F.obj X} {g : ℕ → ∀ X, H.obj X ⟶ F.obj X}
    (J : ∀ X, SuperSumInvFrom (k := k) (f X) (fun m => g m X) p q n)
    (hf : IsSupernatural k p f) (hg : ∀ m, IsSupernatural k (q m) (g m)) :
    SuperSumInvFrom (k := k) (Superfunctor.homMk (F := G) (G := F) hf.toSuperNatTrans)
      (fun m => Superfunctor.homMk (F := H) (G := F) (hg m).toSuperNatTrans) p q n :=
  SuperSumInvFrom.supernatural (fun X => (J X).zeroExtend) hf hg
    (SuperSumInvFrom.principal_supernatural J hf hg)
    (SuperSumInvFrom.row_supernatural J hf hg)

/-- Pointwise augmented row inverses bundle without an inverse-naturality premise. -/
def SuperSumInvTo.ofSupernaturalComponents
    {f : ∀ X, F.obj X ⟶ G.obj X} {g : ℕ → ∀ X, F.obj X ⟶ H.obj X}
    (J : ∀ X, SuperSumInvTo (k := k) (f X) (fun m => g m X) p q n)
    (hf : IsSupernatural k p f) (hg : ∀ m, IsSupernatural k (q m) (g m)) :
    SuperSumInvTo (k := k) (Superfunctor.homMk (F := F) (G := G) hf.toSuperNatTrans)
      (fun m => Superfunctor.homMk (F := F) (G := H) (hg m).toSuperNatTrans) p q n :=
  SuperSumInvTo.supernatural (fun X => (J X).zeroExtend) hf hg
    (SuperSumInvTo.principal_supernatural J hf hg)
    (SuperSumInvTo.column_supernatural J hf hg)

end Families

end OddMath.SKM
