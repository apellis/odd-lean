/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # Coordinate maps of finite supermodule families

The inverse entries in Brundan–Ellis (1.13)–(1.14) are obtained by
projecting the inverse of the specified finite matrix and restoring
its canonical parity shifts. These are the even coordinate inclusions
and projections of that same finite product of supermodules.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.FiniteSupermodule
universe u v
variable {k : Type u} [CommRing k]
  {C : Type v} [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
  {ι : Type} (V : ι → Superfunctor k C (SVec k))

private def coordinate (a b : ι) : V a ⟶ V b := by
  classical
  exact if h : a = b then eqToHom (congrArg V h) else 0

private theorem coordinate_mem (a b : ι) :
    coordinate V a b ∈ parity (R := k) _ _ 0 := by
  classical
  unfold coordinate
  split_ifs with h
  · subst b
    exact id_mem (V a)
  · exact Submodule.zero_mem _

/-- The even projection to a coordinate of the given finite module product. -/
def projectionHom [Fintype ι] (a : ι) : product V ⟶ V a :=
  columnsHom (fun b => coordinate V b a) (fun b => coordinate_mem V b a)

/-- The even inclusion of a coordinate into the given module product. -/
def inclusionHom (a : ι) : V a ⟶ product V :=
  rowsHom (fun b => coordinate V a b) (fun b => coordinate_mem V a b)

theorem projectionHom_mem [Fintype ι] (a : ι) :
    projectionHom V a ∈ parity (R := k) _ _ 0 := by
  unfold projectionHom columnsHom
  exact Superfunctor.mem_parity_iff_isHomogeneous.mpr (SuperNatTrans.ofNatTrans_isHomogeneous _ _)

theorem inclusionHom_mem (a : ι) : inclusionHom V a ∈ parity (R := k) _ _ 0 := by
  unfold inclusionHom rowsHom
  exact Superfunctor.mem_parity_iff_isHomogeneous.mpr (SuperNatTrans.ofNatTrans_isHomogeneous _ _)

@[simp] theorem coordinate_total_self (a : ι) (t : C) (x : (V a).obj t) :
    (coordinate V a a).total t x = x := by
  simp only [coordinate, ↓reduceDIte, eqToHom_refl, SuperNatTrans.total,
    Superfunctor.id_app_zero, Superfunctor.id_app_one, add_zero]
  rfl

@[simp] theorem coordinate_total_ne (a b : ι) (hne : a ≠ b) (t : C) (x : (V a).obj t) :
    (coordinate V a b).total t x = 0 := by
  simp only [coordinate, dite_eq_right hne, SuperNatTrans.total, Superfunctor.zero_app, zero_add]
  rfl

/-- The total projection map evaluates to the original coordinate, on every vector. -/
@[simp] theorem projectionHom_total_apply [Fintype ι] (a : ι) (t : C) (x : (product V).obj t) :
    (projectionHom V a).total t x = x a := by
  classical
  rw [projectionHom, columnsHom_total_apply, Finset.sum_eq_single a]
  · exact coordinate_total_self V a t (x a)
  · intro b _ hba
    exact coordinate_total_ne V b a hba t (x b)
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

@[simp] theorem inclusionHom_total_self (a : ι) (t : C) (x : (V a).obj t) :
    (inclusionHom V a).total t x a = x := by
  rw [inclusionHom, rowsHom_total_apply]
  exact coordinate_total_self V a t x

@[simp] theorem inclusionHom_total_ne (a b : ι) (hne : a ≠ b) (t : C) (x : (V a).obj t) :
    (inclusionHom V a).total t x b = 0 := by
  rw [inclusionHom, rowsHom_total_apply]
  exact coordinate_total_ne V a b hne t x

private theorem sum_hom_apply {U W : SVec k} (s : Finset ι) (f : ι → (U ⟶ W)) (x : U) :
    (∑ a ∈ s, f a) x = ∑ a ∈ s, f a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, SVec.zero_apply]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, SVec.add_apply, ih]

private def totalLinear {M N : Superfunctor k C (SVec k)} (t : C) :
    (M ⟶ N) →ₗ[k] (M.obj t ⟶ N.obj t) where
  toFun f := f.total t
  map_add' f g := by
    simp only [SuperNatTrans.total, Superfunctor.add_app]
    abel
  map_smul' r f := by
    simp only [SuperNatTrans.total, Superfunctor.smul_app, RingHom.id_apply, smul_add]

theorem sum_total {M N : Superfunctor k C (SVec k)} (s : Finset ι)
    (f : ι → (M ⟶ N)) (t : C) :
    (∑ a ∈ s, f a).total t = ∑ a ∈ s, (f a).total t :=
  map_sum (totalLinear (k := k) t) f s

private theorem id_total_eq (M : Superfunctor k C (SVec k)) (t : C) :
    (𝟙 M : M ⟶ M).total t = 𝟙 (M.obj t) := SuperNatTrans.id_total M.toFunctor t

private theorem zero_total_eq (M N : Superfunctor k C (SVec k)) (t : C) :
    (0 : M ⟶ N).total t = 0 := by
  simp only [SuperNatTrans.total, Superfunctor.zero_app, zero_add]

/-- Coordinate inclusion followed by its projection is the identity module map. -/
@[simp] theorem inclusionHom_projectionHom [Fintype ι] (a : ι) :
    inclusionHom V a ≫ projectionHom V a = 𝟙 (V a) := by
  apply hom_ext_total
  intro t
  rw [Superfunctor.comp_total, id_total_eq]
  apply SVec.hom_ext
  intro x
  rw [SVec.comp_apply, projectionHom_total_apply, inclusionHom_total_self, SVec.id_apply]

/-- Distinct coordinates remain orthogonal as whole module maps. -/
theorem inclusionHom_projectionHom_ne [Fintype ι] (a b : ι) (hne : a ≠ b) :
    inclusionHom V a ≫ projectionHom V b = 0 := by
  apply hom_ext_total
  intro t
  rw [Superfunctor.comp_total, zero_total_eq]
  apply SVec.hom_ext
  intro x
  rw [SVec.comp_apply, projectionHom_total_apply, inclusionHom_total_ne V a b hne, SVec.zero_apply]

/-- The coordinate summands recover the entire finite product module. -/
theorem sum_projectionHom_inclusionHom [Fintype ι] :
    ∑ a, projectionHom V a ≫ inclusionHom V a = 𝟙 (product V) := by
  classical
  apply hom_ext_total
  intro t
  rw [sum_total, id_total_eq]
  apply SVec.hom_ext
  intro x
  simp only [sum_hom_apply, Superfunctor.comp_total, SVec.comp_apply, SVec.id_apply]
  funext b
  rw [Finset.sum_apply, Finset.sum_eq_single b]
  · rw [projectionHom_total_apply, inclusionHom_total_self]
  · intro a _ hab
    exact inclusionHom_total_ne V a b hab t _
  · intro hb
    exact (hb (Finset.mem_univ b)).elim

/-- The given column map is the sum of its exact coordinate projections and fields. -/
theorem columnsHom_eq_sum [Fintype ι] {T : Superfunctor k C (SVec k)}
    (f : ∀ a, V a ⟶ T) (hf : ∀ a, f a ∈ parity (R := k) _ _ 0) :
    columnsHom f hf = ∑ a, projectionHom V a ≫ f a := by
  apply hom_ext_total
  intro t
  rw [sum_total]
  apply SVec.hom_ext
  intro x
  simp only [sum_hom_apply, Superfunctor.comp_total, SVec.comp_apply,
    columnsHom_total_apply, projectionHom_total_apply]

/-- A given column is recovered by inserting its coordinate before the whole matrix. -/
@[simp] theorem inclusionHom_columnsHom [Fintype ι] {T : Superfunctor k C (SVec k)}
    (f : ∀ a, V a ⟶ T) (hf : ∀ a, f a ∈ parity (R := k) _ _ 0) (a : ι) :
    inclusionHom V a ≫ columnsHom f hf = f a := by
  rw [columnsHom_eq_sum, Preadditive.comp_sum]
  simp only [← Category.assoc]
  classical
  rw [Finset.sum_eq_single a]
  · rw [inclusionHom_projectionHom, Category.id_comp]
  · intro b _ hab
    rw [inclusionHom_projectionHom_ne V a b (Ne.symm hab), Limits.zero_comp]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

/-- A given row is recovered by projecting its coordinate after the whole matrix. -/
@[simp] theorem rowsHom_projectionHom {T : Superfunctor k C (SVec k)} [Fintype ι]
    (f : ∀ a, T ⟶ V a) (hf : ∀ a, f a ∈ parity (R := k) _ _ 0) (a : ι) :
    rowsHom f hf ≫ projectionHom V a = f a := by
  apply hom_ext_total
  intro t
  rw [Superfunctor.comp_total]
  apply SVec.hom_ext
  intro x
  rw [SVec.comp_apply, projectionHom_total_apply, rowsHom_total_apply]

end OddMath.FiniteSupermodule
