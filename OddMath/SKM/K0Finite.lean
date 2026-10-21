import StringDiagrams.Super.K0
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite decompositions in split K₀

Finite matrix decompositions used for the inversion relations in BE2 Lemma 11.6.
-/

noncomputable section
namespace OddMath.SKM.K0Relations
open CategoryTheory CategoryTheory.Limits StringDiagrams
open CategoryTheory.Preadditive

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C] [HasZeroObject C]

/-- Separate the first summand of a finite biproduct. -/
def finBiprodIso {n : ℕ} (Y : Fin (n + 1) → C) :
    (⨁ Y) ≅ Y 0 ⊞ ⨁ (fun i : Fin n => Y i.succ) where
  hom := biprod.lift (biproduct.π Y 0)
    (biproduct.lift fun i : Fin n => biproduct.π Y i.succ)
  inv := biprod.desc (biproduct.ι Y 0)
    (biproduct.desc fun i : Fin n => biproduct.ι Y i.succ)
  hom_inv_id := by
    rw [biprod.lift_desc, biproduct.lift_desc]
    simpa only [Fin.sum_univ_succ] using (biproduct.total (f := Y))
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext
    · simp
    · apply biproduct.hom_ext; intro j
      simp [Ne.symm (Fin.succ_ne_zero j)]
    · apply biproduct.hom_ext'; intro i; simp
    · apply biproduct.hom_ext'; intro i
      apply biproduct.hom_ext; intro j
      simp [biproduct.ι_π, Fin.succ_inj]

/-- The split class of a finite biproduct is the sum of its classes. -/
theorem mk_finBiproduct {n : ℕ} (Y : Fin n → C) :
    K₀.mk (⨁ Y) = ∑ i, K₀.mk (Y i) := by
  induction n with
  | zero =>
    have hz : IsZero (⨁ Y) := by
      rw [IsZero.iff_id_eq_zero, ← (biproduct.total (f := Y))]
      simp
    rw [K₀.mk_eq_mk_of_iso (hz.iso (isZero_zero C)), K₀.mk_zero]
    simp
  | succ n ih =>
    rw [K₀.mk_eq_mk_of_iso (finBiprodIso Y), K₀.mk_biprod, ih, Fin.sum_univ_succ]

/-- A finite inverse matrix gives the corresponding relation in split K₀. -/
theorem mk_of_matrix {n : ℕ} (A : C) (Y : Fin n → C)
    (p : ∀ i, A ⟶ Y i) (j : ∀ i, Y i ⟶ A)
    (diag : ∀ i, j i ≫ p i = 𝟙 _)
    (off : ∀ i l, i ≠ l → j i ≫ p l = 0)
    (total : ∑ i, p i ≫ j i = 𝟙 A) :
    K₀.mk A = ∑ i, K₀.mk (Y i) := by
  classical
  let e : A ≅ ⨁ Y :=
    { hom := biproduct.lift p
      inv := biproduct.desc j
      hom_inv_id := by simpa only [biproduct.lift_desc] using total
      inv_hom_id := by
        apply biproduct.hom_ext'; intro i
        apply biproduct.hom_ext; intro l
        simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc, Category.id_comp]
        by_cases h : i = l
        · subst l; simpa using diag i
        · rw [off i l h, biproduct.ι_π_ne _ h] }
  rw [K₀.mk_eq_mk_of_iso e, mk_finBiproduct]

/-- Apply a finite decomposition before additive idempotent completion. -/
theorem mk_of_mapped_matrix {B : Type*} [Category B] [Preadditive B]
    (F : B ⥤ C) [F.Additive] {n : ℕ} (A : B) (Y : Fin n → B)
    (p : ∀ i, A ⟶ Y i) (j : ∀ i, Y i ⟶ A)
    (diag : ∀ i, j i ≫ p i = 𝟙 _)
    (off : ∀ i l, i ≠ l → j i ≫ p l = 0)
    (total : ∑ i, p i ≫ j i = 𝟙 A) :
    K₀.mk (F.obj A) = ∑ i, K₀.mk (F.obj (Y i)) := by
  apply mk_of_matrix (F.obj A) (fun i => F.obj (Y i))
    (fun i => F.map (p i)) (fun i => F.map (j i))
  · intro i; rw [← F.map_comp, diag, F.map_id]
  · intro i l h; rw [← F.map_comp, off i l h, F.map_zero]
  · simp only [← F.map_comp, ← F.map_sum, total, F.map_id]

end OddMath.SKM.K0Relations
