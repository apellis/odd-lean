/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.Algebra.FiniteSupermoduleCoordinates

/-! # Homogeneous inverse columns of a specified finite module matrix

Brundan–Ellis (1.13)–(1.14): include each literal parity coordinate
before the inverse of the prescribed even row matrix. The given forward
fields retain all their inverse identities and original parities.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.FiniteSupermodule
universe u v
variable {k : Type u} [CommRing k]
  {C : Type v} [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
  {ι : Type}
  {V T : ι → Superfunctor k C (SVec k)} {A : Superfunctor k C (SVec k)}
  (r : ∀ a, V a ≅ T a) (p : ι → ZMod 2)
  (hr : ∀ a, (r a).hom ∈ parity (R := k) _ _ (p a))
  (f : ∀ a, A ⟶ T a) (hf : ∀ a, f a ∈ parity (R := k) _ _ (p a))

def restoredRow (a : ι) : A ⟶ V a := f a ≫ (r a).inv

include p hr hf in
theorem restoredRow_mem (a : ι) : restoredRow r f a ∈ parity (R := k) _ _ 0 := by
  simpa only [restoredRow, zmod2_add_self] using comp_mem (hf a) (inv_mem (r a) (hr a))

/-- The specified row matrix in its canonical even target coordinates. -/
def restoredRows : A ⟶ product V :=
  rowsHom (restoredRow r f) (restoredRow_mem r p hr f hf)

theorem restoredRows_mem : restoredRows r p hr f hf ∈ parity (R := k) _ _ 0 := by
  unfold restoredRows rowsHom
  exact Superfunctor.mem_parity_iff_isHomogeneous.mpr (SuperNatTrans.ofNatTrans_isHomogeneous _ _)

/-- The inverse column restores its given source parity and inserts its coordinate. -/
def inverseCoordinateColumn (e : A ≅ product V) (a : ι) : T a ⟶ A :=
  (r a).inv ≫ inclusionHom V a ≫ e.inv

variable (e : A ≅ product V) (he : e.hom = restoredRows r p hr f hf)

include he in
theorem inverseCoordinateColumn_mem (a : ι) :
    inverseCoordinateColumn r e a ∈ parity (R := k) _ _ (p a) := by
  have h0 : e.hom ∈ parity (R := k) _ _ 0 := by
    rw [he]
    exact restoredRows_mem r p hr f hf
  simpa only [inverseCoordinateColumn, add_zero] using
    comp_mem (inv_mem (r a) (hr a)) (comp_mem (inclusionHom_mem V a) (inv_mem e h0))

variable [Fintype ι]

include he in
private theorem rowCoordinate_factor (a : ι) :
    f a = (e.hom ≫ projectionHom V a) ≫ (r a).hom := by
  rw [he, restoredRows, rowsHom_projectionHom]
  simp only [restoredRow, Category.assoc, Iso.inv_hom_id, Category.comp_id]

include he in
/-- The extracted inverse column followed by its forward row is the identity. -/
theorem inverseCoordinateColumn_forward (a : ι) :
    inverseCoordinateColumn r e a ≫ f a = 𝟙 (T a) := by
  rw [rowCoordinate_factor r p hr f hf e he a, inverseCoordinateColumn]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (inclusionHom V a) (projectionHom V a), inclusionHom_projectionHom]
  simp only [Category.id_comp, Iso.inv_hom_id]

include he in
/-- The other inverse columns and forward rows remain orthogonal. -/
theorem inverseCoordinateColumn_forward_ne (a b : ι) (hne : a ≠ b) :
    inverseCoordinateColumn r e a ≫ f b = 0 := by
  rw [rowCoordinate_factor r p hr f hf e he b, inverseCoordinateColumn]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (inclusionHom V a) (projectionHom V b), inclusionHom_projectionHom_ne V a b hne]
  simp only [Limits.zero_comp, Limits.comp_zero]

include he in
/-- The prescribed forward rows and extracted inverse columns recover the entire source. -/
theorem sum_forward_inverseCoordinateColumn :
    ∑ a, f a ≫ inverseCoordinateColumn r e a = 𝟙 A := by
  have hterm (a : ι) : f a ≫ inverseCoordinateColumn r e a =
      e.hom ≫ (projectionHom V a ≫ inclusionHom V a) ≫ e.inv := by
    rw [inverseCoordinateColumn, rowCoordinate_factor r p hr f hf e he a]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  calc
    _ = ∑ a, e.hom ≫ (projectionHom V a ≫ inclusionHom V a) ≫ e.inv :=
      Finset.sum_congr rfl (fun a _ => hterm a)
    _ = e.hom ≫ (∑ a, projectionHom V a ≫ inclusionHom V a) ≫ e.inv := by
      rw [Preadditive.sum_comp, Preadditive.comp_sum]
    _ = 𝟙 A := by
      simp only [sum_projectionHom_inclusionHom, Category.id_comp, Iso.hom_inv_id]

end OddMath.FiniteSupermodule
